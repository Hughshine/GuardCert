"""Extract the proved driver and build it in a disposable CompCert copy."""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import stat
import subprocess

ROOT = Path(__file__).resolve().parents[1]
UPSTREAM = ROOT / "vendor" / "CompCert"
WORK = ROOT / "build" / "compcert-guard"


def run(*args):
    subprocess.run(args, cwd=WORK, check=True)


def copy_source(source, destination):
    # Upstream generated .v files are read-only; only the build copy is changed.
    target = Path(destination)
    if target.is_file():
        target.chmod(target.stat().st_mode | stat.S_IWUSR)
    return shutil.copy2(source, destination)


def main():
    global WORK
    parser = argparse.ArgumentParser(description=__doc__)
    variant = parser.add_mutually_exclusive_group()
    variant.add_argument("--store-swap", action="store_true",
                        help="build the optional compiler proved with actual CInstr store commutation")
    variant.add_argument("--matrix-schedule", action="store_true",
                         help="build the compiler accepting untrusted GUARDCERT_POINT_ORDER proposals")
    variant.add_argument("--rectangular-loop", action="store_true",
                         help="build the compiler for guarded dynamic rectangle interchange")
    args = parser.parse_args()
    if args.rectangular_loop:
        entrypoint, import_name = "RectangularCompiler.compile_rectangular_regions", "RectangularCompiler"
        WORK = ROOT / "build" / "compcert-rectangular"
        report = json.loads((ROOT / "build" / "rectangular-proof-report.json").read_text())
        if (report["status"] != "compiled" or report["additional_global_axioms"]
                or report["whole_program_theorem"] != entrypoint + "_correct"
                or any(hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != expected
                       for path, expected in report["sources"].items())):
            raise SystemExit("rebuild and audit the rectangular proof before extraction")
    elif args.matrix_schedule:
        entrypoint, import_name = "ScheduledRegionCompiler.compile_scheduled_regions", "ScheduledRegionCompiler"
        WORK = ROOT / "build" / "compcert-scheduled"
        report = json.loads((ROOT / "build" / "scheduled-matrix-proof-report.json").read_text())
        if (report["status"] != "compiled" or report["additional_global_axioms"]
                or report["whole_program_theorem"] != "ScheduledRegionCompiler.compile_scheduled_regions_correct"
                or any(hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != expected
                       for path, expected in report["sources"].items())):
            raise SystemExit("rebuild and audit the finite scheduling proof before extraction")
    else:
        entrypoint = "PolCertStoreNative.compile" if args.store_swap else "AdaptiveRegionCompiler.compile_progress_regions"
        import_name = "PolCertStoreNative" if args.store_swap else "AdaptiveRegionCompiler"
    if args.store_swap:
        WORK = ROOT / "build" / "compcert-store-swap"
        from polcert_core import select_profile, load_flags, artifact
        select_profile("memory")
        report = json.loads(artifact("store-swap-report.json").read_text())
        if report["status"] != "compiled" or any(
            hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != expected
            for path, expected in report["sources"].items()
        ):
            raise SystemExit("rebuild and audit the concrete store-swap proof before extraction")
        dynamic_report = json.loads(artifact("dynamic-store-report.json").read_text())
        if dynamic_report["status"] != "compiled" or any(
            hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != expected
            for path, expected in dynamic_report["sources"].items()
        ):
            raise SystemExit("rebuild and audit the dynamic store proof before extraction")
        package_report = json.loads(artifact("store-package-report.json").read_text())
        if package_report["status"] != "compiled" or any(
            hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != expected
            for path, expected in package_report["sources"].items()
        ):
            raise SystemExit("rebuild and audit the concrete schedule package before extraction")
        native_report = json.loads((ROOT / "build" / "store-swap-compiler-assumptions-report.json").read_text())
        if (native_report["adapted_theorem"] != "PolCertStoreNative.compile_correct"
                or native_report["additional_global_axioms"]
                or native_report["theorem_source_sha256"] != hashlib.sha256(
                    (ROOT / "theories" / "PolCertStoreNative.v").read_bytes()).hexdigest()):
            raise SystemExit("audit the current native store-swap entrypoint before extraction")
    inputs = [Path(__file__).resolve(), ROOT / "toolchain.lock.json",
              UPSTREAM / "Makefile.config", UPSTREAM / "driver" / "Driver.ml",
              UPSTREAM / "extraction" / "extraction.v"]
    inputs += sorted((ROOT / "theories").glob("*.v"))
    digest = hashlib.sha256()
    digest.update(entrypoint.encode() + b"\0")
    for source in inputs:
        digest.update(str(source.relative_to(ROOT)).encode() + b"\0")
        digest.update(source.read_bytes() + b"\0")
    key = digest.hexdigest()
    stamp = WORK / ".guard-build.json"
    executable = WORK / "ccomp"
    if stamp.exists() and executable.exists():
        cached = json.loads(stamp.read_text())
        if cached["input_sha256"] == key and cached["compiler_sha256"] == hashlib.sha256(executable.read_bytes()).hexdigest():
            print(f"guarded compiler (cached): {executable}")
            return
    shutil.copytree(
        UPSTREAM, WORK, dirs_exist_ok=True, copy_function=copy_source,
        ignore=shutil.ignore_patterns(
            "*.vo", "*.vos", "*.vok", "*.glob", ".*.aux", ".lia.cache",
            "*.cmi", "*.cmx", "*.cmo", "*.o", "*.a", ".depend*", "STAMP",
        ),
    )
    original = (UPSTREAM / "driver" / "Driver.ml").read_text()
    needle = "(Compiler.transf_c_program csyntax)"
    if original.count(needle) != 1:
        raise SystemExit("unexpected upstream driver: compiler call is not unique")
    replacement = (f'({entrypoint} (Camlcoq.intern_string "a") (Camlcoq.intern_string "i") '
                   f'(Camlcoq.intern_string "j") csyntax)' if args.store_swap
                   else f"({entrypoint} csyntax)")
    if args.matrix_schedule:
        replacement = """(let raw_order = match Sys.getenv_opt "GUARDCERT_POINT_ORDER" with
            | None -> "0,2,1,3" | Some value -> String.trim value in
          let tokens = if raw_order = "" then [] else String.split_on_char ',' raw_order in
          if List.length tokens > 64 then invalid_arg "too many GuardCert point identifiers";
          let rec natural n = if n = 0 then Datatypes.O else Datatypes.S (natural (n - 1)) in
          let point token =
            let n = int_of_string (String.trim token) in
            if n < 0 || n > 1024 then invalid_arg "GuardCert point identifier outside parser range";
            natural n in
          ScheduledRegionCompiler.compile_scheduled_regions (List.map point tokens) csyntax)"""
    patched = original.replace(needle, replacement)
    driver = WORK / "driver" / "Driver.ml"
    if driver.read_text() != patched:
        driver.write_text(patched)
    extraction = WORK / "extract_guard.v"
    upstream_extraction = (UPSTREAM / "extraction" / "extraction.v").read_text()
    if upstream_extraction.count("Separate Extraction\n") != 1:
        raise SystemExit("unexpected upstream extraction roots")
    extraction.write_text(
        f"From Guard Require Import {import_name}.\n"
        + upstream_extraction.replace(
            "Separate Extraction\n", f"Separate Extraction {entrypoint}\n"
        )
    )
    flags = ["-Q", str(ROOT / "theories"), "Guard"]
    for name in ("lib", "common", "x86", "x86_64", "backend", "cfrontend", "driver", "cparser", "export"):
        flags += ["-R", str(UPSTREAM / name), "compcert." + name]
    flags += ["-R", str(UPSTREAM / "flocq"), "Flocq", "-R", str(UPSTREAM / "MenhirLib"), "MenhirLib"]
    if args.store_swap:
        flags = [*load_flags(), "-Q", str(artifact("adapters")), "GuardPolCert",
                 "-R", str(UPSTREAM / "cparser"), "compcert.cparser",
                 "-R", str(UPSTREAM / "export"), "compcert.export",
                 "-R", str(UPSTREAM / "MenhirLib"), "MenhirLib"]
    run("rocq", "compile", *flags, str(extraction))
    for source in (WORK / "extraction").glob("*.ml"):
        if "AXIOM TO BE REALIZED" in source.read_text():
            raise SystemExit(f"unrealized extraction axiom: {source.name}")
    run("make", "tools/modorder", "driver/Version.ml", "compcert.ini")
    run("make", "-f", "Makefile.extr", "depend")
    run("make", "-j4", "-f", "Makefile.extr", "ccomp")
    stamp.write_text(json.dumps({
        "input_sha256": key,
        "compiler_sha256": hashlib.sha256(executable.read_bytes()).hexdigest(),
        "proved_entrypoint": entrypoint,
        "array_identifier_input": "frontend identifier for a" if args.store_swap else None,
        "index_identifier_inputs": ["frontend identifier for i", "frontend identifier for j"] if args.store_swap else [],
        "schedule_package_proposer": "PolCertStorePackage.propose_dynamic_package" if args.store_swap else None,
        "schedule_proposal_input": "GUARDCERT_POINT_ORDER" if args.matrix_schedule else None,
    }, indent=2) + "\n")
    print(f"guarded compiler: {WORK / 'ccomp'}")


if __name__ == "__main__":
    main()
