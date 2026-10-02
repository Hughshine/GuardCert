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
    parser.add_argument("--store-swap", action="store_true",
                        help="build the optional compiler proved with actual CInstr store commutation")
    args = parser.parse_args()
    entrypoint = "PolCertStoreNative.compile" if args.store_swap else "RegionCompiler.compile_property_regions"
    import_name = "PolCertStoreNative" if args.store_swap else "RegionCompiler"
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
    replacement = (f'({entrypoint} (Camlcoq.intern_string "a") csyntax)' if args.store_swap
                   else f"({entrypoint} csyntax)")
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
    }, indent=2) + "\n")
    print(f"guarded compiler: {WORK / 'ccomp'}")


if __name__ == "__main__":
    main()
