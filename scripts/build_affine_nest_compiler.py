"""Extract and build the checked deeper-affine whole-program prototype."""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess

import build_compiler
import polcert_core

ROOT = Path(__file__).resolve().parents[1]
UPSTREAM = ROOT / "vendor" / "CompCert"
ADAPTER = ROOT / "adapters" / "compcert-memory"
DIRECTORY = ROOT / "prototype" / "affine-nest"
WORK = ROOT / "build" / "compcert-affine-nest"
ENTRY = "AffineNestWholeCompiler.compile_affine_regions"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(*arguments):
    subprocess.run(arguments, cwd=WORK, check=True)


def main():
    global WORK, ENTRY
    parser = argparse.ArgumentParser()
    parser.add_argument("--unified", action="store_true")
    args = parser.parse_args()
    if args.unified:
        WORK = ROOT / "build" / "compcert-guardcert"
        ENTRY = "AffineNestUnifiedCompiler.compile_guardcert"
    polcert_core.select_profile("optimizer")
    proof_path = ROOT / "build" / "affine-nest-foundation-prototype-report.json"
    proof = json.loads(proof_path.read_text())
    baseline = json.loads((ROOT / "build" / "guard-memory-proof-report.json").read_text())
    sources = {**baseline["sources"], **proof["sources"]}
    proof_entry = "unified_whole_program_entrypoint" if args.unified else "whole_program_entrypoint"
    if (proof["status"] != "compiled" or proof.get(proof_entry) != ENTRY
            or proof["new_global_axioms"] or not proof["same_as_current_whole_program_assumptions"]
            or any(sha(ROOT / filename) != digest for filename, digest in sources.items())):
        raise SystemExit("recompile and audit the current affine-nest prototype before extraction")
    shutil.copytree(UPSTREAM, WORK, dirs_exist_ok=True, copy_function=build_compiler.copy_source,
        ignore=shutil.ignore_patterns("*.vo", "*.vos", "*.vok", "*.glob", ".*.aux",
            "*.cmi", "*.cmx", "*.cmo", "*.o", "*.a", ".depend*", "STAMP"))
    for pattern in ("*.ml", "*.mli", "*.cmi", "*.cmx", "*.o"):
        for path in (WORK / "extraction").glob(pattern):
            path.unlink()
    original = (UPSTREAM / "driver" / "Driver.ml").read_text()
    needle = "(Compiler.transf_c_program csyntax)"
    if original.count(needle) != 1:
        raise SystemExit("unexpected CompCert driver entry")
    invocation = (ENTRY + " GuardAffineNestCandidate.describe GuardAffineNestCandidate.propose "
        + ("GuardMemoryUnifiedCandidate.propose " if args.unified else "")
        + "(GuardMemoryCandidate.natural 32) csyntax")
    replacement = """(let outcome = ref None in
      ImpureConfig.Core.Base.bind (INVOCATION)
        (fun (result, alarm_free) -> outcome := Some (result, alarm_free); ());
      match !outcome with
      | Some (result, true) -> result
      | _ -> invalid_arg "GuardCert affine dependence checker raised an alarm")""".replace("INVOCATION", invocation)
    (WORK / "driver" / "Driver.ml").write_text(original.replace(needle, replacement))
    extraction_text = (UPSTREAM / "extraction" / "extraction.v").read_text()
    if extraction_text.count("Separate Extraction\n") != 1:
        raise SystemExit("unexpected CompCert extraction roots")
    mappings = r'''
Extract Inlined Constant CoqAddOn.posPr => "(fun value -> Z.to_string (GuardMemoryNumbers.export_positive value))".
Extract Inlined Constant CoqAddOn.posPrRaw => "(fun value -> Z.to_string (GuardMemoryNumbers.export_positive value))".
Extract Inlined Constant CoqAddOn.zPr => "(fun value -> Z.to_string (GuardMemoryNumbers.export_integer value))".
Extract Inlined Constant CoqAddOn.zPrRaw => "(fun value -> Z.to_string (GuardMemoryNumbers.export_integer value))".
Extract Inlined Constant Debugging.failwith => "(fun _ _ default -> default)".
Extract Constant PedraQBackend.t => "unit".
Extract Constant PedraQBackend.top => "()".
Extract Constant PedraQBackend.pr => "(fun _ -> String.empty)".
Extract Constant PedraQBackend.isEmpty => "GuardMemoryOracle.is_empty".
Extract Constant PedraQBackend.add => "GuardMemoryOracle.add".
Extraction Inline Core.Base.pure Core.Base.imp CoreAlarmed.Base.pure CoreAlarmed.Base.imp.
'''
    extraction = WORK / "extract_affine.v"
    extraction.write_text("From GuardAffineNest Require Import AffineNestWholeCompiler AffineNestPropose AffineNestRangeProposal.\n"
        + ("From GuardAffineNest Require Import AffineNestUnifiedCompiler.\n" if args.unified else "")
        + "From GuardMemory Require Import GuardMemoryScalarTiling.\n"
        "From polcert.lib Require Import ImpureAlarmConfig TopoSort.\n"
        "From Vpl Require Import CoqAddOn Debugging PedraQBackend CstrC LinTerm.\n"
        + extraction_text.replace("Separate Extraction\n", mappings + "\nSeparate Extraction " + ENTRY
            + " AffineNestPropose.affine_default_source_proposal AffineNestRangeProposal.affine_source_range_proposal GuardMemoryScalarTiling.memory_scalar_tiling_witness LinTerm.LinQ.export CstrC.Cstr.isContrad\n"))
    flags = [*polcert_core.load_flags(), "-Q", str(ADAPTER), "GuardMemory", "-Q", str(DIRECTORY), "GuardAffineNest"]
    for name in ("cparser", "export", "MenhirLib"):
        flags += ["-R", str(UPSTREAM / name), "MenhirLib" if name == "MenhirLib" else "compcert." + name]
    run("rocq", "compile", *flags, str(extraction))
    inferred = [module for module in ("ImpureConfig", "TilingValidator", "GuardMemoryPolyhedral", "GuardMemoryTilingProgress")
        if (WORK / "extraction" / (module + ".ml")).exists()]
    for module in inferred:
        (WORK / "extraction" / (module + ".mli")).unlink(missing_ok=True)
    for path in (WORK / "extraction").glob("*.ml"):
        if "AXIOM TO BE REALIZED" in path.read_text():
            raise SystemExit("unrealized extraction axiom: " + path.name)
    native_sources = [ADAPTER / "native" / name for name in
        ("GuardMemoryNumbersCompCert.ml", "GuardMemoryOracle.ml", "GuardMemoryCandidate.ml")]
    native_sources.append(DIRECTORY / "native" / "GuardAffineNestCandidate.ml")
    native_sources.append(DIRECTORY / "native" / "GuardAffineNestTiling.ml")
    if args.unified:
        native_sources += [ADAPTER / "native" / name for name in
                           ("GuardMemoryScheduleInput.ml", "GuardMemoryUnifiedCandidate.ml")]
    for path in native_sources:
        name = "GuardMemoryNumbers.ml" if path.name == "GuardMemoryNumbersCompCert.ml" else path.name
        shutil.copy2(path, WORK / "extraction" / name)
    makefile = WORK / "Makefile.extr"
    zarith = subprocess.check_output(["ocamlfind", "query", "zarith"], text=True).strip()
    makefile.write_text(makefile.read_text() + f'\nCOMPFLAGS += -I "{zarith}"\nLIBS += zarith.cmxa\n'
        + "".join(f"extraction/{module}.cmi: extraction/{module}.cmx\n" for module in inferred))
    run("make", "tools/modorder", "driver/Version.ml", "compcert.ini")
    run("make", "-f", "Makefile.extr", "depend")
    run("make", "-j4", "-f", "Makefile.extr", "ccomp")
    (WORK / ".guard-build.json").write_text(json.dumps({
        "proved_entrypoint": ENTRY, "compiler_sha256": sha(WORK / "ccomp"),
        "proof_sources": sources, "prototype_proof_report_sha256": sha(proof_path),
        "extraction_sha256": sha(extraction),
        "native_sources": {str(path.relative_to(ROOT)): sha(path) for path in native_sources},
        "oracle": "bounded Fourier-Motzkin with checked LCF certificates",
        "candidate_configuration": "GUARDCERT_AFFINE_MODE; untrusted source and candidate policies",
    }, indent=2) + "\n")
    print("checked affine compiler: " + str(WORK / "ccomp"))


if __name__ == "__main__":
    main()
