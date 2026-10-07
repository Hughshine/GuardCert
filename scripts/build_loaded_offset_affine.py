"""Extract the guarded compiler for actual loaded-plus-offset root headers."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

import build_compiler
import polcert_core

ROOT = Path(__file__).resolve().parents[1]
UPSTREAM = ROOT / "vendor/CompCert"
ADAPTER = ROOT / "adapters/compcert-memory"
WORK = ROOT / "build/loaded-offset-affine/compiler"
PROOF = ROOT / "build/loaded-offset-affine/proof/report.json"
ENTRY = "ClightGuardedLoadedOffsetAffineMultiCompiler.compile_offset_affine_multi_regions"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(*arguments):
    subprocess.run(arguments, cwd=WORK, check=True)


def main():
    polcert_core.select_profile("optimizer")
    proof = json.loads(PROOF.read_text())
    assert proof["status"] == "compiled" and proof["whole_program_entrypoint"] == ENTRY
    assert proof["additional_global_axioms"] == []
    for path, digest in proof["sources"].items():
        assert sha(ROOT / path) == digest, path
    for path, digest in proof["compiled_objects"].items():
        assert sha((ROOT / path).with_suffix(".vo")) == digest, path
    shutil.copytree(UPSTREAM, WORK, dirs_exist_ok=True, copy_function=build_compiler.copy_source,
                   ignore=shutil.ignore_patterns("*.vo", "*.vos", "*.vok", "*.glob", ".*.aux",
                       "*.cmi", "*.cmx", "*.cmo", "*.o", "*.a", ".depend*", "STAMP"))
    for pattern in ("*.ml", "*.mli", "*.cmi", "*.cmx", "*.o"):
        for path in (WORK / "extraction").glob(pattern):
            path.unlink()
    original = (UPSTREAM / "driver/Driver.ml").read_text()
    needle = "(Compiler.transf_c_program csyntax)"
    assert original.count(needle) == 1
    invocation = "(" + ENTRY + " GuardLoadedOffsetAffineCandidate.describe GuardLoadedOffsetAffineCandidate.propose (GuardMemoryCandidate.natural 32) csyntax)"
    replacement = """(let outcome = ref None in
      ImpureConfig.Core.Base.bind INVOCATION
        (fun (result, alarm_free) -> outcome := Some (result, alarm_free); ());
      match !outcome with
      | Some (result, true) -> result
      | _ -> invalid_arg "GuardCert dependence checker raised an alarm")""".replace("INVOCATION", invocation)
    (WORK / "driver/Driver.ml").write_text(original.replace(needle, replacement))
    extraction_text = (UPSTREAM / "extraction/extraction.v").read_text()
    assert extraction_text.count("Separate Extraction\n") == 1
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
    extraction = WORK / "extract_loaded_offset_affine.v"
    roots = ENTRY + " ClightFrontendLoopProtocol.frontend_counted_loop AffineNestPropose.affine_default_source_proposal AffineNestRangeProposal.affine_source_range_proposal AffineNestMultiProposal.affine_reserve_multi_scans GuardMemoryScalarTiling.memory_scalar_tiling_witness LinTerm.LinQ.export CstrC.Cstr.isContrad"
    extraction.write_text("From GuardInterface Require Import " + ENTRY.split(".")[0] + ".\n"
        "From Guard Require Import ClightFrontendLoopProtocol.\n"
        "From GuardAffineNest Require Import AffineNestPropose AffineNestRangeProposal AffineNestMultiProposal.\n"
        "From GuardMemory Require Import GuardMemoryScalarTiling.\n"
        "From polcert.lib Require Import ImpureAlarmConfig TopoSort.\n"
        "From Vpl Require Import CoqAddOn Debugging PedraQBackend CstrC LinTerm.\n"
        + extraction_text.replace("Separate Extraction\n", mappings + "\nSeparate Extraction " + roots + "\n"))
    flags = [*polcert_core.load_flags(), "-Q", str(ADAPTER), "GuardMemory",
             "-Q", str(ROOT / "prototype/interface"), "GuardInterface",
             "-Q", str(ROOT / "prototype/affine-nest"), "GuardAffineNest"]
    for name in ("cparser", "export", "MenhirLib"):
        flags += ["-R", str(UPSTREAM / name), "MenhirLib" if name == "MenhirLib" else "compcert." + name]
    run("rocq", "compile", *flags, str(extraction))
    inferred = ["ImpureConfig", "TilingValidator", "GuardMemoryPolyhedral", "GuardMemoryTilingProgress"]
    for module in inferred:
        (WORK / "extraction" / (module + ".mli")).unlink(missing_ok=True)
    for source in (WORK / "extraction").glob("*.ml"):
        assert "AXIOM TO BE REALIZED" not in source.read_text(), source.name
    sources = [ADAPTER / "native" / name for name in
               ["GuardMemoryNumbersCompCert.ml", "GuardMemoryOracle.ml", "GuardMemoryCandidate.ml"]]
    sources += [ROOT / "prototype/affine-nest/native" / name for name in
                ["GuardAffineNestCandidate.ml", "GuardAffineNestTiling.ml", "GuardAffineNestExternal.ml", "GuardLoadedAffineCandidate.ml", "GuardLoadedOffsetAffineCandidate.ml"]]
    for source in sources:
        name = "GuardMemoryNumbers.ml" if source.name == "GuardMemoryNumbersCompCert.ml" else source.name
        shutil.copy2(source, WORK / "extraction" / name)
    zarith = subprocess.check_output(["ocamlfind", "query", "zarith"], text=True).strip()
    makefile = WORK / "Makefile.extr"
    makefile.write_text(makefile.read_text() + f'\nCOMPFLAGS += -I "{zarith}"\nLIBS += zarith.cmxa\n'
        + "".join(f"extraction/{module}.cmi: extraction/{module}.cmx\n" for module in inferred))
    run("make", "tools/modorder", "driver/Version.ml", "compcert.ini")
    run("make", "-f", "Makefile.extr", "depend")
    run("make", "-j4", "-f", "Makefile.extr", "ccomp")
    (WORK / ".guard-build.json").write_text(json.dumps({
        "proved_entrypoint": ENTRY, "compiler_sha256": sha(WORK / "ccomp"),
        "build_script_sha256": sha(Path(__file__)), "driver_sha256": sha(WORK / "driver/Driver.ml"),
        "proof_sources": proof["sources"], "extraction_sha256": sha(extraction),
        "proof_report_sha256": sha(PROOF),
        "native_sources": {str(path.relative_to(ROOT)): sha(path) for path in sources},
        "build_helpers": {path: sha(ROOT / path) for path in ["scripts/build_compiler.py", "scripts/polcert_core.py"]},
        "oracle": "bounded Fourier-Motzkin with checked LCF certificates",
        "candidate_configuration": "GUARDCERT_AFFINE_MODE; independently checked source, domain, schedule and tiling proposals",
        "guard_configuration": "actual loaded-plus-offset capture, recursive raw-observation stability scans and multi-array alias scans; retained repeated-expression fallback",
        "minimal_semantic_kernel_changed": False,
        "private_count": 32,
    }, indent=2) + "\n")
    print(f"verified loaded-plus-offset recursive-affine compiler: {WORK / 'ccomp'}")


if __name__ == "__main__":
    main()
