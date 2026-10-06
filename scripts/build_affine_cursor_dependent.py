"""Extract and build the dependent-header affine compiler with actual nested guard cursors."""
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
WORK = ROOT / "build/affine-cursor-dependent-compiler/compiler"
PROOF = ROOT / "build/affine-cursor-dependent-compiler/proof/report.json"
ENTRY = "ClightGuardedAffineCursorDependentCompiler.compile_guarded_affine_cursor_dependent"


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
    invocation = "(" + ENTRY + " GuardAffineInnerPointerCandidate.profile GuardAffineInnerPointerCandidate.propose (GuardMemoryCandidate.natural 21) csyntax)"
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
    extraction = WORK / "extract_cursor_dependent.v"
    roots = ENTRY + " ClightAffineInnerPointerCandidates.propose_affine_inner_pointer_profile ClightAffineInnerPointerCandidates.propose_affine_inner_pointer_tiling LinTerm.LinQ.export CstrC.Cstr.isContrad"
    extraction.write_text("From GuardInterface Require Import " + ENTRY.split(".")[0] + ".\n"
        "From polcert.lib Require Import ImpureAlarmConfig TopoSort.\n"
        "From Vpl Require Import CoqAddOn Debugging PedraQBackend CstrC LinTerm.\n"
        + extraction_text.replace("Separate Extraction\n", mappings + "\nSeparate Extraction " + roots + "\n"))
    flags = [*polcert_core.load_flags(), "-Q", str(ADAPTER), "GuardMemory",
             "-Q", str(ROOT / "prototype/interface"), "GuardInterface"]
    for name in ("cparser", "export", "MenhirLib"):
        flags += ["-R", str(UPSTREAM / name), "MenhirLib" if name == "MenhirLib" else "compcert." + name]
    run("rocq", "compile", *flags, str(extraction))
    inferred = ["ImpureConfig", "TilingValidator", "GuardMemoryPolyhedral", "GuardMemoryTilingProgress"]
    for module in inferred:
        (WORK / "extraction" / (module + ".mli")).unlink(missing_ok=True)
    for source in (WORK / "extraction").glob("*.ml"):
        assert "AXIOM TO BE REALIZED" not in source.read_text(), source.name
    # check_plan_tree is only a proof specification: generating an expanded
    # tree here would reintroduce the exponential continuation duplication.
    extracted_plan = (WORK / "extraction/ClightCheckPlan.ml").read_text()
    assert "let rec check_plan_tree" not in extracted_plan
    erased_specs = ["let rec bounded_check_tree", "let rec affine_dependent_stability_tree"]
    for source in (WORK / "extraction").glob("*.ml"):
        for specification in erased_specs:
            assert specification not in source.read_text(), (source.name, specification)
    sources = [ADAPTER / "native" / name for name in
               ["GuardMemoryNumbersCompCert.ml", "GuardMemoryOracle.ml", "GuardMemoryCandidate.ml", "GuardAffineInnerPointerCandidate.ml"]]
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
        "candidate_configuration": "GUARDCERT_LOOP_CANDIDATE, GUARDCERT_AFFINE_* source metadata",
        "guard_configuration": "two nested short-circuit private cursor loops; staged compact checks; fresh Boolean; dynamic physical writes/bound separation; ordered private pointer and bound captures; compound-header fallback",
        "expanded_plan_tree_extracted": False,
        "expanded_bounded_scan_tree_extracted": False,
        "expanded_dependent_stability_tree_extracted": False,
        "actual_nested_cursor_guard": True,
        "private_count": 21,
    }, indent=2) + "\n")
    print(f"verified nested-cursor dependent-header compiler: {WORK / 'ccomp'}")


if __name__ == "__main__":
    main()
