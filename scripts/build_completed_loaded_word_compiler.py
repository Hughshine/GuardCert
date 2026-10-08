"""Extract the loaded-word frontend compiler with actual checked scheduling/codegen proposals."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

import build_compiler
import polcert_core
import audit_zero_loaded_word

ROOT = Path(__file__).resolve().parents[1]
UPSTREAM = ROOT / "vendor/CompCert"
ADAPTER = ROOT / "adapters/compcert-memory"
WORK = ROOT / "build/loaded-word-completed/compiler"
PROOF = ROOT / "build/loaded-word-zero/proof-v2/report.json"
ENTRY = "ClightSelectedZeroLoadedWordFrontendCompiler.compile_selected_zero_loaded_word_frontend_regions"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(*arguments):
    subprocess.run(arguments, cwd=WORK, check=True)


def main():
    assert not WORK.exists(), "Refusing to overwrite a compiler checkpoint"
    polcert_core.select_profile("optimizer")
    proof = audit_zero_loaded_word.validate()
    assert proof["status"] == "compiled" and proof["new_whole_program_entrypoint"] == ENTRY + "_correct"
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
    invocation = "(GuardScopFrontend.trace (); " + ENTRY + " (GuardScopFrontend.chosen_labels ()) GuardZeroLoadedWordTensorCandidate.describe GuardTensorAffineRegionCandidate.describe GuardCompletedPreparedTensorCandidate.propose (GuardTensorLiteralRegionCandidate.nat 42) csyntax)"
    replacement = """(let outcome = ref None in
      ImpureConfig.Core.Base.bind INVOCATION
        (fun (result, alarm_free) -> outcome := Some (result, alarm_free); ());
      match !outcome with
      | Some (result, true) -> result
      | _ -> invalid_arg "GuardCert dependence checker raised an alarm")""".replace("INVOCATION", invocation)
    (WORK / "driver/Driver.ml").write_text(original.replace(needle, replacement))
    parser_source = (UPSTREAM / "cparser/Parse.ml").read_text()
    parser_needle = '  |> Timing.time "Elaboration" Elab.elab_file'
    assert parser_source.count(parser_needle) == 1
    (WORK / "cparser/Parse.ml").write_text(parser_source.replace(parser_needle,
        '  |> GuardScopFrontend.program\n' + parser_needle))
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
Extract Constant TopoSort.topo_sort_untrusted => "GuardMemoryTopo.sort".
Extraction Inline Core.Base.pure Core.Base.imp CoreAlarmed.Base.pure CoreAlarmed.Base.imp.
'''
    extraction = WORK / "extract_tensor_regions.v"
    roots = ENTRY + " GuardMemoryTiledPreparedPipeline.checked_memory_tiled_prepared_loop GuardMemoryScalarLoops.memory_scalar_rectangle ClightTensorRegionPreservation.check_tensor_region_candidate LinTerm.LinQ.export CstrC.Cstr.isContrad"
    extraction.write_text("From GuardInterface Require Import " + ENTRY.split(".")[0] + " GuardMemoryTiledPreparedPipeline.\n"
        "From GuardMemory Require Import GuardMemoryScalarLoops.\n"
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
               ["GuardMemoryNumbersCompCert.ml", "GuardMemoryOracle.ml", "GuardMemoryTopo.ml"]]
    sources += [ROOT / "prototype/interface/native" / name for name in ["GuardTensorAffineRegionCandidate.ml", "GuardTensorLiteralRegionCandidate.ml"]]
    sources += [ROOT / "prototype/annotated-polyhedral/native" / name for name in ["GuardScopFrontend.ml", "GuardOpenScopIO.ml", "GuardTiledPreparedTensorCandidate.ml", "GuardTightPreparedTensorCandidate.ml", "GuardCompletedPreparedTensorCandidate.ml", "GuardLoadedWordTensorCandidateV3.ml", "GuardZeroLoadedWordTensorCandidate.ml"]]
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
        "parser_sha256": sha(WORK / "cparser/Parse.ml"),
        "proof_sources": proof["sources"], "extraction_sha256": sha(extraction),
        "proof_report_sha256": sha(PROOF),
        "native_sources": {str(path.relative_to(ROOT)): sha(path) for path in sources},
        "build_helpers": {path: sha(ROOT / path) for path in ["scripts/build_compiler.py", "scripts/polcert_core.py"]},
        "oracle": "bounded Fourier-Motzkin with checked LCF certificates",
        "candidate_configuration": "GUARDCERT_POLYHEDRAL_MODE / GUARDCERT_PLUTO; exported model, checked affine import and tiling transition, actual PolCert prepared codegen; unit coordinate completion and tile-local affine bounds proposed; all-unit output uses checked affine reindex; partial-unit output uses singleton point completion and original tiling witness; actual candidate factory rechecks all results",
        "guard_configuration": "conditional loaded-header capture and profile gates; source-licensed alpha equality chooses constant-time zero-RMW preparation or the historical complete stability scan; followed by numeric/layout guard; language-equivalent base original fallback and public counter restoration",
        "minimal_semantic_kernel_changed": False,
        "prepared_pipeline_proof_sources": proof["sources"],
        "selected_only_discovery_and_installation": True,
        "annotation_boundary": "native parser pass before elaboration; marker labels retained through SimplExpr/SimplLocals",
        "external_scheduler_callback_connected": True,
        "prepared_codegen_candidate_producer": True,
        "actual_generated_candidate_interface": True, "tiling_transition_checked": True,
        "private_count": 42,
    }, indent=2) + "\n")
    print(f"verified selected-region compiler: {WORK / 'ccomp'}")


if __name__ == "__main__":
    main()
