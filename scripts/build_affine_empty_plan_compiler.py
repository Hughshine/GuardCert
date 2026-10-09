"""Extract the selected compiler with compact header-only empty affine rewrites."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

import build_compiler
import polcert_core
import audit_affine_empty_plan as audit

ROOT = Path(__file__).resolve().parents[1]
UPSTREAM = ROOT / "vendor/CompCert"
ADAPTER = ROOT / "adapters/compcert-memory"
WORK = ROOT / "build/affine-empty-plan/compiler-v1"
PROOF = ROOT / "build/affine-empty-plan/proof-v1/report.json"
ENTRY = "ClightSelectedEmptySnapshotPlannedCompiler.compile_selected_empty_snapshot_planned_regions"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(*arguments):
    subprocess.run(arguments, cwd=WORK, check=True)


def main():
    global WORK
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work",type=Path,default=WORK)
    args=parser.parse_args()
    WORK=args.work.resolve()
    assert WORK.is_relative_to(ROOT / "build/affine-empty-plan")
    assert not WORK.exists(), "Refusing to overwrite a compiler checkpoint"
    polcert_core.select_profile("optimizer")
    proof = audit.validate()
    assert proof["status"] == "compiled" and "ClightSelectedEmptySnapshotPlannedCompiler.compile_selected_empty_snapshot_planned_regions_correct" in proof["endpoint_assumptions"]
    assert proof["additional_global_axioms"] == []
    for path,digest in proof["bindings"].items():
        assert sha(ROOT / path)==digest,path
    shutil.copytree(UPSTREAM, WORK, dirs_exist_ok=True, copy_function=build_compiler.copy_source,
                   ignore=shutil.ignore_patterns("*.vo", "*.vos", "*.vok", "*.glob", ".*.aux",
                       "*.cmi", "*.cmx", "*.cmo", "*.o", "*.a", ".depend*", "STAMP"))
    for pattern in ("*.ml", "*.mli", "*.cmi", "*.cmx", "*.o"):
        for path in (WORK / "extraction").glob(pattern):
            path.unlink()
    original = (UPSTREAM / "driver/Driver.ml").read_text()
    needle = "(Compiler.transf_c_program csyntax)"
    assert original.count(needle) == 1
    invocation = "(GuardScopFrontend.trace (); let scan_service = (match Sys.getenv_opt \"GUARDCERT_ALIAS_SCAN\" with Some \"pair\" -> ClightMultiTensorScanService.pair_scan_builder | Some \"canonical\" -> ClightMultiTensorScanService.canonical_scan_builder | Some \"dedup\" -> ClightDeduplicatedScanService.deduplicated_scan_builder | None | Some \"linear\" -> ClightLinearCanonicalScanService.linear_canonical_scan_builder | Some _ -> invalid_arg \"GUARDCERT_ALIAS_SCAN must be linear, dedup, canonical or pair\") in " + ENTRY + " scan_service (GuardScopFrontend.chosen_labels ()) GuardWordNestedStoreAffineCandidate.describe GuardWordNestedStoreAffineCandidate.describe_cached (GuardRankedMultiTensorPipelineCandidate.propose 2) GuardSignedAffinePipelineCandidate.describe GuardSignedAffinePipelineCandidate.propose GuardLoadedAffinePipelineCandidate.profile GuardLoadedAffinePipelineCandidate.propose (fun source -> match Sys.getenv_opt \"GUARDCERT_TENSOR_MODE\" with Some \"disabled\" -> None | _ -> GuardAffineSnapshotPipelineCandidate.profile source) GuardAffineSnapshotPipelineCandidate.propose (GuardTensorLiteralRegionCandidate.nat 100) csyntax)"
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
Extraction Inline Debugging.trace Debugging.failwith.
Extract Constant PedraQBackend.t => "unit".
Extract Constant PedraQBackend.top => "()".
Extract Constant PedraQBackend.pr => "(fun _ -> String.empty)".
Extract Constant PedraQBackend.isEmpty => "GuardMemoryOracle.is_empty".
Extract Constant PedraQBackend.add => "GuardCompactMemoryOracle.add".
Extract Constant TopoSort.topo_sort_untrusted => "GuardMemoryTopo.sort".
Extraction Inline Core.Base.pure Core.Base.imp CoreAlarmed.Base.pure CoreAlarmed.Base.imp.
'''
    extraction = WORK / "extract_tensor_regions.v"
    roots = ENTRY + " ClightAffineInnerPointerCandidates.propose_affine_inner_pointer_profile ClightLinearCanonicalScanService.linear_canonical_scan_builder ClightDeduplicatedScanService.deduplicated_scan_builder ClightMultiTensorScanService.canonical_scan_builder ClightMultiTensorScanService.pair_scan_builder GuardMemoryTiledPreparedPipeline.checked_memory_tiled_prepared_loop GuardMemoryScalarLoops.memory_scalar_rectangle AffineNestRangeProposal.affine_source_range_proposal AffineNestMultiProposal.affine_reserve_multi_scans ClightTensorRegionPreservation.check_tensor_region_candidate ClightTensorRegionPackage.tensor_propose_nest ClightStructuredProgress.progress_syntax_size ClightLoopAdministrative.trim_loop_skips LinTerm.LinQ.export CstrC.Cstr.isContrad"
    extraction.write_text("From GuardInterface Require Import " + ENTRY.split(".")[0] + " ClightLinearCanonicalScanService ClightDeduplicatedScanService GuardMemoryTiledPreparedPipeline.\n"
        "From GuardMemory Require Import GuardMemoryScalarLoops.\n"
        "From GuardAffineNest Require Import AffineNestRangeProposal AffineNestMultiProposal.\n"
        "From polcert.lib Require Import ImpureAlarmConfig TopoSort.\n"
        "From Vpl Require Import CoqAddOn Debugging PedraQBackend CstrC LinTerm.\n"
        + extraction_text.replace("Separate Extraction\n", mappings + "\nSeparate Extraction " + roots + "\n"))
    flags = [*polcert_core.load_flags(), "-Q", str(ADAPTER), "GuardMemory",
             "-Q", str(ROOT / "prototype/interface"), "GuardInterface",
             "-Q", str(ROOT / "prototype/affine-nest"), "GuardAffineNest"]
    flags += ["-Q", str(audit.language.WORK), "GuardLoadedAffine"]
    for name in ("cparser", "export", "MenhirLib"):
        flags += ["-R", str(UPSTREAM / name), "MenhirLib" if name == "MenhirLib" else "compcert." + name]
    run("rocq", "compile", *flags, str(extraction))
    inferred = ["ImpureConfig", "TilingValidator", "GuardMemoryPolyhedral", "GuardMemoryTilingProgress"]
    for module in inferred:
        (WORK / "extraction" / (module + ".mli")).unlink(missing_ok=True)
    for source in (WORK / "extraction").glob("*.ml"):
        assert "AXIOM TO BE REALIZED" not in source.read_text(), source.name
    sources = [ADAPTER / "native" / name for name in
               ["GuardMemoryNumbersCompCert.ml", "GuardMemoryOracle.ml", "GuardCompactMemoryOracle.ml", "GuardMemoryTopo.ml"]]
    sources += [ROOT / "prototype/interface/native" / name for name in ["GuardTensorAffineRegionCandidate.ml", "GuardTensorLiteralRegionCandidate.ml", "GuardMultiTensorAffineRegionCandidate.ml", "GuardAffineMultiTensorPipelineCandidate.ml", "GuardWordNestedStoreAffineCandidate.ml", "GuardRankedMultiTensorPipelineCandidate.ml", "GuardActualAffinePipelineCandidate.ml", "GuardProfiledAffinePipelineCandidate.ml", "GuardSignedAffineBounds.ml", "GuardSignedAffinePipelineCandidate.ml", "GuardLoadedAffinePipelineCandidate.ml", "GuardAffineSnapshotPipelineCandidate.ml"]]
    sources += [ROOT / "prototype/annotated-polyhedral/native" / name for name in ["GuardScopFrontend.ml", "GuardOpenScopIO.ml", "GuardTiledPreparedTensorCandidate.ml", "GuardTightPreparedTensorCandidate.ml", "GuardCompletedPreparedTensorCandidate.ml"]]
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
        "empty_header_only_builder_after_existing_registry": True,
        "empty_private_boolean_lowering": True,
        "empty_single_original_fallback": True,
        "empty_snapshot_cache_count": 2,
        "empty_snapshot_private_boolean_count": 1,
        "empty_negative_child_public_counter_zero": True,
        "empty_outer_skips_child_load": True,
        "empty_no_body_pointer_observation_requirement": True,
        "build_script_sha256": sha(Path(__file__)), "driver_sha256": sha(WORK / "driver/Driver.ml"),
        "parser_sha256": sha(WORK / "cparser/Parse.ml"),
        "proof_bindings": proof["bindings"], "extraction_sha256": sha(extraction),
        "proof_report_sha256": sha(PROOF),
        "native_sources": {str(path.relative_to(ROOT)): sha(path) for path in sources},
        "build_helpers": {path: sha(ROOT / path) for path in ["scripts/build_compiler.py", "scripts/polcert_core.py"]},
        "oracle": "bounded Fourier-Motzkin with checked LCF certificates; ordinary parallel-row compaction, checked against all original constraints by ExactCs.fromCs during codegen canonicalization",
        "ordinary_constraint_compaction_connected": True,
        "ordinary_compaction_separately_verified": False,
        "candidate_configuration": "Stable affine path adds only small request intervals to the proposed source model and rechecks against the original request/bounds; large machine-word intervals are omitted from scheduler transport; GUARDCERT_POLYHEDRAL_MODE / GUARDCERT_PLUTO; exported model, checked affine import and tiling transition, actual PolCert prepared codegen; unit coordinate completion and signed interval enclosures with exact membership guards proposed; all-unit output uses checked affine reindex; partial-unit output uses singleton point completion and original tiling witness; actual candidate factory rechecks all results",
        "scan_service_selector": {"environment": "GUARDCERT_ALIAS_SCAN", "default": "linear", "choices": ["linear", "dedup", "canonical", "pair"], "ordinary_source_user_semantic_callback": False},
        "guard_configuration": "Four closed certified scan-service builders share one factory, loaded region and selected compiler; source-licensed numeric/layout/box/profile setup with verified readonly repeated-probe elimination, checked fresh private result and shared fallback; linear service deduplicates original root/map templates and checks only loop-coefficient equality, allowing different constants and stable scalar coefficients; checked loop-linear/cap eligibility selects actual canonical difference scanner with four fresh int32 vectors, otherwise old point-pair scan; outer empty bypass; source-licensed complete header stability guard; header refusal runs original loaded AST, inner setup/alias refusal runs cached AST; checked candidate and public iterator restoration",
        "minimal_semantic_kernel_changed": False,
        "signed_interval_bound_proposals": True,
        "signed_interval_proposer_verified_separately": False,
        "prepared_pipeline_proof_bindings": proof["bindings"],
        "selected_only_discovery_and_installation": True,
        "annotation_boundary": "native parser pass before elaboration; marker labels retained through SimplExpr/SimplLocals",
        "external_scheduler_callback_connected": True,
        "prepared_codegen_candidate_producer": True,
        "actual_generated_candidate_interface": True, "tiling_transition_checked": True,
        "private_count": 100, "loaded_word_source_rank": 2, "stable_affine_source_rank": "actual checked request", "synthetic_axis_added": False,
        "stable_affine_source_rectangular_surrogate": False,
        "certified_builders_share_selected_installation_and_backend": True,
        "stable_affine_and_loaded_word_semantic_domains_identified": False,
        "private_loaded_affine_source_rank": 2,
        "private_loaded_affine_actual_pipeline_request": True,
        "private_loaded_affine_final_factory_checker": "ClightAffinePrivateLoadedCandidates.check_affine_private_loaded_source",
        "conditional_child_load_supported": True,
        "conditional_affine_snapshot_factory": "ClightAffineZeroSnapshotPlannedCandidates.check_affine_zero_snapshot_planned_source",
        "conditional_affine_snapshot_original_source_preserved": True,
        "existing_registry_fixed_in_Rocq": True,
        "conditional_affine_snapshot_cache_count": 2,
        "conditional_affine_snapshot_private_boolean_count": 1,
        "conditional_affine_snapshot_complete_tree_materialized": False,
        "conditional_affine_snapshot_guard": "checked header/ranges followed by alternative first-or-second-reached input licensing, nonnegative width preparation, original N/M stability scan, data alias and candidate ranges; compact private Boolean choice with original repeated-load fallback",
        "rmw_snapshot_factory": "ClightAffineRmwSnapshotPlannedCandidates.check_affine_rmw_snapshot_planned_source",
        "rmw_scalar_selected_by_checked_source": True,
        "rmw_actual_row_syntax_checked": True,
        "rmw_stability_contract": "actual row preserves already matching Mint32 header observations; alpha-zero value preservation or original separation scan",
        "rmw_alpha_read_licensed_after_numeric_preparation": True,
        "rmw_whole_memory_equality_claimed": False,
        "rmw_builder_precedes_zero_width_registry": True,
        "rmw_guard_configuration": "original conditional captures, checked numeric preparation and first-or-second reached body licensing; alpha-zero test then value-preservation acceptance or original compact separation scan; unchanged data alias and actual candidate ranges; original repeated-load fallback",
        "zero_width_actual_candidate_rechecked": True,
        "zero_width_snapshot_factory_precedes_existing": True,
        "zero_width_first_or_second_reached_preparation": True,
        "private_loaded_affine_and_recursive_affine_models_identified": False,
    }, indent=2) + "\n")
    print(f"verified selected word/affine/private-loaded/conditional-snapshot compiler: {WORK / 'ccomp'}")


if __name__ == "__main__":
    main()
