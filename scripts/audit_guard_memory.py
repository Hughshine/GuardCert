"""Compile the concrete CompCert-memory INSTR and audit its semantic boundary."""
from pathlib import Path
import hashlib
import json
import subprocess

from audit_compiler import names
import polcert_core

ROOT = Path(__file__).resolve().parents[1]
MODULES = ["GuardMemoryRuntime", "GuardMemoryInstr", "GuardMemoryRectangles", "GuardMemoryPolyhedral",
           "GuardMemoryLoops", "GuardMemoryClightRectangles", "GuardMemoryPolyhedralRectangles",
           "GuardMemoryValidatedRectangles", "GuardMemoryCompiler", "GuardMemoryTilingProgress", "GuardMemoryArrayBackend",
           "GuardMemoryLoopTrace", "GuardMemoryTiledRectangles", "GuardMemoryTiledExecution",
           "GuardMemoryTiledClight", "GuardMemoryFlatArrayBackend", "GuardMemoryModeTiledClight",
           "GuardMemoryTiledCompiler", "GuardMemoryAffineDomains",
           "GuardMemoryConditionalLoops", "GuardMemoryCutExecution", "GuardMemoryCutClight",
           "GuardMemoryCutTiledClight", "GuardMemoryCutCompiler", "GuardMemoryTilingMultipleProgress", "GuardMemoryArrayFamilyBackend", "GuardMemoryIndexedTrace",
           "GuardMemorySequenceLoops", "GuardMemorySequenceClight", "GuardMemorySequencePolyhedral",
           "GuardMemorySequenceOrder", "GuardMemorySequenceExecution", "GuardMemorySequenceTiledClight",
           "GuardMemorySequenceCompiler", "GuardMemoryOperationsClight", "GuardMemoryOperationsTiledClight",
           "GuardMemoryOperationsCompiler", "GuardMemoryExtractorTrace", "GuardMemoryTraceUniqueness",
           "GuardMemoryExtractorCoverage", "GuardMemoryExtractorOrder", "GuardMemoryPointIsomorphism", "GuardMemoryDomainNormalization", "GuardMemoryExtractorProgress",
           "GuardMemoryCoordinateSwap", "GuardMemoryCoordinateShift", "GuardMemoryCoordinateSkew", "GuardMemoryReindexedExtractor",
           "GuardMemoryDomainAlignment", "GuardMemoryExtractedTiling", "GuardMemoryEquivalentDomainsExtractor", "GuardMemoryAffineReindex", "GuardMemoryAffineMappedExtractor",
           "GuardMemoryProposedClight", "GuardMemoryProposedCompiler", "GuardMemoryGeneratedBounds", "GuardMemoryScheduleProducer",
           "GuardMemoryMultipleArrays", "GuardMemoryArraySeparation", "GuardMemoryRegistryBackend", "GuardMemoryRegistryTransfer", "GuardMemoryCrossArray", "GuardMemoryCrossInstruction", "GuardMemoryCopyArray", "GuardMemoryCopyInstruction", "GuardMemoryNamedOperations", "GuardMemoryNamedRegistrySource", "GuardMemoryRegistryGuard", "GuardMemoryNamedClight", "GuardMemoryNamedGuard", "GuardMemoryNamedCandidate", "GuardMemoryNamedChecker", "GuardMemoryNamedCompiler", "GuardMemoryNamedMappedChecker", "GuardMemoryNamedMappedCompiler", "GuardMemoryVariableCounterExit", "GuardMemoryRaggedLoops", "GuardMemoryRaggedClight", "GuardMemoryRaggedGuard", "GuardMemoryRaggedBackend", "GuardMemoryNamedRaggedSource", "GuardMemoryNamedRaggedCandidate", "GuardMemoryNamedRaggedChecker", "GuardMemoryTileRangeTrimming", "GuardMemoryRaggedTiling", "GuardMemoryNamedRaggedTiling", "GuardMemoryNamedRaggedCompiler", "GuardMemoryScheduledCompiler", "GuardMemoryAffineSourceExpressions", "GuardMemoryAffineSourceReifier", "GuardMemoryAffineSourceValuation", "GuardMemoryAffineSourceLoop", "GuardMemoryAffineSourceContext", "GuardMemoryAffineSourceEndpoints", "GuardMemoryParametricSourceClight", "GuardMemoryParametricLoops", "GuardMemoryNamedParametricSource", "GuardMemoryParametricWidth", "GuardMemoryParametricRestore", "GuardMemoryParametricGuard", "GuardMemoryParametricSourceDomain", "GuardMemoryParametricSyntax", "GuardMemoryParametricChecker", "GuardMemoryParametricTiling", "GuardMemoryParametricCandidate", "GuardMemoryParametricCompiler", "GuardMemoryCommonLayout", "GuardMemoryLayoutCopy", "GuardMemoryLayoutCopyInstruction", "GuardMemoryLayoutCopyRegistry", "GuardMemoryCopyLayoutRegistry", "GuardMemoryLayoutCopySource", "GuardMemoryLayoutCopyDomain", "GuardMemoryParametricInstructionChecker", "GuardMemoryParametricInstructionTiling", "GuardMemoryLayoutCopyCandidate", "GuardMemoryLayoutCopySyntax", "GuardMemoryLayoutCopyCompiler", "GuardMemoryParametricBody", "GuardMemoryNamedBodyModel", "GuardMemoryLayoutCopyBodyModel", "GuardMemoryParametricBodyDomain", "GuardMemoryParametricBodyCandidate", "GuardMemoryParametricRegion", "GuardMemoryLayoutRegistry", "GuardMemoryLayoutCopyRegistryPoint", "GuardMemoryLayoutOperations", "GuardMemoryLayoutSequence", "GuardMemoryLayoutRanges", "GuardMemoryLayoutBodyModel", "GuardMemoryLayoutSyntax", "GuardMemoryAffineAccessExpressions", "GuardMemoryAffineAccess", "GuardMemoryAffineCopy", "GuardMemoryGeneralLayoutOperations", "GuardMemoryGeneralLayoutSequence", "GuardMemoryGeneralLayoutBodyModel", "GuardMemoryGeneralLayoutSyntax", "GuardMemoryAccessAnchors", "GuardMemoryOffsetAccessRanges", "GuardMemoryOffsetBodyModel", "GuardMemoryOffsetSyntax", "GuardMemorySourceValues", "GuardMemoryAffineReadRegistry", "GuardMemoryAffineCompute", "GuardMemoryComputeAnchors", "GuardMemoryComputeSequence", "GuardMemoryComputeBodyModel", "GuardMemoryComputeSyntax", "GuardMemoryParametricRegionInstances", "GuardMemoryParametricRegionCompiler", "GuardMemoryUnifiedCompiler"]
LOWERING_MODULES = ["ClightPositiveDivision", "PolCertLoopGuard", "PolCertAffineClight", "PolCertAffineGuard",
                    "PolCertCountedClight", "PolCertClightBody", "PolCertNestedClight"]
DIRECTORY = ROOT / "adapters" / "compcert-memory"
WORK = ROOT / "build" / "guard-memory-assumptions"


def main():
    polcert_core.select_profile("optimizer")
    report = json.loads(polcert_core.artifact("report.json").read_text())
    if (report["status"] != "compiled" or report["source_manifest_sha256"] !=
            hashlib.sha256(polcert_core.MANIFEST.read_bytes()).hexdigest()):
        raise SystemExit("build the locked PolCert optimizer proof profile first")
    flags = [*polcert_core.load_flags(), "-Q", str(DIRECTORY), "GuardMemory"]
    WORK.mkdir(parents=True, exist_ok=True)
    logs = []
    for module in LOWERING_MODULES:
        result = subprocess.run(["rocq", "compile", *flags, str(ROOT / "theories" / (module + ".v"))],
                                cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        logs.append(result.stdout)
    for module in MODULES:
        result = subprocess.run(["rocq", "compile", *flags, str(DIRECTORY / (module + ".v"))],
                                cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        logs.append(result.stdout)
    (WORK / "build.log").write_text("\n".join(logs))
    audit = WORK / "Audit.v"
    audit.write_text("""From compcert.driver Require Import Compiler.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles GuardMemoryPolyhedral
  GuardMemoryLoops GuardMemoryClightRectangles GuardMemoryPolyhedralRectangles
  GuardMemoryValidatedRectangles GuardMemoryCompiler GuardMemoryTilingProgress GuardMemoryArrayBackend
  GuardMemoryLoopTrace GuardMemoryTiledRectangles GuardMemoryTiledExecution GuardMemoryTiledClight
  GuardMemoryFlatArrayBackend GuardMemoryModeTiledClight GuardMemoryTiledCompiler
  GuardMemoryAffineDomains GuardMemoryConditionalLoops GuardMemoryCutExecution GuardMemoryCutClight
  GuardMemoryCutTiledClight GuardMemoryCutCompiler GuardMemoryTilingMultipleProgress
  GuardMemoryArrayFamilyBackend GuardMemoryIndexedTrace GuardMemorySequenceLoops GuardMemorySequenceClight
  GuardMemorySequencePolyhedral GuardMemorySequenceOrder GuardMemorySequenceExecution
  GuardMemorySequenceTiledClight GuardMemorySequenceCompiler GuardMemoryOperationsClight
  GuardMemoryOperationsTiledClight GuardMemoryOperationsCompiler GuardMemoryExtractorTrace GuardMemoryTraceUniqueness
  GuardMemoryExtractorCoverage GuardMemoryExtractorOrder GuardMemoryPointIsomorphism GuardMemoryDomainNormalization GuardMemoryExtractorProgress GuardMemoryCoordinateSwap GuardMemoryCoordinateShift GuardMemoryCoordinateSkew GuardMemoryReindexedExtractor GuardMemoryDomainAlignment GuardMemoryExtractedTiling GuardMemoryEquivalentDomainsExtractor GuardMemoryAffineReindex GuardMemoryAffineMappedExtractor
  GuardMemoryProposedClight GuardMemoryProposedCompiler GuardMemoryGeneratedBounds GuardMemoryScheduleProducer
  GuardMemoryMultipleArrays GuardMemoryArraySeparation GuardMemoryRegistryBackend GuardMemoryRegistryTransfer GuardMemoryCrossArray GuardMemoryCrossInstruction GuardMemoryCopyArray GuardMemoryCopyInstruction GuardMemoryNamedOperations GuardMemoryNamedRegistrySource GuardMemoryRegistryGuard GuardMemoryNamedClight GuardMemoryNamedGuard GuardMemoryNamedCandidate GuardMemoryNamedChecker GuardMemoryNamedCompiler GuardMemoryNamedMappedChecker GuardMemoryNamedMappedCompiler GuardMemoryVariableCounterExit GuardMemoryRaggedLoops GuardMemoryRaggedClight GuardMemoryRaggedGuard GuardMemoryRaggedBackend GuardMemoryNamedRaggedSource GuardMemoryNamedRaggedCandidate GuardMemoryNamedRaggedChecker GuardMemoryTileRangeTrimming GuardMemoryRaggedTiling GuardMemoryNamedRaggedTiling GuardMemoryNamedRaggedCompiler GuardMemoryScheduledCompiler GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceReifier GuardMemoryAffineSourceValuation GuardMemoryAffineSourceLoop GuardMemoryAffineSourceContext GuardMemoryAffineSourceEndpoints GuardMemoryParametricSourceClight GuardMemoryParametricLoops GuardMemoryNamedParametricSource GuardMemoryParametricWidth GuardMemoryParametricRestore GuardMemoryParametricGuard GuardMemoryParametricSourceDomain GuardMemoryParametricSyntax GuardMemoryParametricChecker GuardMemoryParametricTiling GuardMemoryParametricCandidate GuardMemoryParametricCompiler GuardMemoryCommonLayout GuardMemoryLayoutCopy GuardMemoryLayoutCopyInstruction GuardMemoryLayoutCopyRegistry GuardMemoryCopyLayoutRegistry GuardMemoryLayoutCopySource GuardMemoryLayoutCopyDomain GuardMemoryParametricInstructionChecker GuardMemoryParametricInstructionTiling GuardMemoryLayoutCopyCandidate GuardMemoryLayoutCopySyntax GuardMemoryLayoutCopyCompiler GuardMemoryParametricBody GuardMemoryNamedBodyModel GuardMemoryLayoutCopyBodyModel GuardMemoryParametricBodyDomain GuardMemoryParametricBodyCandidate GuardMemoryParametricRegion GuardMemoryLayoutRegistry GuardMemoryLayoutCopyRegistryPoint GuardMemoryLayoutOperations GuardMemoryLayoutSequence GuardMemoryLayoutRanges GuardMemoryLayoutBodyModel GuardMemoryLayoutSyntax GuardMemoryAffineAccessExpressions GuardMemoryAffineAccess GuardMemoryAffineCopy GuardMemoryGeneralLayoutOperations GuardMemoryGeneralLayoutSequence GuardMemoryGeneralLayoutBodyModel GuardMemoryGeneralLayoutSyntax GuardMemoryAccessAnchors GuardMemoryOffsetAccessRanges GuardMemoryOffsetBodyModel GuardMemoryOffsetSyntax GuardMemorySourceValues GuardMemoryAffineReadRegistry GuardMemoryAffineCompute GuardMemoryComputeAnchors GuardMemoryComputeSequence GuardMemoryComputeBodyModel GuardMemoryComputeSyntax GuardMemoryParametricRegionInstances GuardMemoryParametricRegionCompiler GuardMemoryUnifiedCompiler.
Goal True. idtac "MEM_CC_BASE". exact I. Qed.
Print Assumptions Compiler.transf_c_program_correct.
Goal True. idtac "MEM_VALIDATOR_BASE". exact I. Qed.
Print Assumptions GuardMemoryValidator.validate_correct.
Print Assumptions GuardMemoryValidator.validate_tiling_correct.
Print Assumptions GuardMemoryTilingValidator.checked_tiling_validate_poly_correct.
Goal True. idtac "MEM_PHYSICAL_REGISTRY". exact I. Qed.
Print Assumptions flat_array_locations_nonalias.
Print Assumptions memory_array_registry_nonalias.
Print Assumptions memory_array_base_comparison.
Print Assumptions memory_blocks_unique_correct.
Goal True. idtac "MEM_INSTRUCTION". exact I. Qed.
Print Assumptions GuardMemoryInstr.bc_condition_implie_permutbility.
Print Assumptions GuardMemoryInstr.access_function_checker_correct.
Print Assumptions resolved_instruction_execution.
Print Assumptions rect_memory_write_execution.
Print Assumptions rect_memory_write_clight_decode.
Print Assumptions rect_memory_update_execution.
Print Assumptions rect_memory_row_update_execution.
Print Assumptions memory_rectangle_loop_iterations.
Print Assumptions memory_rectangle_lift.
Print Assumptions memory_rectangle_source_clight_decode.
Print Assumptions memory_rectangle_candidate_clight_encode.
Print Assumptions array_write_backend.
Print Assumptions compile_memory_array_loop_correct.
Print Assumptions memory_loop_trace_correct.
Print Assumptions rectangle_tiled_loop_points.
Print Assumptions compile_memory_cut_condition_evaluation.
Print Assumptions memory_cut_source_clight_decode.
Print Assumptions array_family_source_clight_decode.
Print Assumptions array_family_backend.
Print Assumptions indexed_memory_loop_execution.
Print Assumptions memory_sequence_tiled_loop_points.
Print Assumptions array_operations_source_clight_decode.
Print Assumptions flat_array_instruction_backend.
Print Assumptions compile_memory_flat_array_loop_within_correct.
Print Assumptions memory_extractor_static_sites.
Print Assumptions memory_extractor_trace_metadata.
Print Assumptions memory_extracted_trace_execution.
Print Assumptions memory_extracted_trace_coverage_iff.
Print Assumptions memory_extracted_trace_points_unique.
Print Assumptions memory_extracted_trace_points_sorted.
Print Assumptions memory_extractor_execution_at.
Print Assumptions memory_point_isomorphism_execution.
Print Assumptions memory_domain_normalization_execution.
Print Assumptions memory_coordinate_swap_execution.
Print Assumptions memory_coordinate_shift_execution.
Print Assumptions memory_coordinate_skew_execution.
Print Assumptions memory_affine_reindexed_execution.
Print Assumptions memory_reindexed_execution.
Print Assumptions memory_array_separation_exact.
Print Assumptions memory_registry_instruction_backend.
Print Assumptions compile_memory_registry_loop_correct.
Print Assumptions memory_instruction_registry_transfer.
Print Assumptions memory_cross_update_evaluation.
Print Assumptions memory_cross_update_inverse.
Print Assumptions memory_cross_registry_execution.
Print Assumptions memory_copy_statement_evaluation.
Print Assumptions memory_copy_statement_inverse.
Print Assumptions memory_copy_registry_execution.
Print Assumptions named_operation_registry_execution.
Print Assumptions named_array_operations_source_clight_iterations.
Print Assumptions named_array_operations_registry.
Print Assumptions memory_registry_guard_primitives.
Print Assumptions named_array_operations_source_clight_decode.
Print Assumptions memory_named_guard_primitives.
Print Assumptions frontend_variable_settle_decode.
Print Assumptions memory_ragged_sequence_lift.
Print Assumptions memory_ragged_source_decode.
Print Assumptions memory_ragged_source_guard_domain.
Print Assumptions named_array_operations_ragged_source_decode.
Print Assumptions memory_ragged_width_exact.
Print Assumptions memory_ragged_guard_primitives.
Print Assumptions memory_ragged_parameter_bounds.
Print Assumptions memory_ragged_tile_trimming.
Print Assumptions memory_named_array_candidate_rule.
Print Assumptions memory_source_affine_evaluation.
Print Assumptions memory_source_affine_defined_words.
Print Assumptions memory_source_affine_decode.
Print Assumptions memory_source_affine_row_extrema.
Print Assumptions memory_source_affine_iteration_value.
Print Assumptions memory_source_loop_expression_value.
Print Assumptions memory_source_context_typed.
Print Assumptions memory_source_endpoints_sound.
Print Assumptions memory_parametric_source_decode.
Print Assumptions memory_parametric_source_words.
Print Assumptions memory_parametric_sequence_lift.
Print Assumptions named_array_operations_parametric_source_decode.
Print Assumptions compile_memory_source_width_sound.
Print Assumptions memory_parametric_restore_execution.
Print Assumptions memory_source_guard_primitives.
Print Assumptions memory_parametric_named_source_domain.
Print Assumptions memory_parametric_tile_trimming.
Print Assumptions memory_parametric_array_candidate_rule.
Print Assumptions memory_common_layout_facts.
Print Assumptions memory_common_layout_points.
Print Assumptions memory_layout_copy_statement_evaluation.
Print Assumptions memory_layout_copy_statement_inverse.
Print Assumptions memory_layout_copy_registry_execution.
Print Assumptions memory_layout_copy_registry.
Print Assumptions memory_layout_copy_point_execution.
Print Assumptions memory_copy_layout_registry.
Print Assumptions memory_copy_layout_point_execution.
Print Assumptions memory_parametric_body_source_decode.
Print Assumptions memory_named_body_model.
Print Assumptions memory_layout_copy_body_model.
Print Assumptions memory_descriptor_entries_exist.
Print Assumptions memory_layout_copy_general_registry_point.
Print Assumptions memory_layout_operation_clight_inverse.
Print Assumptions memory_layout_operation_registry_execution.
Print Assumptions memory_layout_sequence_registry.
Print Assumptions memory_layout_sequence_point_execution.
Print Assumptions memory_layout_body_model.
Print Assumptions memory_index_expression_evaluation.
Print Assumptions memory_affine_access_load_inverse.
Print Assumptions memory_affine_access_registry.
Print Assumptions memory_affine_copy_inverse.
Print Assumptions memory_affine_copy_registry_point.
Print Assumptions memory_general_layout_registry_execution.
Print Assumptions memory_general_sequence_registry.
Print Assumptions memory_general_sequence_point_execution.
Print Assumptions memory_general_layout_body_model.
Print Assumptions memory_general_anchors_registry.
Print Assumptions memory_index_offset_box_sound.
Print Assumptions memory_offset_sequence_point_execution.
Print Assumptions memory_offset_layout_body_model.
Print Assumptions check_memory_offset_region.
Print Assumptions memory_source_value_loads_exist.
Print Assumptions memory_source_value_evaluation_inverse.
Print Assumptions memory_affine_reads_resolve.
Print Assumptions memory_affine_reads_loads.
Print Assumptions memory_affine_compute_inverse.
Print Assumptions memory_affine_compute_registry.
Print Assumptions memory_compute_anchor_bindings.
Print Assumptions memory_compute_sequence_registry.
Print Assumptions memory_compute_sequence_point_execution.
Print Assumptions memory_compute_body_model.
Print Assumptions check_memory_compute_region.
Print Assumptions memory_parametric_body_source_domain.
Print Assumptions memory_parametric_body_candidate_rule.
Print Assumptions memory_layout_copy_source_decode.
Print Assumptions memory_layout_copy_source_domain.
Print Assumptions memory_layout_copy_candidate_rule.
Goal True. idtac "MEM_ADAPTED_VALIDATOR". exact I. Qed.
Print Assumptions guarded_memory_validate_refines.
Print Assumptions guarded_memory_validate_tiling_refines.
Print Assumptions guarded_memory_checked_tiling_refines.
Print Assumptions validated_memory_equivalence.
Print Assumptions validated_memory_equivalence_at.
Print Assumptions validated_memory_rectangle_interchange.
Print Assumptions before_to_retiled_old_progress.
Print Assumptions validated_memory_single_tiling_progress_at.
Print Assumptions guarded_memory_tiling_equivalence_refines.
Print Assumptions validated_memory_rectangle_tiling.
Print Assumptions validated_memory_cut_tiling.
Print Assumptions before_to_retiled_multiple_progress.
Print Assumptions validated_memory_multiple_tiling_progress_at.
Print Assumptions validated_memory_sequence_tiling.
Print Assumptions validated_memory_affine_loops_at.
Print Assumptions validated_memory_reindexed_loops_at.
Print Assumptions validated_memory_equivalent_domain_loops_at.
Print Assumptions memory_check_domain_equivalence_correct.
Print Assumptions memory_aligned_domains_execution.
Print Assumptions checked_named_affine_candidate_correct.
Print Assumptions validated_memory_affine_mapped_domain_loops_at.
Print Assumptions checked_named_mapped_candidate_correct.
Print Assumptions checked_named_ragged_candidate_correct.
Print Assumptions validated_memory_extracted_tiling_loops_at.
Print Assumptions checked_named_ragged_tiling_correct.
Print Assumptions memory_attempt_codegen_accept.
Print Assumptions memory_checked_generated_loop_certificate.
Print Assumptions checked_named_tiled_candidate_correct.
Print Assumptions checked_named_parametric_candidate_correct.
Print Assumptions checked_named_parametric_tiling_correct.
Print Assumptions checked_parametric_instruction_candidate_correct.
Print Assumptions checked_parametric_instruction_tiling_correct.
Goal True. idtac "MEM_REGION". exact I. Qed.
Print Assumptions memory_validated_rectangle_local.
Print Assumptions memory_validated_rectangle_rule.
Print Assumptions check_memory_region_sound.
Print Assumptions memory_tiled_rectangle_local.
Print Assumptions memory_tiled_rectangle_rule.
Print Assumptions check_memory_tiled_region_sound.
Print Assumptions memory_cut_tiled_local.
Print Assumptions check_memory_cut_region_sound.
Print Assumptions memory_tiled_array_family_local.
Print Assumptions memory_mode_tiled_rectangle_local.
Print Assumptions check_memory_sequence_region_sound.
Print Assumptions memory_tiled_array_operations_local.
Print Assumptions check_memory_operations_region_sound.
Print Assumptions memory_proposed_array_operations_local.
Print Assumptions check_memory_proposed_region_sound.
Print Assumptions check_memory_unified_region_sound.
Print Assumptions check_memory_named_affine_region_sound.
Print Assumptions check_memory_named_mapped_region_sound.
Print Assumptions check_memory_named_tiled_region_sound.
Print Assumptions check_memory_named_unified_region_sound.
Print Assumptions memory_ragged_array_candidate_local.
Print Assumptions memory_ragged_named_source_domain.
Print Assumptions memory_ragged_array_candidate_rule.
Print Assumptions check_memory_ragged_mapped_region_sound.
Print Assumptions check_memory_ragged_tiled_region_sound.
Print Assumptions check_memory_ragged_scheduled_region_sound.
Print Assumptions check_memory_named_scheduled_region_sound.
Print Assumptions check_memory_ragged_unified_region_sound.
Print Assumptions check_memory_parametric_mapped_region_sound.
Print Assumptions check_memory_parametric_scheduled_region_sound.
Print Assumptions check_memory_parametric_tiled_region_sound.
Print Assumptions check_memory_parametric_unified_region_sound.
Print Assumptions check_memory_layout_copy_mapped_region_sound.
Print Assumptions check_memory_layout_copy_scheduled_region_sound.
Print Assumptions check_memory_layout_copy_tiled_region_sound.
Print Assumptions check_memory_layout_copy_unified_region_sound.
Print Assumptions check_memory_parametric_region_mapped_sound.
Print Assumptions check_memory_parametric_region_conditioned_sound.
Print Assumptions check_memory_parametric_region_scheduled_sound.
Print Assumptions check_memory_parametric_region_conditioned_tiling_sound.
Goal True. idtac "MEM_COMPILER". exact I. Qed.
Print Assumptions compile_memory_regions_correct.
Print Assumptions compile_memory_tiled_regions_correct.
Print Assumptions compile_memory_cut_regions_correct.
Print Assumptions compile_memory_sequence_regions_correct.
Print Assumptions compile_memory_operations_regions_correct.
Print Assumptions compile_memory_proposed_regions_correct.
Print Assumptions compile_memory_unified_regions_correct.
Goal True. idtac "MEM_END". exact I. Qed.
""")
    result = subprocess.run(["rocq", "compile", *flags, str(audit)], cwd=ROOT, check=True,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (WORK / "audit.log").write_text(result.stdout)
    cc, rest = result.stdout.split("MEM_CC_BASE", 1)[1].split("MEM_VALIDATOR_BASE", 1)
    baseline, rest = rest.split("MEM_PHYSICAL_REGISTRY", 1)
    registry, rest = rest.split("MEM_INSTRUCTION", 1)
    instruction, rest = rest.split("MEM_ADAPTED_VALIDATOR", 1)
    adapted, rest = rest.split("MEM_REGION", 1)
    region, rest = rest.split("MEM_COMPILER", 1)
    compiler = rest.split("MEM_END", 1)[0]
    if names(registry) or "Closed under the global context" not in registry:
        raise SystemExit("unexpected physical-registry assumptions")
    if names(instruction) - names(cc) or names(adapted) != names(baseline):
        raise SystemExit("concrete memory adapter adds unexpected global assumptions")
    expected = names(cc) | names(baseline)
    if names(region) - expected or names(compiler) != expected:
        raise SystemExit("memory compiler differs from the CompCert and concrete validator union")
    sources = [DIRECTORY / (module + ".v") for module in MODULES]
    sources += sorted((ROOT / "theories").glob("*.v"))
    result = {
        "status": "compiled", "checked_modules": MODULES, "checked_lowering_modules": LOWERING_MODULES,
        "physical_flat_array_nonalias_global_axioms": [],
        "instruction_assumptions": sorted(names(instruction)),
        "actual_validator_baseline_assumptions": sorted(names(baseline)),
        "concrete_validator_assumptions": sorted(names(adapted)),
        "memory_region_assumptions": sorted(names(region)),
        "whole_program_assumptions": sorted(names(compiler)),
        "whole_program_entrypoint": "GuardMemoryCompiler.compile_memory_regions",
        "whole_program_theorem": "GuardMemoryCompiler.compile_memory_regions_correct",
        "cut_whole_program_entrypoint": "GuardMemoryCutCompiler.compile_memory_cut_regions",
        "cut_whole_program_theorem": "GuardMemoryCutCompiler.compile_memory_cut_regions_correct",
        "tiling_whole_program_entrypoint": "GuardMemoryTiledCompiler.compile_memory_tiled_regions",
        "tiling_whole_program_theorem": "GuardMemoryTiledCompiler.compile_memory_tiled_regions_correct",
        "sequence_whole_program_entrypoint": "GuardMemorySequenceCompiler.compile_memory_sequence_regions",
        "sequence_whole_program_theorem": "GuardMemorySequenceCompiler.compile_memory_sequence_regions_correct",
        "operations_whole_program_entrypoint": "GuardMemoryOperationsCompiler.compile_memory_operations_regions",
        "operations_whole_program_theorem": "GuardMemoryOperationsCompiler.compile_memory_operations_regions_correct",
        "proposed_whole_program_entrypoint": "GuardMemoryProposedCompiler.compile_memory_proposed_regions",
        "proposed_whole_program_theorem": "GuardMemoryProposedCompiler.compile_memory_proposed_regions_correct",
        "unified_whole_program_entrypoint": "GuardMemoryUnifiedCompiler.compile_memory_unified_regions",
        "unified_whole_program_theorem": "GuardMemoryUnifiedCompiler.compile_memory_unified_regions_correct",
        "one_guarded_compiler_for_affine_and_tiling_candidates_proved": True,
        "multiple_physical_arrays_registry_nonalias_closed": True,
        "array_object_base_guard_encoding_proved": True,
        "multiarray_actual_source_and_candidate_clight_bridge_proved": True,
        "multiarray_unified_csem_asm_proved": True,
        "multiarray_c_source_scope": "rectangular pure-write, own-cell and row-prefix statements on distinct actual array objects sharing a fixed layout; cross-array reads and pointer slices are not decoded",
        "untrusted_loop_candidate_csem_asm_proved": True,
        "untrusted_loop_candidate_c_source_scope": "canonical rectangular mixed statements on one fixed-layout array",
        "multiple_mixed_array_statements_tiling_csem_asm_proved": True,
        "operations_c_source_scope": "nonempty list of pure writes, own-cell updates and row-prefix updates on one fixed-layout array",
        "multiple_pure_array_statements_tiling_csem_asm_proved": True,
        "sequence_c_source_scope": "nonempty pure-write statement list on one fixed-layout array",
        "whole_program_acceptance": "alarm-free mayReturn with OK assembly program",
        "additional_global_axioms": [],
        "concrete_instr_module": "GuardMemoryInstr.GuardMemoryInstr",
        "actual_compcert_mem_load_store_execution": True,
        "state_equivalence": "exact registry and Mem equality",
        "instruction_interface_fields_are_proved": True,
        "cstate_valid_used": False,
        "affine_access_footprints_checked": True,
        "pure_payload_operations": ["constant", "parameter", "loaded value", "Int.add", "Int.sub", "Int.mul"],
        "actual_clight_store_to_instr_decoder_instantiated": True,
        "actual_affine_and_tiling_validator_instantiated": True,
        "actual_point_space_tiling_checker_instantiated": True,
        "bidirectional_affine_validation_establishes_progress": True,
        "single_statement_tiling_source_to_candidate_progress_proved": True,
        "tiling_progress_preserves_actual_parameters": True,
        "general_multiple_statement_tiling_progress_proved": True,
        "native_validator_validation_report": "build/native-memory-validator/report.json",
        "canonical_rectangle_clight_to_loop_decoder_instantiated": True,
        "canonical_rectangle_loop_to_clight_encoder_instantiated": True,
        "general_pure_array_loop_to_clight_encoder_instantiated": True,
        "general_single_flat_array_memory_loop_encoder_instantiated": True,
        "flat_array_encoder_payload_operations": ["constant", "parameter", "loaded value", "Int.add", "Int.sub", "Int.mul"],
        "read_modify_write_rectangle_tiling_csem_asm_proved": True,
        "row_prefix_read_rectangle_tiling_csem_asm_proved": True,
        "nonnegative_floor_division_lowering_proved": True,
        "pure_rectangle_two_dimensional_tiling_csem_asm_proved": True,
        "affine_conditional_domain_two_dimensional_tiling_csem_asm_proved": True,
        "conditional_domain_c_source_scope": "one static affine leaf cut with nonnegative limit",
        "pure_rectangle_tiling_public_exit": "agreement on all source program temporaries and exact Mem",
        "pure_rectangle_tiling_partial_tiles_checked": True,
        "canonical_rectangle_memory_modes": ["pure write", "own-cell update", "row-prefix update"],
        "canonical_rectangle_public_exit": "exact full temporary environment and Mem",
        "canonical_rectangle_clight_poly_bridge_instantiated": True,
        "canonical_rectangle_dependence_csem_asm_rule_instantiated": True,
        "polyhedral_parameters_preserved_by_validator": True,
        "complete_source_loop_decoder_instantiated": False,
        "complete_candidate_loop_encoder_instantiated": False,
        "complete_csem_asm_rule_instantiated": False,
        "general_affine_loop_to_poly_execution_equivalence_proved": True,
        "general_loop_statement_scope": "arbitrary nesting of affine Loop, Seq and conjunctive affine Guard accepted by the actual extractor",
        "semantically_equivalent_affine_domain_alignment_proved": True,
        "domain_equivalence_uses_existing_emptiness_certificates": True,
        "adjacent_iterator_coordinate_permutation_proved": True,
        "externally_proposed_iterator_coordinate_swaps_consumed": True,
        "domain_constraint_order_normalization_proved": True,
        "point_representation_isomorphism_semantic_interface_proved": True,
        "array_entry_presumption_consumed_by_candidate_checker": True,
        "general_affine_loop_candidate_equivalence_checker": "GuardMemoryExtractorProgress.checked_memory_loop_equivalence",
        "general_affine_loop_progress_theorem": "GuardMemoryExtractorProgress.validated_memory_affine_loops_at",
        "general_loop_endpoint_preserves_exact_entry_parameters_and_mem": True,
        "general_loop_endpoint_is_complete_c_source_decoder": False,
        "external_scheduler_connected": False,
        "different_array_layout_copy_c_bridge_proved": True,
        "different_array_layout_guard_machine_encoding_proved": True,
        "different_array_layout_source_scope": "one signed-int copy between named arrays with independently fixed extents and strides, including same-array remapping with equal extents, parametric affine inner bound, and conservative common row/column guard",
        "same_array_different_stride_copy_registry_proved": True,
        "same_array_copy_actual_dependence_validation_proved": True,
        "parametric_source_body_semantic_interface_instantiated": True,
        "heterogeneous_layout_operation_list_c_bridge_proved": True,
        "anchored_nonzero_affine_c_accesses_proved": True,
        "affine_multi_read_value_computations_proved": True,
        "affine_multi_read_value_computations_scope": "finite signed Int.add/sub/mul expressions over constants, row/column values and affine array reads; source-used read slots only; concrete load/store with source-anchored object bases and checked finite common domain",
        "anchored_nonzero_affine_c_accesses_scope": "nonnegative constant offsets and aggregate coefficients, checked common domain, source-proved zero-address anchors covering every requested actual array object",
        "zero_origin_affine_c_accesses_proved": True,
        "zero_origin_affine_c_accesses_scope": "signed affine expressions over both loop indices, zero constant coefficient, nonnegative aggregate coefficients and independently checked finite common domain; affine copies may mix with existing recognized layout operations",
        "heterogeneous_layout_operation_list_scope": "parameterized affine inner bound, arbitrary finite list of recognized named writes/updates or independent-layout copies, compatible repeated array extents, and checked common domain",
        "candidate_interval_condition_search_verified": True,
        "candidate_condition_search_scope": "default parameter box then outer-count upper caps 8,4,3,2,1; same candidate independently revalidated for each box; affine mapped candidates, generated schedules and two-dimensional tiling",
        "parametric_affine_inner_c_bound_decoded": True,
        "affine_bound_eager_reads_and_machine_encoding_proved": True,
        "affine_parameter_guard_short_circuit_safety_proved": True,
        "affine_bound_endpoint_condition_synthesis_proved": True,
        "affine_inner_bound_tiling_csem_asm_proved": True,
        "parametric_c_source_scope": "signed affine inner upper bounds, zero initial counters, named fixed-layout arrays and existing mixed statements; first row nonempty and all rows within layout required for fast path",
        "sources": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                    for path in sources},
        "upstream_profile": "build/polcert-optimizer-report.json",
        "upstream_proof_dependencies_rebuilt_in_this_audit": False,
    }
    (ROOT / "build" / "guard-memory-proof-report.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"Concrete Mem INSTR compiled: physical nonalias closed, {len(names(instruction))} inherited "
          f"instruction, {len(names(adapted))} unchanged validator and {len(names(compiler))} "
          "CompCert/validator union compiler assumptions")


if __name__ == "__main__":
    main()
