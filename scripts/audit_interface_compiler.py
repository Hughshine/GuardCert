"""Audit the new read-only API's connection to the existing CompCert region host."""
import json
import subprocess
from pathlib import Path

from audit_compiler import names
from audit_interface_clight import ROOT, sha, compcert_flags

WORK = ROOT / "build/interface-compiler"
MODULES = ["ClightReadonlyCompiler", "ClightReadonlyLoopRule", "ClightPreloadCompiler", "ClightReadonlyMatrix", "ClightReadonlyRectangle",
           "ClightReadonlyLoopUpdates", "ClightRectangleAssumptions", "ClightReadonlyCellSwap", "ClightCellFrame",
           "ClightReadonlyProjectedCompiler", "ClightPrivateCandidateCompiler",
           "ClightCountedLocalization", "ClightStableLoadBody", "ClightStableLoadGuard",
           "ClightReadonlyProjectedLoopRule", "ClightStableLoadLoop", "ClightStableLoadCompiler",
           "ClightStrictLoopProgress", "ClightStableLoopCondition", "ClightReadonlyLoadedTreeSynthesis",
           "ClightLoadedBoundSyntax", "ClightLoadedBoundGuard", "ClightLoadedBoundLoop", "ClightLoadedBoundCompiler",
           "ClightReadonlyRuleEmbedding", "ClightLoopBodyTransport", "ClightRuntimeStrideBody",
           "ClightRuntimeStrideLoops", "ClightRuntimeStrideEntry", "ClightRuntimeStrideGuard",
           "ClightRuntimeStrideCompiler", "ClightIndexedLoadBody", "ClightIndexedLoadDomain",
           "ClightIndexedAliasGuard", "ClightIndexedLoadLoop", "ClightIndexedLoadCompiler",
           "ClightIndexedBoundSyntax", "ClightStrictIteration", "ClightIndexedBoundPrefix", "ClightIndexedBoundScan",
           "ClightActiveLoopCondition", "ClightIndexedBoundGuard", "ClightIndexedBoundLoop", "ClightIndexedBoundCompiler",
           "ClightCounterProgress", "ClightCounterCondition", "ClightCircularCounter", "ClightEqualityLoop",
           "ClightEqualityCompiler", "ClightReadonlyExpression", "ClightReadonlyTestSyntax", "ClightReadonlyTestProof",
           "ClightReadonlyTestCompiler", "ClightEqualityHead", "ClightEqualityHeadCompiler", "ClightCommonRewriteCompiler"]
ENDPOINTS = {
    "ClightReadonlyExpression.readonly_expression_host": "FRAGMENT",
    "ClightReadonlyExpression.fragment_condition_for_expression": "FRAGMENT",
    "ClightReadonlyExpression.readonly_expression_contract": "FRAGMENT",
    "ClightReadonlyTestSyntax.transform_statement_matches": "FRAGMENT",
    "ClightReadonlyTestProof.step_simulation": "STEPWISE",
    "ClightReadonlyTestProof.transform_program_correct": "STEPWISE",
    "ClightReadonlyTestProof.transform_program_correct2": "STEPWISE",
    "ClightReadonlyTestCompiler.readonly_test_selection_sound": "FRAGMENT",
    "ClightReadonlyTestCompiler.compile_readonly_tests_correct": "COMPILER",
    "ClightReadonlyTestCompiler.compile_readonly_tests_after_correct": "COMPILER",
    "ClightEqualityHead.equality_head_guard_run": "FRAGMENT",
    "ClightEqualityHead.equality_head_condition": "FRAGMENT",
    "ClightEqualityHead.equality_head_local": "FRAGMENT",
    "ClightEqualityHead.equality_head_rule": "FRAGMENT",
    "ClightEqualityHeadCompiler.choose_equality_head": "FRAGMENT",
    "ClightEqualityHeadCompiler.compile_equality_heads_correct": "COMPILER",
    "ClightCounterProgress.generic_step_closed": "REGION",
    "ClightCounterProgress.generic_region_completed": "REGION",
    "ClightCounterProgress.generic_frontend_progress": "REGION",
    "ClightCounterCondition.generic_active_condition_transport": "FRAGMENT",
    "ClightCircularCounter.cyclic_distance_nonnegative": "FRAGMENT",
    "ClightCircularCounter.cyclic_distance_positive": "FRAGMENT",
    "ClightCircularCounter.unsigned_increment_value": "FRAGMENT",
    "ClightCircularCounter.cyclic_distance_decreases": "FRAGMENT",
    "ClightCircularCounter.circular_counter_facts": "FRAGMENT",
    "ClightCircularCounter.unsigned_equality_test_facts": "FRAGMENT",
    "ClightCircularCounter.unsigned_order_test_eval": "FRAGMENT",
    "ClightCircularCounter.unsigned_increment_execution_exact": "FRAGMENT",
    "ClightCircularCounter.unsigned_equality_progress": "REGION",
    "ClightEqualityLoop.equality_guard_run": "FRAGMENT",
    "ClightEqualityLoop.equality_condition": "FRAGMENT",
    "ClightEqualityLoop.equality_header_transport": "FRAGMENT",
    "ClightEqualityLoop.equality_domain_from_source": "FRAGMENT",
    "ClightEqualityLoop.equality_loop_forward": "FRAGMENT",
    "ClightEqualityCompiler.equality_loop_supported_sound": "REGION",
    "ClightEqualityCompiler.equality_progress_supported_sound": "REGION",
    "ClightEqualityCompiler.equality_loop_rule": "FRAGMENT",
    "ClightEqualityCompiler.choose_equality_loop": "FRAGMENT",
    "ClightEqualityCompiler.compile_equality_loops_correct": "COMPILER",
    "ClightReadonlyLoopRule.readonly_forward_loop_rule": "FRAGMENT",
    "ClightReadonlyCompiler.readonly_rule_fragment_contract": "FRAGMENT",
    "ClightReadonlyCompiler.readonly_rule_region_contract": "REGION",
    "ClightReadonlyCompiler.readonly_selection_sound": "REGION",
    "ClightReadonlyCompiler.compile_readonly_rewrites_correct": "COMPILER",
    "ClightPreloadCompiler.preload_branch_rule": "FRAGMENT",
    "ClightPreloadCompiler.choose_preload_rewrite": "FRAGMENT",
    "ClightPreloadCompiler.trim_readonly_rule": "FRAGMENT",
    "ClightPreloadCompiler.compile_preload_rewrites_correct": "COMPILER",
    "ClightReadonlyMatrix.readonly_matrix_condition": "FRAGMENT",
    "ClightReadonlyMatrix.readonly_matrix_forward": "MEMORY_FRAGMENT",
    "ClightReadonlyMatrix.readonly_matrix_rule": "MEMORY_FRAGMENT",
    "ClightReadonlyMatrix.compile_readonly_matrix_correct": "COMPILER",
    "ClightReadonlyRectangle.readonly_rectangle_condition": "FRAGMENT",
    "ClightReadonlyRectangle.readonly_rectangle_forward": "MEMORY_FRAGMENT",
    "ClightReadonlyRectangle.readonly_rectangle_rule": "MEMORY_FRAGMENT",
    "ClightReadonlyRectangle.compile_readonly_rectangle_correct": "COMPILER",
    "ClightReadonlyLoopUpdates.readonly_rectangle_layout_condition": "FRAGMENT",
    "ClightReadonlyLoopUpdates.readonly_rectangle_update_forward": "MEMORY_FRAGMENT",
    "ClightReadonlyLoopUpdates.readonly_rectangle_update_rule": "MEMORY_FRAGMENT",
    "ClightReadonlyLoopUpdates.readonly_rectangle_row_update_forward": "MEMORY_FRAGMENT",
    "ClightReadonlyLoopUpdates.readonly_rectangle_row_update_rule": "MEMORY_FRAGMENT",
    "ClightReadonlyLoopUpdates.compile_readonly_rectangles_correct": "COMPILER",
    "ClightRectangleAssumptions.rectangle_text_derivation": "FRAGMENT",
    "ClightRectangleAssumptions.accepted_rectangle_text_requirements": "FRAGMENT",
    "ClightRectangleAssumptions.accepted_rectangle_address_injective": "FRAGMENT",
    "ClightRectangleAssumptions.collected_rectangle_machine_index": "FRAGMENT",
    "ClightReadonlyCellSwap.cell_pair_condition": "FRAGMENT",
    "ClightReadonlyCellSwap.known_cell_alias_negation": "FRAGMENT",
    "ClightReadonlyCellSwap.distinct_aligned_words_disjoint": "FRAGMENT",
    "ClightReadonlyCellSwap.cell_pair_source_domain": "FRAGMENT",
    "ClightReadonlyCellSwap.cell_pair_forward": "MEMORY_FRAGMENT",
    "ClightReadonlyCellSwap.cell_pair_rule": "MEMORY_FRAGMENT",
    "ClightReadonlyCellSwap.compile_readonly_cell_pairs_correct": "COMPILER",
    "ClightCellFrame.cell_pair_write_frame": "FRAGMENT",
    "ClightCellFrame.cell_pair_stable_parameters": "FRAGMENT",
    "ClightReadonlyProjectedCompiler.projected_readonly_rule_region_contract": "FRAGMENT",
    "ClightReadonlyProjectedCompiler.projected_readonly_selection_sound": "FRAGMENT",
    "ClightReadonlyProjectedCompiler.transform_projected_readonly_correct": "PROJECTED_REGION",
    "ClightReadonlyProjectedCompiler.compile_projected_readonly_correct": "COMPILER",
    "ClightPrivateCandidateCompiler.private_candidate_rule": "FRAGMENT",
    "ClightPrivateCandidateCompiler.choose_private_candidate": "FRAGMENT",
    "ClightPrivateCandidateCompiler.compile_private_candidate_correct": "COMPILER",
    "ClightCountedLocalization.counted_body_decode": "FRAGMENT",
    "ClightCountedLocalization.counted_body_encode": "FRAGMENT",
    "ClightStableLoadBody.mint32_load_survives_apart_store": "FRAGMENT",
    "ClightStableLoadBody.stable_load_body_cached": "FRAGMENT",
    "ClightStableLoadBody.stable_load_body_preserves_parameter": "FRAGMENT",
    "ClightStableLoadGuard.stable_load_condition": "FRAGMENT",
    "ClightStableLoadGuard.stable_load_domain_from_source": "FRAGMENT",
    "ClightReadonlyProjectedLoopRule.readonly_projected_forward_loop_rule": "FRAGMENT",
    "ClightStableLoadLoop.stable_iterations_cached": "FRAGMENT",
    "ClightStableLoadLoop.stable_load_forward": "FRAGMENT",
    "ClightStableLoadCompiler.stable_load_rule": "FRAGMENT",
    "ClightStableLoadCompiler.choose_stable_load": "FRAGMENT",
    "ClightStableLoadCompiler.compile_stable_loads_correct": "COMPILER",
    "ClightStrictLoopProgress.strict_increment_distance": "FRAGMENT",
    "ClightStrictLoopProgress.strict_step_closed": "FRAGMENT",
    "ClightStrictLoopProgress.strict_region_cannot_diverge": "FRAGMENT",
    "ClightStrictLoopProgress.strict_frontend_progress": "FRAGMENT",
    "ClightStableLoopCondition.strict_loop_condition_transport": "FRAGMENT",
    "ClightStableLoopCondition.strict_header_execution": "FRAGMENT",
    "ClightStableLoopCondition.flatten_statement_temps": "FRAGMENT",
    "ClightReadonlyLoadedTreeSynthesis.readonly_decision_run_safe": "FRAGMENT",
    "ClightReadonlyLoadedTreeSynthesis.synthesized_loaded_tree_condition": "FRAGMENT",
    "ClightReadonlyLoadedTreeSynthesis.positive_readonly_tree_primitives": "FRAGMENT",
    "ClightLoadedBoundSyntax.loaded_bound_test_strict": "FRAGMENT",
    "ClightLoadedBoundSyntax.loaded_bound_cached_test": "FRAGMENT",
    "ClightLoadedBoundSyntax.loaded_bound_body_preserves": "FRAGMENT",
    "ClightLoadedBoundGuard.loaded_bound_condition": "FRAGMENT",
    "ClightLoadedBoundGuard.loaded_bound_domain_from_source": "FRAGMENT",
    "ClightLoadedBoundGuard.loaded_bound_tail_run": "FRAGMENT",
    "ClightLoadedBoundGuard.loaded_bound_tail_condition": "FRAGMENT",
    "ClightLoadedBoundLoop.loaded_bound_loop_cached": "FRAGMENT",
    "ClightLoadedBoundLoop.loaded_bound_forward": "FRAGMENT",
    "ClightLoadedBoundCompiler.loaded_bound_supported_sound": "FRAGMENT",
    "ClightLoadedBoundCompiler.loaded_bound_rule": "FRAGMENT",
    "ClightLoadedBoundCompiler.choose_loaded_bound": "FRAGMENT",
    "ClightLoadedBoundCompiler.compile_loaded_bounds_correct": "COMPILER",
    "ClightReadonlyRuleEmbedding.exact_clight_local_observed": "FRAGMENT",
    "ClightReadonlyRuleEmbedding.exact_readonly_as_projected": "FRAGMENT",
    "ClightReadonlyRuleEmbedding.exact_projected_replacement": "FRAGMENT",
    "ClightReadonlyRuleEmbedding.quiet_source_write_bound": "FRAGMENT",
    "ClightLoopBodyTransport.strict_loop_body_transport": "FRAGMENT",
    "ClightRuntimeStrideBody.runtime_stride_index_constant": "FRAGMENT",
    "ClightRuntimeStrideBody.runtime_stride_lvalue_constant": "FRAGMENT",
    "ClightRuntimeStrideBody.runtime_stride_store_constant": "FRAGMENT",
    "ClightRuntimeStrideBody.runtime_stride_lvalue_domain": "FRAGMENT",
    "ClightRuntimeStrideLoops.counted_body_transport_fixed": "FRAGMENT",
    "ClightRuntimeStrideLoops.runtime_inner_constant": "FRAGMENT",
    "ClightRuntimeStrideLoops.constant_inner_runtime": "FRAGMENT",
    "ClightRuntimeStrideLoops.runtime_rectangle_constant": "FRAGMENT",
    "ClightRuntimeStrideLoops.constant_interchanged_runtime": "FRAGMENT",
    "ClightRuntimeStrideLoops.runtime_stride_rectangle_forward": "MEMORY_FRAGMENT",
    "ClightRuntimeStrideEntry.runtime_stride_domain_from_source": "FRAGMENT",
    "ClightRuntimeStrideGuard.stride_wide_product_exact": "FRAGMENT",
    "ClightRuntimeStrideGuard.stride_dimensions_condition": "FRAGMENT",
    "ClightRuntimeStrideGuard.stride_dimensions_sound": "FRAGMENT",
    "ClightRuntimeStrideCompiler.stride_runtime_layout": "FRAGMENT",
    "ClightRuntimeStrideCompiler.stride_forward": "MEMORY_FRAGMENT",
    "ClightRuntimeStrideCompiler.stride_rule": "MEMORY_FRAGMENT",
    "ClightRuntimeStrideCompiler.choose_runtime_stride": "MEMORY_FRAGMENT",
    "ClightRuntimeStrideCompiler.compile_runtime_strides_correct": "COMPILER",
    "ClightIndexedLoadBody.indexed_pointer_evaluation": "FRAGMENT",
    "ClightIndexedLoadBody.indexed_pointer_inverse": "FRAGMENT",
    "ClightIndexedLoadBody.indexed_load_body_facts": "FRAGMENT",
    "ClightIndexedLoadBody.indexed_load_body_cached": "FRAGMENT",
    "ClightIndexedLoadBody.indexed_load_body_preserves_parameter": "FRAGMENT",
    "ClightIndexedLoadDomain.indexed_iterations_writable": "FRAGMENT",
    "ClightIndexedLoadDomain.indexed_load_domain_from_source": "FRAGMENT",
    "ClightIndexedAliasGuard.indexed_alias_apart": "FRAGMENT",
    "ClightIndexedAliasGuard.indexed_alias_scan_run": "FRAGMENT",
    "ClightIndexedAliasGuard.indexed_alias_scan_sound": "FRAGMENT",
    "ClightIndexedAliasGuard.indexed_guard_condition": "FRAGMENT",
    "ClightIndexedAliasGuard.indexed_guard_sound": "FRAGMENT",
    "ClightIndexedLoadLoop.indexed_iterations_cached": "FRAGMENT",
    "ClightIndexedLoadLoop.indexed_load_forward": "FRAGMENT",
    "ClightIndexedLoadCompiler.indexed_load_rule": "FRAGMENT",
    "ClightIndexedLoadCompiler.choose_indexed_load": "FRAGMENT",
    "ClightIndexedLoadCompiler.compile_indexed_loads_correct": "COMPILER",
    "ClightIndexedBoundSyntax.indexed_bound_test_strict": "FRAGMENT",
    "ClightIndexedBoundSyntax.indexed_bound_body_store": "FRAGMENT",
    "ClightStrictIteration.strict_active_iteration": "FRAGMENT",
    "ClightStrictIteration.strict_increment_execution_exact": "FRAGMENT",
    "ClightIndexedBoundPrefix.indexed_bound_source_step": "FRAGMENT",
    "ClightIndexedBoundScan.indexed_bound_alias_scan_run": "FRAGMENT",
    "ClightIndexedBoundScan.indexed_bound_alias_scan_sound": "FRAGMENT",
    "ClightActiveLoopCondition.strict_active_condition_transport": "FRAGMENT",
    "ClightIndexedBoundGuard.indexed_bound_guard_run": "FRAGMENT",
    "ClightIndexedBoundGuard.indexed_bound_guard_sound": "FRAGMENT",
    "ClightIndexedBoundGuard.indexed_bound_condition": "FRAGMENT",
    "ClightIndexedBoundGuard.indexed_bound_domain_from_source": "FRAGMENT",
    "ClightIndexedBoundLoop.indexed_bound_loop_cached": "FRAGMENT",
    "ClightIndexedBoundLoop.indexed_bound_forward": "FRAGMENT",
    "ClightIndexedBoundCompiler.indexed_bound_supported_sound": "FRAGMENT",
    "ClightIndexedBoundCompiler.indexed_bound_progress_supported_sound": "FRAGMENT",
    "ClightIndexedBoundCompiler.indexed_bound_rule": "FRAGMENT",
    "ClightIndexedBoundCompiler.choose_indexed_bound": "FRAGMENT",
    "ClightIndexedBoundCompiler.compile_indexed_bounds_correct": "COMPILER",
    "ClightCommonRewriteCompiler.choose_common_rewrite": "MEMORY_FRAGMENT",
    "ClightCommonRewriteCompiler.compile_common_rewrites_correct": "COMPILER",
}
BASELINES = {
    "FRAGMENT": "ClightCondition.fragment_language",
    "MEMORY": "Mem.mkmem_ext",
    "REGION": "ClightRegionRewrite.guarded_fragment_region_contract",
    "PROJECTED_REGION": "ClightPrivatePool.transform_private_program_correct",
    "STEPWISE": "ClightTreeRewriteProof.transform_program_correct",
    "COMPILER": "Compiler.transf_c_program_correct",
}


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    prerequisite = ROOT / "build/interface-clight/report.json"
    report = json.loads(prerequisite.read_text())
    for path, digest in report["sources"].items():
        if sha(ROOT / path) != digest:
            raise SystemExit(f"Clight interface changed: {path}; run make interface-clight-proof")
    inherited = json.loads((ROOT / "build/compcert-guardcert/.guard-build.json").read_text())["proof_sources"]
    for path, digest in inherited.items():
        if sha(ROOT / path) != digest:
            raise SystemExit(f"Compiler dependency changed: {path}")
    flags = compcert_flags()
    sections = []
    for module in MODULES:
        result = subprocess.run(["rocq", "compile", *flags, f"prototype/interface/{module}.v"],
                                cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        sections.append(f"Compiling {module}\n{result.stdout}")
        (WORK / "proof.log").write_text("\n".join(sections))
        if result.returncode:
            raise SystemExit(f"Compiler interface failed: {module}; see {WORK / 'proof.log'}")
        print(f"Compiled {module}", flush=True)
    audit = WORK / "Audit.v"
    lines = ["From compcert.driver Require Import Compiler.",
             "From compcert.common Require Import Memory.",
             "From Guard Require Import ClightCondition ClightRegionRewrite ClightPrivatePool.",
             "From GuardInterface Require Import " + " ".join(MODULES) + "."]
    queries = {**BASELINES, **{f"CHECK_{i}": theorem for i, theorem in enumerate(ENDPOINTS)}}
    for marker, theorem in queries.items():
        lines += [f'Goal True. idtac "{marker}". exact I. Qed.', f"Print Assumptions {theorem}."]
    lines += ['Goal True. idtac "END". exact I. Qed.']
    audit.write_text("\n".join(lines) + "\n")
    result = subprocess.run(["rocq", "compile", *flags, str(audit)], cwd=ROOT,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (WORK / "assumptions.log").write_text(result.stdout)
    if result.returncode:
        raise SystemExit("Compiler assumption audit failed")
    markers = [*queries, "END"]
    sections = {marker: names(result.stdout.split(marker + "\n", 1)[1].split(markers[i+1] + "\n", 1)[0])
                for i, marker in enumerate(markers[:-1])}
    # Equality of concrete CompCert memories reuses the upstream record
    # extensionality lemma, whose proof uses CompCert's proof irrelevance.
    sections["MEMORY_FRAGMENT"] = sections["FRAGMENT"] | sections["MEMORY"]
    checked = {}
    for i, (theorem, level) in enumerate(ENDPOINTS.items()):
        extra = sections[f"CHECK_{i}"] - sections[level]
        if extra:
            raise SystemExit(f"Additional assumptions at {theorem}: {sorted(extra)}")
        checked[theorem] = {"baseline": level, "assumptions": sorted(sections[f"CHECK_{i}"])}
    sources = {**inherited, **report["sources"]}
    sources.update({f"prototype/interface/{m}.v": sha(ROOT / f"prototype/interface/{m}.v") for m in MODULES})
    sources.update(json.loads((ROOT / "build/interface/report.json").read_text())["sources"])
    output = {
        "status": "compiled", "sources": sources,
        "prerequisite_clight_report_sha256": sha(prerequisite),
        "baseline_assumptions": {level: sorted(sections[level]) for level in [*BASELINES, "MEMORY_FRAGMENT"]},
        "endpoint_assumptions": checked, "additional_global_axioms": [],
        "whole_program_entrypoint": "ClightPreloadCompiler.compile_preload_rewrites",
        "whole_program_theorem": "ClightPreloadCompiler.compile_preload_rewrites_correct",
        "whole_program_entrypoints": {
            "preload": "ClightPreloadCompiler.compile_preload_rewrites",
            "matrix": "ClightReadonlyMatrix.compile_readonly_matrix",
            "rectangle": "ClightReadonlyRectangle.compile_readonly_rectangle",
            "cells": "ClightReadonlyCellSwap.compile_readonly_cell_pairs",
            "loops": "ClightReadonlyLoopUpdates.compile_readonly_rectangles",
            "private_candidate": "ClightPrivateCandidateCompiler.compile_private_candidate",
            "stable_load": "ClightStableLoadCompiler.compile_stable_loads",
            "loaded_bound": "ClightLoadedBoundCompiler.compile_loaded_bounds",
            "common": "ClightCommonRewriteCompiler.compile_common_rewrites",
            "runtime_stride": "ClightRuntimeStrideCompiler.compile_runtime_strides",
            "indexed_load": "ClightIndexedLoadCompiler.compile_indexed_loads",
            "indexed_bound": "ClightIndexedBoundCompiler.compile_indexed_bounds",
            "equality": "ClightEqualityCompiler.compile_equality_loops",
            "equality_head": "ClightEqualityHeadCompiler.compile_equality_heads",
        },
        "user_supplied_selection_supported": True,
        "new_readonly_api_consumed_by_compiler": True,
        "clight_whole_program_equivalence_proved": False,
        "csem_to_asm_backward_simulation_proved": True,
        "boundary_mode": "exact raw exits, or projected exits protecting every original program temporary",
        "exact_adapter_private_temporary_projection_supported": False,
        "private_temporary_projection_supported": True,
        "projected_context_adapter_proved": True,
        "private_candidate_uses_projected_adapter": True,
        "stable_load_hoisting_uses_projected_adapter": True,
        "guarded_loop_parameter_load_stability_proved": True,
        "guarded_memory_loaded_loop_bound_supported": True,
        "memory_bound_source_progress_independent_of_load_stability": True,
        "readonly_formula_tree_atoms_may_contain_ordinary_loads": True,
        "memory_bound_rule_consumes_language_independent_condition_composition": True,
        "exact_rules_embed_without_changing_generated_code": True,
        "common_user_pass_combines_exact_and_projected_rules": True,
        "runtime_stride_rectangular_interchange_supported": True,
        "runtime_stride_guard_product_proved_exact_in_signed_64_bits": True,
        "runtime_stride_domain_preserves_lazy_source_parameter_reads": True,
        "bounded_indexed_loop_write_footprint_checked_by_readonly_guard": True,
        "indexed_parameter_stability_derived_after_active_address_non_alias_checks": True,
        "indexed_memory_bound_stability_checked_by_prefix_safe_readonly_scan": True,
        "indexed_memory_bound_guard_safety_does_not_assume_complete_entry_footprint": True,
        "active_loop_body_certificate_receives_true_source_header": True,
        "generic_counter_protocol_accepts_a_rank_update_and_active_condition_certificate": True,
        "unsigned_equality_loop_progress_uses_cyclic_distance_not_a_no_wrap_assumption": True,
        "guarded_fixed_bound_unsigned_equality_exit_to_ordered_exit_supported": True,
        "selected_potentially_diverging_equality_loop_supported": False,
        "readonly_expression_contract_consumes_the_shared_guarded_rewrite_core": True,
        "stepwise_loop_header_rewrite_supported_inside_potentially_diverging_loops": True,
        "stepwise_loop_header_host_requires_no_enclosing_source_termination_certificate": True,
        "common_user_pass_composes_projected_region_and_readonly_expression_passes": True,
        "projected_adapter_protects_all_original_program_temporaries": True,
        "fixed_2x2_loop_interchange_uses_new_api": True,
        "dynamic_rectangle_store_interchange_uses_new_api": True,
        "dynamic_rectangle_read_modify_write_and_row_dependency_use_new_api": True,
        "dynamic_rectangle_guard_certifies_registered_control_and_address_requirements": True,
        "two_aligned_word_stores_have_readonly_non_alias_guard": True,
        "general_loop_transformation_migrated": False,
        "native_execution_run": False,
    }
    (WORK / "report.json").write_text(json.dumps(output, indent=2) + "\n")
    print(f"Read-only compiler audited: {len(ENDPOINTS)} endpoints; inherited baselines "
          + ", ".join(f"{level}={len(sections[level])}" for level in BASELINES))


if __name__ == "__main__":
    main()
