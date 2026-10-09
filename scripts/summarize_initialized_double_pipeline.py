"""Summarize frozen actual-source entry and real initialized-loop pipeline evidence."""

import argparse
import json

import audit_initialized_double_pipeline as initial
import audit_initialized_double_uniform_pipeline as uniform
import validate_initialized_double_pipeline as native
from audit_interface_clight import ROOT, sha

SUMMARY = ROOT / "docs/initialized-double-pipeline.json"


def snapshot():
    first, last, runs = initial.validate(), uniform.validate(), native.validate()
    reports = [initial.WORK / "report.json", uniform.WORK / "report.json", native.WORK / "report.json"]
    return {"status": "validated", "kind": "actual-initialized-source-safe-entry-and-real-pipeline",
            "actual_original_cases": ["mxv", "matmul-init"],
            "new_modules": first["new_modules"] + last["new_modules"],
            "source_lines": first["new_source_lines"] + last["new_source_lines"],
            "audited_endpoints": len(first["endpoints"]) + len(last["endpoints"]),
            "closed_endpoints": first["closed_endpoints"] + last["closed_endpoints"],
            "maximum_endpoint_globals": max(first["maximum_endpoint_globals"], last["maximum_endpoint_globals"]),
            "additional_global_axioms": [], "reachable_sources": last["reachable_source_count"],
            "generic_library_attempts": {"successful": 5, "failed": 6},
            "actual_wrapper_attempts": {"successful": 3, "failed": 2, "interrupted": 2},
            "reports": [{"path": str(path.relative_to(ROOT)), "sha256": sha(path),
                         "bound_files": len(report["bindings"])} for path, report in zip(reports, [first, last, runs])],
            "structural_transport_between_existing_Loop_instances": True,
            "safe_header_capture_contract_from_original_finite_normal_execution": True,
            "accepted_capture_produces_count_and_point_resolution": True,
            "accepted_and_refused_capture_preserve_public_source_execution": True,
            "original_IEEE_instructions_retained_by_actual_model_import_and_codegen": True,
            "uniform_scattering_coordinates_support_mixed_statement_depths": True,
            "actual_parameter_count_used_for_schedule_import": True,
            "runtime_read_license_assumes_source_is_preexecuted": False,
            "all_arbitrary_entry_states_or_divergence_safety_proved": False,
            "condition": {"family": "single global I64 header; private I32 cache and Boolean flag",
                          "accepted_range": [0, 98], "actual_extent": 100, "source_padding": 2,
                          "numeric_entry_premises_supplied_by_C_user": False,
                          "actual_scope_and_private_allocation_still_need_factory_receipts": True},
            "native": {"checks": len(runs["checks"]), "accepted": runs["accepted_final_candidates"],
                       "refused": runs["refused_candidates"], "timeouts": runs["timed_out_attempts"],
                       "changes": {"mxv": "initialization/reduction fission",
                                   "matmul-init": "initialization/reduction fission and i/k/j reduction order"},
                       "checks_by_stage": [{key: item[key] for key in ["case", "mode", "swap_witness", "stage"]}
                                           for item in runs["checks"]],
                       "failed_builds_preserved": 2,
                       "previous_diagnostic_refusals": 4, "previous_diagnostic_interruptions": 1,
                       "executes_C_or_assembly": False,
                       "guard_or_optimized_program_cost_measured": False},
            "candidate_lowering_public_exit_restore_and_scoped_Csem_installation_added": False,
            "new_installed_original_corpus_cases": 0, "original_corpus_nonidentity_optimized_cases": 1,
            "original_corpus_total_cases": 62, "kernel_or_language_host_changed": False,
            "full_goal_complete": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    result = snapshot()
    if args.validate:
        if json.loads(SUMMARY.read_text()) != result:
            raise ValueError("Summary differs from frozen evidence")
    else:
        SUMMARY.open("x").write(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"status": "validated", "source_lines": result["source_lines"],
                      "endpoints": result["audited_endpoints"], "native_checks": result["native"]["checks"],
                      "summary_sha256": sha(SUMMARY)}))


if __name__ == "__main__":
    main()
