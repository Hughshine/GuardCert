"""Publish bound actual matmul capture/source-model evidence with its installation boundary."""

import argparse
import json

import audit_original_matmul_capture as audit
import verify_original_matmul_capture as native
from audit_interface_clight import ROOT, sha

SUMMARY = ROOT / "docs/original-matmul-capture.json"


def receipt(path):
    return {"path": str(path.relative_to(ROOT)), "sha256": sha(path)}


def payload():
    proof = audit.validate()
    runs = native.validate()
    return {
        "status": "audited_actual_conditional_capture_to_fixed_source_model_not_installed_candidate",
        "narrative_reference": "8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9",
        "proof_report": receipt(audit.WORK / "report.json"),
        "source_report": receipt(audit.AST / "report.json"),
        "native_report": receipt(native.WORK / "report.json"),
        "new_modules": proof["new_modules"], "new_source_lines": proof["new_source_lines"],
        "endpoints": len(proof["endpoints"]), "closed_endpoints": proof["closed_endpoints"],
        "maximum_endpoint_globals": proof["maximum_endpoint_globals"],
        "additional_global_axioms": proof["additional_global_axioms"],
        "reachable_sources": proof["reachable_source_count"], "proof_bindings": len(proof["bindings"]),
        "successful_proof_attempts": sum(a["compiled"] for a in proof["attempts"]),
        "rejected_proof_attempts": sum(not a["compiled"] for a in proof["attempts"]),
        "actual_original_selected_region_connected": proof["actual_original_selected_region_exact"],
        "read_permission_source": "finite normal execution of the actual original region",
        "header_load_or_numeric_range_premises": False,
        "runtime_source_preexecution_required": False,
        "conditional_capture_Clight_execution_proved": proof["conditional_capture_Clight_execution_proved"],
        "all_completed_capture_executions_sound": proof["all_completed_capture_executions_sound"],
        "I64_checks_precede_exact_I32_conversion": proof["I64_checks_precede_exact_I32_conversion"],
        "numeric_limit": proof["numeric_capture_limit_original_case"],
        "empty_path_private_parameters_filled_without_child_reads": proof[
            "empty_path_private_parameters_filled_without_child_reads"],
        "fresh_capture_resources_checked_from_actual_program": proof[
            "fresh_capture_resources_checked_from_actual_program"],
        "E0_memory_and_public_temp_frame_proved": proof["E0_memory_and_public_temp_frame_proved"],
        "original_fallback_entry_and_source_exit_transport_proved": proof[
            "original_fallback_entry_and_source_exit_transport_proved"],
        "source_model_at_actual_captured_parameters": proof["source_model_at_actual_captured_parameters"],
        "static_layout_bindings_and_finite_source_execution_still_required": True,
        "successful_capture_native_runs": runs["successful_capture_runs"],
        "accepted_native_runs": sum(r.get("result", {}).get("accepted", False) for r in runs["runs"]),
        "refused_native_runs": sum("result" in r and not r["result"]["accepted"] for r in runs["runs"]),
        "expected_outside_license_failures": runs["expected_outside_license_failures"],
        "native_bindings": len(runs["bindings"]),
        "native_boundary": "actual extracted capture AST and CompCert Cop/Mem operations; probe supplies global lookup and an unproved AST interpreter",
        "native_source_candidate_fallback_or_Asm_execution": runs[
            "source_candidate_fallback_or_Asm_execution"],
        "fixed_parameter_generated_candidate_bridge_complete": False,
        "total_source_or_candidate_progress_proved": False,
        "selected_compiler_connected": False, "new_Csem_to_Asm_endpoint": False,
        "original_corpus_requested_optimized_cases": 0,
        "cost_or_profitability_evidence": False, "full_goal_complete": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    summary = payload()
    if args.validate:
        if json.loads(SUMMARY.read_text()) != summary:
            raise ValueError("Summary differs from bound capture receipts")
    else:
        if SUMMARY.exists():
            raise ValueError("Summary already exists")
        SUMMARY.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({"status": "validated" if args.validate else "summarized",
                      "endpoints": summary["endpoints"], "summary_sha256": sha(SUMMARY)}))


if __name__ == "__main__":
    main()
