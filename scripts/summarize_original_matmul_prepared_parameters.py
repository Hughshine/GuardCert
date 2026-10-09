"""Publish fixed-parameter generated-to-source evidence and the remaining installation obligations."""

import argparse
import json

import audit_original_matmul_prepared_parameters as audit
from audit_interface_clight import ROOT, sha

SUMMARY = ROOT / "docs/original-matmul-prepared-parameters.json"


def payload():
    proof = audit.validate()
    return {
        "status": "audited_same_captured_parameter_generated_backward_source_not_installed_candidate",
        "narrative_reference": "8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9",
        "proof_report": {"path": str((audit.WORK / "report.json").relative_to(ROOT)),
                         "sha256": sha(audit.WORK / "report.json")},
        "source_report": {"path": str((audit.AST / "report.json").relative_to(ROOT)),
                          "sha256": sha(audit.AST / "report.json")},
        "new_modules": proof["new_modules"], "new_source_lines": proof["new_source_lines"],
        "endpoints": len(proof["endpoints"]), "closed_endpoints": proof["closed_endpoints"],
        "maximum_endpoint_globals": proof["maximum_endpoint_globals"],
        "additional_global_axioms": proof["additional_global_axioms"],
        "reachable_sources": proof["reachable_source_count"], "proof_bindings": len(proof["bindings"]),
        "successful_proof_attempts": sum(a["compiled"] for a in proof["attempts"]),
        "rejected_proof_attempts": sum(not a["compiled"] for a in proof["attempts"]),
        "generic_POLIRS_fixed_parameter_composition": True,
        "source_and_target_parameter_environment": "the same actual captured [M;N;K]; named polyhedral environment is its reverse",
        "parameter_context_preserved_by_validation": True,
        "raw_codegen_and_actual_cleanup_connected": True,
        "actual_checked_double_pipeline_consumed": True,
        "actual_capture_to_generated_backward_source_bridge": True,
        "original_source_fallback_and_public_exits_connected": True,
        "header_load_or_numeric_range_premises": False,
        "static_layout_bindings_and_finite_normal_source_execution_still_required": True,
        "proof_direction": proof["proof_direction"],
        "original_optimizer_and_kernel_unchanged": True,
        "candidate_Clight_lowering_complete": False, "candidate_forward_progress_proved": False,
        "source_total_progress_or_divergence_proved": False,
        "selected_compiler_connected": False, "new_Csem_to_Asm_endpoint": False,
        "new_native_or_cost_results": False, "original_corpus_requested_optimized_cases": 0,
        "full_goal_complete": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    summary = payload()
    if args.validate:
        if json.loads(SUMMARY.read_text()) != summary:
            raise ValueError("Summary differs from bound fixed-parameter receipts")
    else:
        if SUMMARY.exists():
            raise ValueError("Summary already exists")
        SUMMARY.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({"status": "validated" if args.validate else "summarized",
                      "endpoints": summary["endpoints"], "summary_sha256": sha(SUMMARY)}))


if __name__ == "__main__":
    main()
