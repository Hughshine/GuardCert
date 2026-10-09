"""Publish the actual guarded double Clight proof and native AST-emission evidence."""

import argparse
import json

import audit_original_matmul_double_lowering as audit
import verify_original_matmul_double_lowering as native
from audit_interface_clight import ROOT, sha

SUMMARY = ROOT / "docs/original-matmul-double-lowering.json"


def payload():
    proof = audit.validate()
    runs = native.validate()
    return {
        "status": "audited_actual_guarded_double_Clight_finite_execution_not_whole_program_installed",
        "narrative_reference": "8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9",
        "proof_report": {"path": str((audit.WORK / "report.json").relative_to(ROOT)),
                         "sha256": sha(audit.WORK / "report.json")},
        "source_report": {"path": str((audit.AST / "report.json").relative_to(ROOT)),
                          "sha256": sha(audit.AST / "report.json")},
        "native_report": {"path": str((native.WORK / "report.json").relative_to(ROOT)),
                          "sha256": sha(native.WORK / "report.json")},
        "new_modules": proof["new_modules"], "new_source_lines": proof["new_source_lines"],
        "endpoints": len(proof["endpoints"]), "closed_endpoints": proof["closed_endpoints"],
        "maximum_endpoint_globals": proof["maximum_endpoint_globals"],
        "additional_global_axioms": proof["additional_global_axioms"],
        "reachable_sources": proof["reachable_source_count"], "proof_bindings": len(proof["bindings"]),
        "successful_proof_attempts": sum(a["compiled"] for a in proof["attempts"]),
        "rejected_proof_attempts": sum(not a["compiled"] for a in proof["attempts"]),
        "native_bindings": len(runs["bindings"]), "native_checks": len(runs["runs"]),
        "ranged_I32_operands_and_exact_I64_casts": True,
        "arbitrary_rank_global_double_tensor_backend": True,
        "original_IEEE_operation_tree_and_I64_public_exits_preserved": True,
        "source_and_target_parameter_environment": "the same actual captured [M;N;K]",
        "actual_final_generated_body_checked_and_lowered": True,
        "actual_capture_candidate_exit_and_original_fallback_execution": True,
        "original_source_fallback_runs_from_actual_checked_state": True,
        "header_load_or_numeric_range_premises": False,
        "static_layout_bindings_and_finite_normal_source_execution_still_required": True,
        "proof_direction": proof["proof_direction"],
        "original_optimizer_and_kernel_unchanged": True,
        "candidate_Clight_lowering_complete": True, "candidate_model_forward_progress_proved": True,
        "source_total_progress_or_divergence_proved": False,
        "selected_compiler_connected": False, "new_Csem_to_Asm_endpoint": False,
        "native_candidate_and_guarded_Clight_ASTs_emitted": True,
        "native_Clight_statement_or_C_Asm_execution": False,
        "new_cost_results": False, "original_corpus_requested_optimized_cases": 0,
        "full_goal_complete": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    summary = payload()
    if args.validate:
        if json.loads(SUMMARY.read_text()) != summary:
            raise ValueError("Summary differs from actual Clight receipts")
    else:
        if SUMMARY.exists():
            raise ValueError("Summary already exists")
        SUMMARY.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({"status": "validated" if args.validate else "summarized",
                      "endpoints": summary["endpoints"], "summary_sha256": sha(SUMMARY)}))


if __name__ == "__main__":
    main()
