"""Publish the source-header license evidence and its uninstalled boundary."""

import argparse
import json

import audit_original_matmul_header_license as audit
from audit_interface_clight import ROOT, sha

SUMMARY = ROOT / "docs/original-matmul-header-license.json"


def payload():
    proof = audit.validate()
    return {
        "status": "audited_actual_source_conditional_header_licenses_not_installed_capture",
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
        "actual_original_selected_region_connected": proof["actual_original_selected_region_exact"],
        "read_permission_source": "finite normal execution of the actual original region",
        "header_load_or_numeric_range_premises": False,
        "license_memory": "original region entry memory",
        "conditional_read_dependencies": "M; signed M>0 licenses N; signed M,N>0 licenses K",
        "static_bindings_and_finite_normal_execution_still_required": True,
        "runtime_source_preexecution_required": False,
        "scope": "signed I64 header observations without a nonnegative bound premise",
        "new_capture_or_emitted_guard": False, "numeric_range_acceptance_complete": False,
        "checked_state_transport_complete": False, "fixed_parameter_candidate_bridge_complete": False,
        "total_progress_or_divergence_proved": False,
        "new_Csem_to_Asm_endpoint": False, "new_native_optimized_case": False,
        "original_corpus_requested_optimized_cases": 0, "cost_or_profitability_evidence": False,
        "full_goal_complete": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    summary = payload()
    if args.validate:
        if json.loads(SUMMARY.read_text()) != summary:
            raise ValueError("Summary differs from bound proof receipts")
    else:
        if SUMMARY.exists():
            raise ValueError("Summary already exists")
        SUMMARY.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({"status": "validated" if args.validate else "summarized",
                      "endpoints": summary["endpoints"], "summary_sha256": sha(SUMMARY)}))


if __name__ == "__main__":
    main()
