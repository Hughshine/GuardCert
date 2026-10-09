"""Publish or validate correspondence with the typed pipeline Loop instance."""

import argparse
import json

import audit_original_matmul_pipeline_loop as audit
from audit_interface_clight import ROOT, sha

SUMMARY = ROOT / "docs/original-matmul-pipeline-loop.json"


def payload():
    report = audit.validate()
    return {
        "status": "audited_actual_pipeline_Loop_source_bridge_not_installed_optimization",
        "proof_report": {"path": str((audit.WORK / "report.json").relative_to(ROOT)), "sha256": sha(audit.WORK / "report.json")},
        "source_report": {"path": str((audit.AST / "report.json").relative_to(ROOT)), "sha256": sha(audit.AST / "report.json")},
        "new_modules": report["new_modules"], "new_source_lines": report["new_source_lines"],
        "endpoints": len(report["endpoints"]), "closed_endpoints": report["closed_endpoints"],
        "maximum_endpoint_globals": report["maximum_endpoint_globals"],
        "additional_global_axioms": report["additional_global_axioms"],
        "reachable_sources": report["reachable_source_count"], "bindings": len(report["bindings"]),
        "successful_attempts": sum(a["compiled"] for a in report["attempts"]),
        "rejected_attempts": sum(not a["compiled"] for a in report["attempts"]),
        "generative_AST_type_rejection_reproduced_and_bound": True,
        "actual_POLIRS_Loop_constructors_used": True, "execution_correspondence": "both finite directions",
        "actual_original_selected_region_connected": True,
        "instruction_and_state_kept": "same strict double instruction, CompCert memory and registry",
        "new_external_scheduler_call_or_candidate_lowering": False,
        "safe_runtime_guard_and_entry_producer_installed": False,
        "new_Csem_to_Asm_endpoint": False, "new_native_optimized_case": False,
        "original_corpus_requested_optimized_cases": 0, "full_goal_complete": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    summary = payload()
    if args.validate:
        if json.loads(SUMMARY.read_text()) != summary:
            raise ValueError("Pipeline Loop summary differs from frozen proof")
    else:
        if SUMMARY.exists():
            raise ValueError("Summary already exists")
        SUMMARY.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({"status": "validated" if args.validate else "summarized", "endpoints": summary["endpoints"],
                      "bindings": summary["bindings"], "summary_sha256": sha(SUMMARY)}))


if __name__ == "__main__":
    main()
