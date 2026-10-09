"""Publish the actual-source double prepared-pipeline proof and native probe boundary."""

import argparse
import json

import audit_original_matmul_prepared as audit
import verify_original_matmul_prepared as native
from audit_interface_clight import ROOT, sha

SUMMARY = ROOT / "docs/original-matmul-prepared-pipeline.json"


def payload():
    proof = audit.validate()
    runs = native.validate()
    return {
        "status": "audited_real_double_prepared_pipeline_not_installed_C_optimization",
        "proof_report": {"path": str((audit.WORK / "report.json").relative_to(ROOT)), "sha256": sha(audit.WORK / "report.json")},
        "source_report": {"path": str((audit.AST / "report.json").relative_to(ROOT)), "sha256": sha(audit.AST / "report.json")},
        "native_report": {"path": str((native.WORK / "report.json").relative_to(ROOT)), "sha256": sha(native.WORK / "report.json")},
        "new_modules": proof["new_modules"], "new_source_lines": proof["new_source_lines"],
        "endpoints": len(proof["endpoints"]), "closed_endpoints": proof["closed_endpoints"],
        "maximum_endpoint_globals": proof["maximum_endpoint_globals"],
        "additional_global_axioms": proof["additional_global_axioms"],
        "reachable_sources": proof["reachable_source_count"], "proof_bindings": len(proof["bindings"]),
        "successful_proof_attempts": sum(a["compiled"] for a in proof["attempts"]),
        "rejected_proof_attempts": sum(not a["compiled"] for a in proof["attempts"]),
        "native_runs": len(runs["runs"]), "native_bindings": len(runs["bindings"]),
        "native_pipeline_results": {run["mode"]: run["result"]["status"] for run in runs["runs"] if "result" in run},
        "actual_original_selected_source_supplies_exportable_input": True,
        "parameter_context": "K,N,M; model execution environment M,N,K",
        "real_affine_schedule": "i/j/k -> i/k/j",
        "original_double_instruction_tree_retained": True,
        "prepared_codegen_direction": "generated wrapped Loop execution to source wrapped Loop execution",
        "fixed_parameter_source_candidate_execution_bridge_complete": False,
        "prior_dense_array_probe_transport_failure_reproduced": True,
        "current_exporter_double_bit_literals_supported": False,
        "safe_runtime_guard_and_entry_producer_installed": False,
        "candidate_Clight_lowering_installed": False,
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
            raise ValueError("Summary differs from bound proof and native receipts")
    else:
        if SUMMARY.exists():
            raise ValueError("Summary already exists")
        SUMMARY.write_text(json.dumps(summary, indent=2)+"\n")
    print(json.dumps({"status": "validated" if args.validate else "summarized",
                      "endpoints": summary["endpoints"], "native_runs": summary["native_runs"],
                      "summary_sha256": sha(SUMMARY)}))


if __name__ == "__main__":
    main()
