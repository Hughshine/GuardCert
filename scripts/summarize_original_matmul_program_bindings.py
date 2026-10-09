"""Publish the checked actual-program facts and scoped host proof boundary."""

import argparse
import json

import audit_original_matmul_program_bindings as audit
from audit_interface_clight import ROOT, sha

SUMMARY = ROOT / "docs/original-matmul-program-bindings.json"


def payload():
    proof = audit.validate()
    return {
        "status": "audited_actual_program_static_producer_and_scoped_contract_not_installed_matmul_compiler",
        "narrative_reference": "8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9",
        "proof_report": {"path": str((audit.WORK / "report.json").relative_to(ROOT)),
                         "sha256": sha(audit.WORK / "report.json")},
        "new_modules": proof["new_modules"], "new_source_lines": proof["new_source_lines"],
        "endpoints": len(proof["endpoints"]), "closed_endpoints": proof["closed_endpoints"],
        "maximum_endpoint_globals": proof["maximum_endpoint_globals"],
        "additional_global_axioms": proof["additional_global_axioms"],
        "reachable_sources": proof["reachable_source_count"], "proof_bindings": len(proof["bindings"]),
        "successful_proof_attempts": sum(a["compiled"] for a in proof["attempts"]),
        "rejected_proof_attempts": sum(not a["compiled"] for a in proof["attempts"]),
        "typed_global_declaration_and_no_shadow_checkers": True,
        "actual_program_scope_invariant_preserved_by_all_Clight_steps": True,
        "scoped_host_forward_simulation_proved": True,
        "old_universal_contract_admitted_by_scoped_contract": True,
        "original_private_region_AST_transform_reused": True,
        "actual_matmul_static_and_header_bindings_produced": True,
        "actual_matmul_scoped_region_contract_proved": True,
        "declarations_imply_memory_read_permissions": False,
        "static_global_bindings_still_supplied_by_source_user": False,
        "program_preservation_and_no_shadow_guarantees_supplied_by_language_host": True,
        "source_execution_not_runtime_preexecution": True,
        "finite_normal_source_execution_and_actual_pipeline_lowering_receipts_still_required": True,
        "generic_kernel_changed": False,
        "language_host_contract_successor_added": True,
        "source_total_progress_or_divergence_proved": False,
        "actual_matmul_host_installation_complete": False,
        "selected_compiler_connected": False,
        "new_Csem_to_Asm_endpoint": False,
        "new_native_or_cost_results": False,
        "original_corpus_requested_optimized_cases": 0,
        "full_goal_complete": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    summary = payload()
    if args.validate:
        if json.loads(SUMMARY.read_text()) != summary:
            raise ValueError("Summary differs from actual program proof receipts")
    else:
        if SUMMARY.exists():
            raise ValueError("Summary already exists")
        SUMMARY.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({"status": "validated" if args.validate else "summarized",
                      "endpoints": summary["endpoints"], "summary_sha256": sha(SUMMARY)}))


if __name__ == "__main__":
    main()
