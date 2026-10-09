"""Publish or validate the original-matmul three-loop correspondence summary."""

import argparse
import json

import audit_original_matmul_nest as audit
from audit_interface_clight import ROOT, sha

SUMMARY = ROOT / "docs/original-matmul-full-nest.json"


def payload():
    report = audit.validate()
    proof = audit.WORK / "report.json"
    ast = audit.AST / "report.json"
    return {
        "status": "audited_full_finite_source_model_bridge_not_installed_optimization",
        "narrative_reference": "8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9",
        "source": "build/benchmark-alignment/probe-v1/matmul/marked.c",
        "source_adaptation": "existing scop markers only; original double computation, nested arrays and I64 controls retained",
        "actual_selected_region_exact": True,
        "proof_report": {"path": str(proof.relative_to(ROOT)), "sha256": sha(proof)},
        "source_nest_report": {"path": str(ast.relative_to(ROOT)), "sha256": sha(ast)},
        "new_modules": report["new_modules"], "new_source_lines": report["new_source_lines"],
        "endpoint_count": len(report["endpoints"]), "closed_endpoints": report["closed_endpoints"],
        "maximum_endpoint_globals": report["maximum_endpoint_globals"],
        "inherited_globals_union": sorted(set().union(*map(set, report["endpoint_assumptions"].values()))),
        "additional_global_axioms": report["additional_global_axioms"],
        "reachable_source_count": report["reachable_source_count"], "bound_files": len(report["bindings"]),
        "successful_attempts": sum(item["compiled"] for item in report["attempts"]),
        "rejected_attempts": sum(not item["compiled"] for item in report["attempts"]),
        "complete_three_loop_source_model_correspondence": True,
        "execution_directions": "both finite execution directions, under static and conditional entry premises",
        "final_memory_and_all_temporary_exits_exact": True,
        "outer_zero_trip": "only i is set to zero; original j and k, including absent values, are retained",
        "middle_zero_trip": "i ends at M and j at zero; original k is retained",
        "active_middle_exit": "i=M, j=N, k=K; includes K=0 initialization and break",
        "header_premises": ["M load at entry", "N load only if M positive", "K load only if M and N positive"],
        "header_stability": "all original C actions preserve M/N/K loads by global block separation",
        "per_assignment_entry": "derived from static facts, reached coordinates and loop invariants",
        "scope": "nonnegative signed-I64 bounds with padding/address limits; finite executions, no total progress or divergence theorem",
        "kernel_or_existing_host_changed": False, "additional_optimizer_IR": False,
        "source_user_premises_automatically_produced": False, "conditional_capture_or_runtime_guard_installed": False,
        "actual_double_scheduler_or_candidate_lowering_installed": False, "new_selected_Csem_to_Asm_endpoint": False,
        "new_native_optimized_case": False, "original_corpus_requested_optimized_cases": 0,
        "cost_or_profitability_evidence": False,
        "pending": ["source/site metadata producer and safely licensed conditional bound capture/guard",
                    "negative bound paths and broader affine/statement/value families",
                    "actual typed scheduling/tiling/codegen and candidate Clight lowering",
                    "candidate entry/public exits, progress and selected Csem-to-Asm installation",
                    "native acceptance/fallback, whole contexts and complete costs",
                    "remaining original PolCert/CGO17 programs and sequential configurations"],
        "full_goal_complete": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    summary = payload()
    if args.validate:
        if json.loads(SUMMARY.read_text()) != summary:
            raise ValueError("Documentation differs from frozen full-nest proof")
    else:
        if SUMMARY.exists():
            raise ValueError("Summary already exists")
        SUMMARY.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({"status": "validated" if args.validate else "summarized",
                      "endpoints": summary["endpoint_count"], "bound_files": summary["bound_files"],
                      "summary_sha256": sha(SUMMARY)}))


if __name__ == "__main__":
    main()
