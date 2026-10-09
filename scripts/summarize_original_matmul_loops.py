"""Publish or validate the original-matmul inner-loop checkpoint summary."""

import argparse
import json

import audit_original_matmul_loops as audit
from audit_interface_clight import ROOT, sha

SUMMARY = ROOT / "docs/original-matmul-inner-loop.json"


def payload():
    report = audit.validate()
    proof = audit.WORK / "report.json"
    ast = audit.AST / "report.json"
    return {
        "status": "audited_finite_inner_loop_bridge_not_installed_optimization",
        "narrative_reference": "8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9",
        "source": "build/benchmark-alignment/probe-v1/matmul/marked.c",
        "source_adaptation": "existing scop markers only; original double computation, arrays and I64 controls retained",
        "actual_source_AST": "reuses frozen exported complete program and verifies selected inner-loop identity",
        "proof_report": {"path": str(proof.relative_to(ROOT)), "sha256": sha(proof)},
        "source_loop_report": {"path": str(ast.relative_to(ROOT)), "sha256": sha(ast)},
        "new_modules": report["new_modules"], "new_source_lines": report["new_source_lines"],
        "endpoint_count": len(report["endpoints"]), "closed_endpoints": report["closed_endpoints"],
        "maximum_endpoint_globals": report["maximum_endpoint_globals"],
        "inherited_globals_union": sorted(set().union(*map(set, report["endpoint_assumptions"].values()))),
        "additional_global_axioms": report["additional_global_axioms"],
        "reachable_source_count": report["reachable_source_count"], "bound_files": len(report["bindings"]),
        "successful_attempts": sum(item["compiled"] for item in report["attempts"]),
        "rejected_attempts": sum(not item["compiled"] for item in report["attempts"]),
        "execution_directions": ["actual initialized k loop to and from finite physical memory iterations",
                                 "physical iterations to and from typed PolCert inner Loop"],
        "public_exit": "all temporaries retained, except k set exactly to the nonnegative I64 upper bound",
        "invariant_producer": "static global/layout facts and loop invariant produce each reached assignment entry",
        "loaded_header_stability": "writes to C preserve K by global symbol/block separation",
        "conditional_reads": "body reads come from actual assignment execution; no speculative body preload",
        "entry_header_load_and_range": "explicit logical premises, not automatically produced runtime checks",
        "finite_scope": "nonnegative signed-I64 upper bound; no total progress or divergence theorem added",
        "kernel_or_existing_host_changed": False,
        "complete_three_loop_nest": False, "conditional_bound_capture_installed": False,
        "new_emitted_runtime_guard": False, "actual_double_scheduler_or_candidate_lowering_installed": False,
        "source_user_premises_automatically_produced": False, "new_selected_Csem_to_Asm_endpoint": False,
        "new_native_optimized_case": False, "original_corpus_requested_optimized_cases": 0,
        "cost_or_profitability_evidence": False,
        "pending": ["outer i/j loops, conditional M/N/K observation and full public exits",
                    "actual typed scheduling/tiling/codegen and candidate lowering",
                    "safe guard and checked source/site premise producer",
                    "selected Csem-to-Asm installation, native acceptance/fallback and complete costs",
                    "remaining original PolCert/CGO17 cases and sequential configurations"],
        "full_goal_complete": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    summary = payload()
    if args.validate:
        if json.loads(SUMMARY.read_text()) != summary:
            raise ValueError("Documentation differs from frozen loop proof checkpoint")
    else:
        if SUMMARY.exists():
            raise ValueError("Summary already exists")
        SUMMARY.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({"status": "validated" if args.validate else "summarized",
                      "endpoints": summary["endpoint_count"], "bound_files": summary["bound_files"],
                      "summary_sha256": sha(SUMMARY)}))


if __name__ == "__main__":
    main()
