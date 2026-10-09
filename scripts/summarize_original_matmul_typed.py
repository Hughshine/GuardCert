"""Publish or validate the audited original-matmul bridge summary."""

import argparse
import json

import audit_original_matmul_typed as audit
from audit_interface_clight import ROOT, sha

SUMMARY = ROOT / "docs/original-matmul-typed-bridge.json"


def payload():
    report = audit.validate()
    proof = audit.WORK / "report.json"
    ast = audit.AST / "report.json"
    frontend = ROOT / "build/original-matmul/frontend-v1/report.json"
    return {
        "status": "audited_local_progress_not_installed_optimization",
        "narrative_reference": "8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9",
        "source": "build/benchmark-alignment/probe-v1/matmul/marked.c",
        "source_adaptation": "existing scop markers only; original computation, double/global arrays and I64 controls retained",
        "exported_AST_adaptation": "Rocq import namespaces only",
        "proof_report": {"path": str(proof.relative_to(ROOT)), "sha256": sha(proof)},
        "source_AST_report": {"path": str(ast.relative_to(ROOT)), "sha256": sha(ast)},
        "frontend_report": {"path": str(frontend.relative_to(ROOT)), "sha256": sha(frontend)},
        "new_modules": report["new_modules"], "new_source_lines": report["new_source_lines"],
        "endpoint_count": len(report["endpoints"]), "closed_endpoints": report["closed_endpoints"],
        "maximum_endpoint_globals": report["maximum_endpoint_globals"],
        "inherited_globals_union": sorted(set().union(*map(set, report["endpoint_assumptions"].values()))),
        "additional_global_axioms": report["additional_global_axioms"],
        "reachable_source_count": report["reachable_source_count"], "bound_files": len(report["bindings"]),
        "new_proof_successful_attempts": sum(item["compiled"] for item in report["attempts"]),
        "new_proof_rejected_attempts": sum(not item["compiled"] for item in report["attempts"]),
        "source_AST_import_namespace_rejection_preserved": True,
        "actual_source_selected_region_and_assignment_exact": True,
        "decoder_executed_on_actual_original_RHS": True,
        "local_execution_directions": ["original assignment to memory action", "memory action to lowered assignment",
                                       "memory action to and from concrete PolCert INSTR and body Loop"],
        "local_entry_premises": "global bindings, temp/control values, shifted index bounds, address span, layout lookup",
        "partial_reads": "successful original assignment licenses its RHS reads; address receipts assume no load",
        "strict_assignment": "only Vfloat can be a successful double assignment value",
        "IEEE_reassociation_or_FMA_licensed": False,
        "I64_point_expressions_and_tests_proved": True,
        "typed_polyhedral_validator_extractor_and_prepared_codegen_instantiated": True,
        "typed_codegen_direction": "generated Loop to source model; progress and target lowering remain separate",
        "source_user_entry_premises_automatically_produced": False,
        "kernel_or_existing_host_changed": False,
        "whole_loop_or_Mfloat64_guard_or_selected_factory_installed": False,
        "new_native_optimized_case": False, "original_corpus_requested_optimized_cases": 0,
        "new_Csem_to_Asm_optimization_endpoint": False, "cost_or_profitability_evidence": False,
        "pending": ["complete original I64 nest to Loop correspondence and partial bound/capture producer",
                    "actual typed scheduling/tiling and candidate lowering",
                    "safe runtime guard, source-derived entry premises and exact public exits",
                    "selected factory and Csem-to-Asm installation, native acceptance/fallback and full cost",
                    "remaining 62-case sequential configurations and original CGO17 programs"],
        "full_goal_complete": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    summary = payload()
    if args.validate:
        if json.loads(SUMMARY.read_text()) != summary:
            raise ValueError("Documentation summary differs from frozen proof checkpoint")
    else:
        if SUMMARY.exists():
            raise ValueError("Summary already exists")
        SUMMARY.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({"status": "validated" if args.validate else "summarized",
                      "endpoints": summary["endpoint_count"], "bound_files": summary["bound_files"],
                      "summary_sha256": sha(SUMMARY)}))


if __name__ == "__main__":
    main()
