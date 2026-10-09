"""Bind the quotient installation proof without importing preceding native results."""
import argparse
import json
from pathlib import Path

import audit_quotient_double_tiled_installation as proof
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

OUTPUT = ROOT / "docs/quotient-parameter-installation.json"


def summarize():
    report = proof.validate()
    if (report["new_source_lines"] != 884 or len(report["endpoints"]) != 15
            or report["closed_endpoints"] != 3
            or report["maximum_endpoint_globals"] != 42
            or report["kernel_changed"] or report["new_host_contract"]
            or report["source_user_supplies_semantic_callbacks"]
            or report["semantic_compiler_proof_unchanged"]
            or report["native_or_cost_evidence_added_by_audit"]):
        raise ValueError("Changed quotient proof or delivery scope")
    bindings = dict(report["bindings"])
    for path in [proof.WORK / "report.json", Path(__file__)]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    return {"status": "validated", "date": "2026-10-09",
            "narrative_reference": "8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9",
            "delivery_scope": "compiled model, Clight execution, factory and Csem-to-Asm proofs",
            "report": str((proof.WORK / "report.json").relative_to(ROOT)),
            "report_sha256": sha(permitted(proof.WORK / "report.json")),
            "new_modules": report["new_modules"], "new_source_lines": report["new_source_lines"],
            "whole_program_entrypoint": report["whole_program_entrypoint"],
            "whole_program_theorem": report["whole_program_theorem"],
            "queried_endpoints": report["endpoints"],
            "endpoint_assumptions": report["endpoint_assumptions"],
            "closed_endpoints": report["closed_endpoints"],
            "maximum_endpoint_globals": report["maximum_endpoint_globals"],
            "reachable_source_count": report["reachable_source_count"],
            "additional_global_axioms": [],
            "kernel_changed": False, "new_host_contract": False,
            "semantic_compiler_proof_unchanged": False,
            "source_user_supplies_semantic_callbacks": False,
            "parameter_extension_preserves_actual_Loop_execution": True,
            "quotient_relation_consumed_by_final_actual_candidate_validation": True,
            "actual_safe_capture_and_candidate_lowering_proved": True,
            "public_exits_original_fallback_and_current_program_installation_proved": True,
            "prior_passes_consume_actual_intermediate_program": True,
            "new_native_compiler_built": False, "new_native_or_context_runs": False,
            "new_runtime_cost_measured": False,
            "prior_native_results_are_not_relabelled_as_quotient_results": True,
            "proof_attempts": report["attempts"],
            "next_required_work": ["extract a compiler that proposes dynamic quotient tile bounds",
                                   "run original cases, refusal, context and actual dispatch checks",
                                   "measure complete costs and continue broader sequential/OLO coverage"],
            "full_goal_complete": False, "bindings": bindings}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    result = summarize()
    if args.validate:
        if json.loads(permitted(OUTPUT).read_text()) != result:
            raise ValueError("Changed quotient proof summary")
    else:
        with permitted(OUTPUT).open("x") as target:
            target.write(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": "validated", "source_lines": result["new_source_lines"],
                      "endpoints": len(result["queried_endpoints"]),
                      "bindings": len(result["bindings"]), "sha256": sha(permitted(OUTPUT))}))


if __name__ == "__main__":
    main()
