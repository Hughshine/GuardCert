"""Bind actual quotient installations, context evidence and complete-call costs."""
import argparse
import json
from pathlib import Path
import re

import audit_partitioned_quotient_compiler as proof
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked
from summarize_pruned_double_tiling import corpus_summary, complete_cost

OUTPUT = ROOT / "docs/quotient-double-tiling.json"
REPORTS = {
    "preceding_proof_checkpoint": "docs/quotient-parameter-installation.json",
    "proof": "build/quotient-double-tiling/partitioned-proof-v1/report.json",
    "first_compiler": "build/quotient-double-tiling/compiler-attempts/native-v1/report.json",
    "preflight_rejection": "build/quotient-double-tiling/compiler-preflight/native-v2/rejection.json",
    "cyclic_extraction_rejection": "build/quotient-double-tiling/compiler-attempts/native-v3/rejection.json",
    "traced_compiler": "build/quotient-double-tiling/compiler-attempts/native-v4/report.json",
    "compiler": "build/quotient-double-tiling/compiler-attempts/native-v5/report.json",
    "first_profile": "build/benchmark-alignment/adaptive-tiled-attempts/quotient-focused-v1/report.json",
    "traced_profile": "build/benchmark-alignment/adaptive-tiled-attempts/quotient-trace-v4/report.json",
    "partitioned_profile": "build/benchmark-alignment/adaptive-tiled-attempts/quotient-partition-focused-v5/report.json",
    "corpus": "build/benchmark-alignment/adaptive-tiled-attempts/quotient-full-corpus-v5/report.json",
    "point_contexts": "build/quotient-double-tiling/context-attempts/quotient-contexts-v5/report.json",
    "reduction_contexts": "build/quotient-double-tiling/reduction-context-attempts/quotient-reduction-contexts-v5/report.json",
    "initialized_contexts": "build/initialized-double-tiling/check-attempts/quotient-initialized-contexts-v5/report.json",
    "public_and_legacy": "build/initialized-double-tiling/public-attempts/quotient-public-v5/report.json",
    "paths": "build/quotient-double-tiling/path-attempts/quotient-paths-v5/report.json",
    "unit_observer_rejection": "build/quotient-double-tiling/unit-matrix-attempts/quotient-unit-matrix-v5/report.json",
    "unit_receipts": "build/quotient-double-tiling/unit-receipt-attempts/quotient-unit-receipts-v5/report.json",
    "cost": "build/pruned-double-tiling/cost-attempts/quotient-cost-v5/report.json",
}
EXPECTED = {name: ("validated" if name == "preceding_proof_checkpoint" else
                  "compiled" if name == "proof" else
                  "rejected" if name.endswith("rejection") else
                  "built" if name.endswith("compiler") else
                  "diagnostic_complete" if name.endswith("profile") or name == "corpus" else
                  "measured" if name == "cost" else "passed") for name in REPORTS}


def summarize():
    certificate = proof.validate()
    if (certificate["new_source_lines"] != 1093 or len(certificate["endpoints"]) != 21
            or certificate["closed_endpoints"] != 3 or certificate["maximum_endpoint_globals"] != 42
            or certificate["additional_global_axioms"]):
        raise ValueError("Changed quotient proof scope")
    bindings = dict(certificate["bindings"])
    reports = {name: checked(permitted(ROOT / path), bindings) for name, path in REPORTS.items()}
    if any(reports[name]["status"] != EXPECTED[name] for name in REPORTS):
        raise ValueError("Unexpected report status")
    build = reports["compiler"]
    if (build["whole_program_entrypoint"] != proof.ENTRY
            or build["actual_source_Csem_to_Asm_theorem"] != proof.ENTRY + "_correct"
            or build["additional_global_axioms"]
            or not all(build[key] for key in ["actual_safe_quotient_capture_extracted",
                "fallback_phase_resolver_reads_actual_intermediate_program",
                "no_history_dependent_phase_suppression_required",
                "affine_quotient_relation_consumed_by_final_validation",
                "verified_membership_constructors_extracted_and_called"])
            or build["semantic_compiler_proof_unchanged"]):
        raise ValueError("Changed actual program entrypoint or safe capture integration")
    corpus = corpus_summary(reports["corpus"])
    work = (ROOT / REPORTS["corpus"]).parent
    quotient, older, initialized = {}, {}, {}
    for row in reports["corpus"]["results"]:
        if row["variant"] != "original" or row["configurations"]["tile"]["status"] != "native_match":
            continue
        trace = permitted(work / (row["case"]+"-original/tile/compiler.stderr"))
        tags = re.findall(r"GUARDCERT_QUOTIENT_TILING_INSTALLED regions=(\d+) older_reduction_regions=(\d+) divisor=(\d+)", trace.read_text())
        if not tags or int(tags[-1][2]) != 32:
            raise ValueError("Missing current-build quotient observation")
        q, o, _ = map(int, tags[-1])
        init = row["configurations"]["tile"]["installed"][1]
        if q: quotient[row["case"]] = q
        if o: older[row["case"]] = o
        if init: initialized[row["case"]] = init
        if q + o + init != row["configurations"]["tile"]["installed"][2]:
            raise ValueError("Double-counted or unaccounted installation")
    if len(quotient) != 11 or sum(quotient.values()) != 27 or older or sum(initialized.values()) != 3:
        raise ValueError("Quotient and retained-route accounting changed")
    for name, count in [("point_contexts", 23), ("reduction_contexts", 14),
                        ("initialized_contexts", 20), ("public_and_legacy", 7),
                        ("paths", 6), ("unit_receipts", 10)]:
        rows = reports[name]["cases"]
        if len(rows) != count or not all(row["passed"] for row in rows):
            raise ValueError("Incomplete current-binary checks: " + name)
    if not reports["paths"]["actual_quotient_values_observed"] or not reports["paths"]["assembly_not_modified"]:
        raise ValueError("Actual unchanged-assembly dispatch observations required")
    directory, = sorted((work / "polynomial-original/tile").glob("tiling-pipeline-*"))
    receipt = permitted(directory / "quotient-parameter.txt").read_text()
    proposal = permitted(directory / "quotient-proposals.txt").read_text()
    generated = permitted(directory / "generated.loop").read_text()
    if (receipt != "divisor=32\nlayout=quotient,original-bound\nrelation=0<=d*q-n<=d-1\n"
            or "upper=(2*v0)" not in proposal or "upper=(1*v1)" not in proposal
            or "loop [0,(2*v0))" not in generated or "loop [0,(1*v1))" not in generated):
        raise ValueError("Actual quotient-dependent polynomial bounds required")
    cost = complete_cost(reports["cost"])
    for path in [Path(__file__), Path(proof.__file__), ROOT / "scripts/summarize_pruned_double_tiling.py"]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    return {"status": "validated", "date": "2026-10-09",
            "narrative_reference": "8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9",
            "whole_program_entrypoint": build["whole_program_entrypoint"],
            "whole_program_theorem": build["actual_source_Csem_to_Asm_theorem"],
            "compiler": build["compiler"], "compiler_sha256": build["compiler_sha256"],
            "reports": {name: {"path": path, "sha256": sha(permitted(ROOT / path)),
                               "status": reports[name]["status"]} for name, path in REPORTS.items()},
            "new_modules_since_pruned_checkpoint": certificate["new_modules"],
            "new_source_lines_since_pruned_checkpoint": certificate["new_source_lines"],
            "new_source_lines_since_proof_checkpoint": 209,
            "queried_endpoints": certificate["endpoints"],
            "endpoint_assumptions": certificate["endpoint_assumptions"],
            "closed_endpoints": 3, "maximum_endpoint_globals": 42,
            "additional_global_axioms": [], "kernel_changed": False, "host_laws_changed": False,
            "source_user_supplies_semantic_callbacks": False,
            "quotient_capture_and_relation_actually_consumed_by_compiler": True,
            "actual_runtime_dependent_quotient_tile_bounds_installed": True,
            "fallback_phase_policy_receives_actual_intermediate_program": True,
            "history_dependent_phase_suppression": False,
            "partition_policy_may_refuse_other_equal_source_models": True,
            "source_execution_is_runtime_preexecution": False,
            "native_versions_and_previous_results_not_relabelled": True,
            "first_observer_zero_was_not_quotient_validator_refusal": True,
            "unit_observer_failure_corrected_from_unchanged_successful_run_receipts": True,
            "corpus": corpus, "quotient_installed_original_cases": quotient,
            "quotient_installed_sites": sum(quotient.values()),
            "older_reduction_installed_original_cases": older,
            "retained_initialized_installed_original_cases": initialized,
            "source_coverage_expanded": False,
            "context_and_dispatch_checks_passed": 70, "unit_mask_configurations_passed": 10,
            "polynomial_parameters": {"divisor": 32, "model_environment": "[q,n]",
                "relation": "0 <= 32*q-n <= 31", "prefix_bounds": ["2*q", "q"]},
            "complete_call_cost": cost,
            "cost_acceptance_passed": cost["optimized_over_unmarked_complete_call_ratio"] < 1,
            "general_assumption_inference_or_general_guard_language_claimed": False,
            "broader_source_and_sequential_OLO_acceptance_complete": False,
            "next_required_work": ["extend actual source/configuration support using the 45 no-phase cases and tricky3",
                "reduce actual checking/point work and establish useful complete costs",
                "install remaining sequential transformations and original BT/LLVM/SPEC/larger tiers"],
            "full_goal_complete": False, "bindings": bindings}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    result = summarize()
    if args.validate:
        if json.loads(permitted(OUTPUT).read_text()) != result:
            raise ValueError("Changed native quotient summary")
    else:
        with permitted(OUTPUT).open("x") as target:
            target.write(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": "validated", "reports": len(REPORTS), "bindings": len(result["bindings"]),
                      "quotient_sites": result["quotient_installed_sites"],
                      "cost_ratio": result["complete_call_cost"]["optimized_over_unmarked_complete_call_ratio"],
                      "sha256": sha(permitted(OUTPUT))}))


if __name__ == "__main__":
    main()
