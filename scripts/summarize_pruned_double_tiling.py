"""Bind prefix pruning, actual verified condition consumption and complete costs."""
import argparse
import json
from pathlib import Path
import re

import audit_floor_membership_service as proof
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked
from summarize_initialized_double_tiling import schedules

OUTPUT = ROOT / "docs/pruned-double-tiling.json"
REPORTS = {
    "preceding_checkpoint": "docs/bounded-double-tiling.json",
    "first_compiler": "build/pruned-double-tiling/compiler-attempts/native-v1/report.json",
    "first_profile": "build/benchmark-alignment/adaptive-tiled-attempts/pruned-point-profile-v1/report.json",
    "unit_compiler": "build/pruned-double-tiling/compiler-attempts/native-v2/report.json",
    "unit_corpus": "build/benchmark-alignment/adaptive-tiled-attempts/pruned-point-corpus-v2/report.json",
    "unit_contexts": "build/bounded-double-tiling/context-attempts/pruned-contexts-v2/report.json",
    "first_mixed_rank3": "build/double-tiling/original-attempts/pruned-mixed-rank3-v2/report.json",
    "unit_cost": "build/pruned-double-tiling/cost-attempts/cost-v2/report.json",
    "proof": "build/pruned-double-tiling/floor-proof-v1/report.json",
    "build_rejection": "build/pruned-double-tiling/compiler-attempts/native-v3/rejection.json",
    "compiler": "build/pruned-double-tiling/compiler-attempts/native-v4/report.json",
    "corpus": "build/benchmark-alignment/adaptive-tiled-attempts/verified-prefix-corpus-v4/report.json",
    "unit_matrix": "build/pruned-double-tiling/unit-matrix-attempts/verified-prefix-v4/report.json",
    "contexts": "build/bounded-double-tiling/context-attempts/verified-prefix-contexts-v4/report.json",
    "reduction_contexts": "build/double-tiling/check-attempts/verified-prefix-contexts-v4/report.json",
    "initialized_contexts": "build/initialized-double-tiling/check-attempts/verified-prefix-contexts-v4/report.json",
    "public_and_legacy": "build/initialized-double-tiling/public-attempts/verified-prefix-public-v4/report.json",
    "paths": "build/pruned-double-tiling/path-attempts/verified-prefix-paths-v4/report.json",
    "cost": "build/pruned-double-tiling/cost-attempts/verified-prefix-cost-v4/report.json",
}


def corpus_summary(report):
    if (not report["full_corpus_attempted"] or report["original_cases_attempted"] != 62
            or len(report["results"]) != 64 or report["native_failures"]
            or report["private_count_override"] is not None or report["witness_axes_override"] is not None
            or report["phase_trace_requested"]):
        raise ValueError("A complete default-resource untraced replay is required")
    raw = {row["case"]: row["configurations"]["tile"] for row in report["results"]
           if row["variant"] == "original"}
    adapted = [row["configurations"]["tile"] for row in report["results"] if row["variant"] != "original"]
    installed = {case: row["installed"][2] for case, row in raw.items() if row["installed"] and row["installed"][2]}
    refusals = sorted(case for case, row in raw.items() if row["status"] == "frontend_or_compiler_refusal")
    no_phase = sum(row["status"] == "native_match" and not row["tiling_phase_calls"] for row in raw.values())
    phase_without_install = sorted(case for case, row in raw.items() if row["status"] == "native_match"
                                  and row["tiling_phase_calls"] and case not in installed)
    if (len(installed) != 14 or sum(installed.values()) != 30
            or sum(row["status"] == "native_match" for row in raw.values()) != 60
            or len(adapted) != 2 or not all(row["status"] == "native_match" for row in adapted)
            or refusals != ["corcol3", "pca"] or any(row["compiler"]["timeout"] for row in raw.values())
            or no_phase != 45 or phase_without_install != ["tricky3"]):
        raise ValueError("Corpus accounting changed")
    return {"originals": 62, "adaptations": 2, "raw_native_matches": 60,
            "adapted_native_matches": 2, "frontend_refusals": refusals, "compiler_timeouts": [],
            "installed_original_cases": installed, "installed_sites": sum(installed.values()),
            "compiled_originals_without_tiling_phase": no_phase,
            "compiled_originals_with_phase_without_installation": phase_without_install,
            "polynomial_compiler_wall_seconds": raw["polynomial"]["compiler"]["elapsed_seconds"],
            "tce_compiler_wall_seconds": raw["tce"]["compiler"]["elapsed_seconds"],
            "diagnostic_times_are_not_controlled_compile_time_comparisons": True}


def complete_cost(report):
    if (report["trials_per_variant"] != 7 or not report["all_outputs_match_original_GCC"]
            or not report["same_compiler_flags_and_toolchain"]
            or report["other_concurrent_goal_commands_running"]):
        raise ValueError("Same-compiler alternating complete costs are required")
    return {key: report[key] for key in ["trials_per_variant", "medians_seconds",
            "optimized_over_unmarked_complete_call_ratio", "measurement_scope", "guard_cost_isolated",
            "same_compiler_flags_and_toolchain", "other_concurrent_goal_commands_running",
            "cpu_affinity_or_host_load_controlled", "benchmark_wide_profitability_claimed"]}


def summarize():
    certificate = proof.validate()
    bindings = dict(certificate["bindings"])
    reports = {name: checked(permitted(ROOT / path), bindings) for name, path in REPORTS.items()}
    for name, report in reports.items():
        expected = ("validated" if name == "preceding_checkpoint" else "compiled" if name == "proof" else
                    "built" if name in {"first_compiler", "unit_compiler", "compiler"} else
                    "rejected" if name == "build_rejection" else
                    "diagnostic_complete" if name in {"first_profile", "unit_corpus", "corpus"} else
                    "measured" if name in {"unit_cost", "cost"} else "passed")
        if report["status"] != expected:
            raise ValueError("Changed report status: " + name)
    build = reports["compiler"]
    if (build["whole_program_entrypoint"] != proof.ENTRY or not build["semantic_compiler_proof_unchanged"]
            or not build["verified_membership_constructors_extracted_and_called"]
            or not build["floor_membership_math_and_machine_service_audited"]
            or build["additional_global_axioms"] or build["new_runtime_dependent_loop_bounds"]):
        raise ValueError("Changed semantic compiler or condition-service boundary")
    corpus = corpus_summary(reports["corpus"])
    first_corpus = corpus_summary(reports["unit_corpus"])
    for name, count in [("unit_contexts", 20), ("contexts", 20), ("reduction_contexts", 14),
                        ("initialized_contexts", 20), ("public_and_legacy", 7), ("paths", 3)]:
        if len(reports[name]["cases"]) != count or not all(row["passed"] for row in reports[name]["cases"]):
            raise ValueError("Incomplete context/path replay: " + name)
    matrix = reports["unit_matrix"]["cases"]
    if len(matrix) != 10 or not all(row["passed"] and row["installed_phase_calls_adaptations"][0] == 2 for row in matrix):
        raise ValueError("Incomplete canonical unit-mask replay")
    polynomial = (ROOT / REPORTS["corpus"]).parent / "polynomial-original/tile"
    directories = sorted(polynomial.glob("tiling-pipeline-*"))
    if len(directories) != 1:
        raise ValueError("Expected the actual installed original polynomial pipeline")
    directory = directories[0]
    receipt = permitted(directory / "verified-membership.txt").read_text()
    match = re.fullmatch(r"verified-predicates=(\d+) cleared-floor-nodes=(\d+)\n", receipt)
    if not match or int(match[1]) < 4 or int(match[2]) == 0:
        raise ValueError("Actual verified floor-service consumption is required")
    generated = permitted(directory / "generated.loop").read_text()
    cost, unit_cost = complete_cost(reports["cost"]), complete_cost(reports["unit_cost"])
    for path in [Path(__file__), ROOT / "toolchain.lock.json"]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    return {"status": "validated", "date": "2026-10-09",
            "whole_program_entrypoint": proof.ENTRY, "whole_program_theorem": proof.ENTRY + "_correct",
            "new_proof_modules": certificate["new_modules"], "new_source_lines": certificate["new_source_lines"],
            "queried_endpoints": len(certificate["endpoints"]), "closed_endpoints": certificate["closed_endpoints"],
            "maximum_service_endpoint_globals": certificate["maximum_endpoint_globals"],
            "additional_global_axioms": [], "kernel_changed": False, "new_host_contract": False,
            "source_user_supplies_semantic_callbacks": False, "semantic_compiler_proof_unchanged": True,
            "verified_floor_membership_constructors_actually_consumed": True,
            "math_membership_exact_even_for_negative_numerators": True,
            "machine_condition_contract_requires_ranges_and_typed_view": True,
            "pure_condition_with_no_public_or_private_writes": True,
            "interval_bounds_prefix_placement_hoisting_and_unit_completion_are_untrusted": True,
            "final_actual_candidate_checker_and_existing_machine_lowering_remain_authoritative": True,
            "raw_to_adapted_equivalence_assumed": False, "new_runtime_dependent_loop_bounds": False,
            "first_build_rejection": "missing GuardSelectedReductionCandidate in native inputs; snapshot and failure retained",
            "proof_attempts": certificate["attempts"],
            "actual_polynomial": {"limit": int(permitted(directory / "adaptation-limit.txt").read_text()),
                "before": schedules(directory / "before.scop"),
                "after": schedules(directory / "before.scop.afterscheduling.scop"),
                "verified_predicates": int(match[1]), "cleared_floor_nodes": int(match[2]),
                "bound_proposals": permitted(directory / "bounded-proposals.txt").read_text(),
                "generated": generated},
            "first_complete_default_corpus": first_corpus, "complete_default_corpus": corpus,
            "contexts": {"polynomial": 20, "reduction": 14, "initialized": 20, "public_and_legacy": 7,
                "unchanged_assembly_paths": 3, "canonical_unit_mask_configurations": 10},
            "canonical_unit_matrix": [{key: row[key] for key in
                ["case", "tile_sizes", "installed_phase_calls_adaptations", "native_match", "passed"]} for row in matrix],
            "first_complete_call_cost": unit_cost, "complete_call_cost": cost,
            "cost_acceptance_failed": cost["optimized_over_unmarked_complete_call_ratio"] > 1,
            "next_required_work": "captured quotient parameters and dynamic affine tile bounds, useful complete costs, broader sequential source/configuration and original OLO coverage",
            "full_goal_complete": False, "reports": REPORTS, "bindings": bindings}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    result = summarize()
    if args.validate:
        if json.loads(OUTPUT.read_text()) != result:
            raise ValueError("Summary changed")
    else:
        with OUTPUT.open("x") as target:
            target.write(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": "validated", "reports": len(REPORTS), "bindings": len(result["bindings"]),
        "installed_cases": len(result["complete_default_corpus"]["installed_original_cases"]),
        "installed_sites": result["complete_default_corpus"]["installed_sites"],
        "complete_call_ratio": result["complete_call_cost"]["optimized_over_unmarked_complete_call_ratio"],
        "sha256": sha(OUTPUT)}))


if __name__ == "__main__":
    main()
