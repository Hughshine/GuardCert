"""Validate and summarize actual double tiling, preserving refused and timed-out attempts."""

import argparse
import json
from pathlib import Path

import audit_double_tiled_installation as proof
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked

OUTPUT = ROOT / "docs/double-tiling-installation.json"
REPORTS = {
    "compiler_v1": "build/double-tiling/compiler-attempts/native-v1/report.json",
    "compiler_v2": "build/double-tiling/compiler-attempts/native-v2/report.json",
    "original_matrix": "build/double-tiling/original-attempts/original-matrix-v1/report.json",
    "rectangular_sizes": "build/double-tiling/original-attempts/rectangular-sizes-v1/report.json",
    "contexts": "build/double-tiling/check-attempts/contexts-v2/report.json",
    "paths": "build/double-tiling/path-attempts/paths-v1/report.json",
    "corpus": "build/benchmark-alignment/double-tiled-attempts/corpus-v1/report.json",
    "initial_context_rejection": "build/double-tiling/check-attempts/contexts-v1/rejection.json",
    "initial_unit_refusal": "build/double-tiling/original-attempts/mixed-unit-v1/report.json",
    "mixed_unit": "build/double-tiling/original-attempts/mixed-unit-v2/report.json",
    "transpose_unit": "build/double-tiling/original-attempts/transpose-unit-v2/report.json",
    "all_unit": "build/double-tiling/original-attempts/all-unit-v2/report.json",
    "three_axis_unit": "build/double-tiling/original-attempts/three-axis-unit-v2/report.json",
    "normal_v2": "build/double-tiling/original-attempts/original-v2/report.json",
    "high_rank": "build/double-tiling/original-attempts/high-rank-v1/report.json",
}


def summarize():
    baseline = proof.validate()
    bindings = dict(baseline["bindings"])
    bindings[str((proof.WORK / "report.json").relative_to(ROOT))] = sha(proof.WORK / "report.json")
    reports = {name: checked(permitted(ROOT / path), bindings) for name, path in REPORTS.items()}
    for name, report in reports.items():
        expected = ("built" if name.startswith("compiler") else "diagnostic_complete" if name == "corpus"
                    else "rejected" if name.startswith("initial") else "passed")
        if report["status"] != expected:
            raise ValueError(f"Unexpected report: {name}")
    for name in ["compiler_v1", "compiler_v2"]:
        if (reports[name]["whole_program_entrypoint"] != proof.ENTRY
                or reports[name]["actual_source_Csem_to_Asm_theorem"] != proof.ENTRY + "_correct"):
            raise ValueError("Wrong extracted entry")
    matrix = reports["original_matrix"]["results"]
    if len(matrix) != 10 or not all(row["passed"] for row in matrix):
        raise ValueError("Incomplete original matrix")
    contexts = reports["contexts"]["cases"]
    if len(contexts) != 14 or not all(row["passed"] for row in contexts):
        raise ValueError("Incomplete context checks")
    paths = reports["paths"]["cases"]
    if len(paths) != 3 or not all(row["passed"] for row in paths):
        raise ValueError("Incomplete unchanged-assembly path checks")
    corpus = reports["corpus"]
    rows = corpus["results"]
    if corpus["original_cases_attempted"] != 62 or len(rows) != 64 or corpus["native_failures"]:
        raise ValueError("Incomplete full corpus diagnostic")
    originals = [row for row in rows if row["variant"] == "original"]
    adaptations = [row for row in rows if row["variant"] != "original"]
    installs = {row["case"]: row["configurations"]["tile"]["installed"][2]
                for row in originals if row["configurations"]["tile"]["installed"]
                and row["configurations"]["tile"]["installed"][2]}
    if len(installs) != 9 or sum(installs.values()) != 22:
        raise ValueError("Changed installed-corpus results")
    failures = {row["case"]: row["configurations"]["tile"]["compiler"]
                for row in originals if row["configurations"]["tile"]["status"] != "native_match"}
    if set(failures) != {"corcol3", "pca", "tce"} or not failures["tce"]["timeout"]:
        raise ValueError("Changed corpus refusals/timeouts")
    high_rank = reports["high_rank"]["results"]
    if (len(high_rank) != 1 or high_rank[0]["case"] != "tce" or not high_rank[0]["passed"]
            or high_rank[0]["installed_phase_calls_adaptations"] != [4, 4, 4]):
        raise ValueError("Incomplete high-rank retry")
    unit_rows = [row for name in ["mixed_unit", "transpose_unit", "all_unit", "three_axis_unit"]
                 for row in reports[name]["results"]]
    if len(unit_rows) != 4 or not all(row["passed"] for row in unit_rows):
        raise ValueError("Incomplete unit-coordinate successor")
    if reports["initial_context_rejection"]["native_mismatches"]:
        raise ValueError("Unexpected initial native mismatch")
    initial_unit = reports["initial_unit_refusal"]["results"]
    if not all(row["native_match"] and row["installed_phase_calls_adaptations"][0] == 0 for row in initial_unit):
        raise ValueError("Unexpected initial unit refusal")
    all_installs = {**installs, "tce": 4}
    bindings[str(Path(__file__).relative_to(ROOT))] = sha(Path(__file__))
    return {"status": "validated", "whole_program_entrypoint": proof.ENTRY,
            "whole_program_theorem": proof.ENTRY + "_correct",
            "proof_report": "docs/double-tiling-proof.json",
            "proof_report_sha256": sha(ROOT / "docs/double-tiling-proof.json"),
            "new_semantic_proofs_in_native_successor": False, "additional_global_axioms": [],
            "maximum_inherited_globals": baseline["maximum_endpoint_globals"],
            "phase_options": "real Pluto sequential tiling with identity pretransform; later scheduling/ISS not connected here",
            "original_numeric_types_and_computations_preserved": True,
            "C_users_supply_semantic_callbacks_or_handwritten_target": False,
            "full_corpus_v1": {"originals": 62, "disclosed_adaptations": 2,
                "raw_native_matches": sum(row["configurations"]["tile"]["status"] == "native_match" for row in originals),
                "adaptation_native_matches": sum(row["configurations"]["tile"]["status"] == "native_match" for row in adaptations),
                "installed_cases": installs, "installed_sites": sum(installs.values()),
                "frontend_refusals": ["corcol3", "pca"], "terminal_compiler_timeout_seconds": {"tce": 180},
                "cases_without_phase_calls": [row["case"] for row in originals
                    if row["configurations"]["tile"]["installed"] is not None
                    and not row["configurations"]["tile"]["tiling_phase_calls"]],
                "default_tile_size": 32, "private_count": 32,
                "Clight_comparison_to_unmarked_not_available_in_this_report": True},
            "high_rank_v2": {"case": "tce", "installed_sites": 4, "compiler_budget_seconds": 600,
                "compiler_elapsed_seconds_diagnostic": high_rank[0]["compiler"]["elapsed_seconds"],
                "compiler_wall_controlled": False, "point_dimensions": 5, "tiled_loop_depth": 10,
                "native_matches_original_GCC": True, "private_count": 32},
            "combined_original_tiling_cases": all_installs, "combined_original_tiling_sites": sum(all_installs.values()),
            "combined_counts_span_two_bound_native_builds": True,
            "original_matrix_checks_v1": len(matrix), "rectangular_sizes_v1": "2,3",
            "context_checks_v1_compiler": len(contexts),
            "public_controls": {row["case"]: row["public_controls"] for row in contexts if "public_controls" in row},
            "multiple_marked_installs_and_calls": [4, 4], "marked_with_unmarked_installs_and_calls": [2, 2],
            "unchanged_assembly_path_checks_v1_compiler": len(paths),
            "paths": {row["case"]: row["actual"] for row in paths},
            "unit_coordinate_successor_v2": {"checks": 4, "tested_tiles": ["1,3", "3,1", "1,1", "1,3,2"],
                "checker_and_proof_unchanged": True,
                "prepared_codegen_dump": "original-raw-generated.loop", "completion_proposal_dump": "completed.loop",
                "final_candidate_dump": "generated.loop", "base_raw_dump_is_adapter_input": True},
            "normal_v2_native_checks": len(reports["normal_v2"]["results"]),
            "initial_unit_refusal_and_context_script_failures_preserved": True,
            "compact_runtime_guard_changed_by_this_stage": False,
            "dynamic_alias_guard_added": False,
            "guard_or_total_cost_controlled": False, "speedup_claimed": False, "full_goal_complete": False,
            "pending": ["affine scheduling followed by tiling; other sequential phases",
                "initialized/multiple-bound/loaded and other original source structures",
                "automatic scratch sizing and faster high-rank compilation",
                "compact conditions, useful acceptance and controlled complete costs",
                "original BT and LLVM/SPEC plus larger tiers"],
            "reports": [{"name": name, "path": path, "sha256": sha(ROOT / path), "status": reports[name]["status"]}
                        for name, path in REPORTS.items()], "bindings": bindings}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    result = summarize()
    if args.validate:
        if json.loads(OUTPUT.read_text()) != result:
            raise ValueError("Changed aggregate evidence")
    else:
        with OUTPUT.open("x") as target:
            target.write(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": "validated", "reports": len(REPORTS), "bindings": len(result["bindings"]),
                      "original_tiling_cases": len(result["combined_original_tiling_cases"]),
                      "original_tiling_sites": result["combined_original_tiling_sites"],
                      "report_sha256": sha(OUTPUT)}))


if __name__ == "__main__":
    main()
