"""Bind actual original-matmul tile entries and complete-process cost diagnostics."""
import argparse
import json
from pathlib import Path

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_combined_residual_traced_corpus import checked

WORK = ROOT / "build/double-tree-combined-residual/matmul-execution-summary-v1"
PORTABLE = ROOT / "docs/double-tree-combined-matmul-execution.json"
PATH = ROOT / "build/double-tree-combined-residual/matmul-path-attempts/original-v1/report.json"
COST = ROOT / "build/double-tree-combined-residual/matmul-cost-attempts/original-v1/report.json"
EARLY_COST = ROOT / "build/double-tree-combined-residual/matmul-cost-diagnostic-v1/report.json"


def validate():
    report = json.loads(permitted(WORK / "report.json").read_text())
    if (report["status"] != "diagnostic_complete" or report["full_goal_complete"]
            or report["runtime_guard_refusal_exercised"] or report["all_candidate_updates_counted"]):
        raise ValueError("Invalid actual-matmul execution summary")
    for name, digest in report["bindings"].items():
        if sha(permitted(ROOT / name)) != digest:
            raise ValueError("Changed bound file: " + name)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    if args.validate:
        report = validate()
        print(json.dumps({"status": "validated", "bindings": len(report["bindings"])}))
        return
    bindings = {}
    path, cost, early = [checked(source, bindings) for source in [PATH, COST, EARLY_COST]]
    if (path["status"] != "passed" or path["tile_triples"] != path["expected_tile_triples"]
            or len(path["tile_triples"]) != 27 or path["first_observed_update"] != [[0, 0, 0]]
            or not path["assembly_not_modified"] or not path["complete_original_output_matches_in_debugger"]
            or cost["status"] != "diagnostic_complete" or not cost["all_outputs_match"]
            or len(cost["samples"]) != 21 or early["status"] != "diagnostic_complete"
            or not early["all_outputs_match"] or len(early["samples"]) != 21
            or cost["whole_program_theorem"] != path["whole_program_theorem"]
            or cost["original_input_sha256"] != path["original_input_sha256"]):
        raise ValueError("Missing actual tiling or complete original-output evidence")
    WORK.mkdir(parents=True, exist_ok=False)
    report = {"status": "diagnostic_complete", "case": "original-matmul",
              "compiler_entrypoint": cost["compiler_entrypoint"], "whole_program_theorem": cost["whole_program_theorem"],
              "original_input": cost["original_input"], "original_input_sha256": cost["original_input_sha256"],
              "source_computation_unchanged": True, "input_dimensions": [96, 96, 96], "tile_size": 32,
              "actual_observed_tile_entries": 27, "tile_order": path["tile_order"],
              "first_observed_candidate_point": [0, 0, 0], "complete_output_matches_in_debugger": True,
              "target_assembly_modified": False, "target_instrumented": False,
              "all_candidate_updates_counted": False, "runtime_guard_refusal_exercised": False,
              "cost_matching_calls": 21, "cost_batches": cost["batches"],
              "median_cpu_ms": cost["median_cpu_ms"], "paired_ratio_medians": cost["paired_ratio_medians"],
              "cost_includes_startup_initialization_kernel_digest_and_printing": True,
              "cpu_pinning": False, "isolated_guard_cost": False,
              "early_one_off_diagnostic": {"report": str(EARLY_COST.relative_to(ROOT)),
                  "matching_calls": 21, "paired_ratio_medians": early["paired_ratio_medians"],
                  "script_snapshot_present": False, "used_for_main_cost_numbers": False},
              "cross_program_or_larger_input_speedup_established": False,
              "configuration_union_is_not_actual_tiling_coverage": True,
              "full_goal_complete": False,
              "reports": {"path": str(PATH.relative_to(ROOT)), "cost": str(COST.relative_to(ROOT))},
              "bindings": bindings}
    bindings[str(Path(__file__).relative_to(ROOT))] = sha(Path(__file__))
    portable = {k: v for k, v in report.items() if k != "bindings"}
    portable["report"] = str((WORK / "report.json").relative_to(ROOT))
    with PORTABLE.open("x") as out:
        out.write(json.dumps(portable, indent=2) + "\n")
    bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "diagnostic_complete", "tile_entries": 27,
                      "matching_cost_calls": 21, "bindings": len(bindings)}))


if __name__ == "__main__":
    main()
