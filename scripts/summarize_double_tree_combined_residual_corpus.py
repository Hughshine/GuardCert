"""Keep complete outputs, guarded shapes and transformation support separate."""
import json
from collections import Counter
from pathlib import Path

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_combined_residual_traced_corpus import checked

BASE = ROOT / "build/benchmark-alignment/current-double-combined-residual-attempts"
PREVIOUS = ROOT / "build/benchmark-alignment/current-double-residual-attempts/corpus-v2/report.json"
PORTABLE = ROOT / "docs/double-tree-combined-residual-corpus.json"
WORK = ROOT / "build/double-tree-combined-residual/corpus-summary-v1"


def failures(report):
    return [{"case": row["case"], "variant": row["variant"], "mode": mode,
             "status": config["status"],
             "compiler_returncode": config["compiler"]["returncode"],
             "compiler_timeout": config["compiler"]["timeout"],
             "compiler_seconds": config["compiler"]["elapsed_seconds"]}
            for row in report["results"]
            for mode, config in row["configurations"].items()
            if config["status"] != "native_match"]


def main():
    bindings = {}
    earlier = checked(BASE / "corpus-v1/report.json", bindings)
    report = checked(BASE / "corpus-v2/report.json", bindings)
    previous = checked(PREVIOUS, bindings)
    for value in [earlier, report, previous]:
        configurations = [config for row in value["results"]
                          for config in row["configurations"].values()]
        if (value["status"] != "diagnostic_complete"
                or value["original_cases_attempted"] != 62
                or value["source_variants"] != 64 or len(configurations) != 192
                or value["native_failures"]):
            raise ValueError("Require all original inputs and separately disclosed adaptations")
    by_mode = {}
    originals = [row for row in report["results"] if row["variant"] == "original"]
    for mode in report["modes"]:
        tree = sorted(row["case"] for row in originals
                      if row["configurations"][mode]["installed"]
                      and row["configurations"][mode]["installed"][0] > 0)
        typed = sorted(row["case"] for row in originals
                       if row["configurations"][mode]["typed_installed"]
                       and row["configurations"][mode]["typed_installed"][2] > 0)
        union = sorted(set(tree) | set(typed))
        if mode == "unmarked" and union:
            raise ValueError("Unmarked controls must have no installed shapes")
        by_mode[mode] = {
            "statuses_including_separate_adaptations": dict(Counter(
                row["configurations"][mode]["status"] for row in report["results"])),
            "tree_cases": tree, "typed_cases": typed,
            "overlap_cases": sorted(set(tree) & set(typed)),
            "union_cases": union, "union_count": len(union)}
    refusal_rows = failures(report)
    if (len(refusal_rows) != 7
            or sum(row["compiler_timeout"] for row in refusal_rows) != 1):
        raise ValueError("Retain the six initializer refusals and the jacobi timeout")
    original_matches = sum(config["status"] == "native_match" for row in originals
                           for config in row["configurations"].values())
    adaptation_matches = report["native_configuration_matches"] - original_matches
    bindings[str(Path(__file__).relative_to(ROOT))] = sha(permitted(Path(__file__)))
    summary = {
        "status": "incomplete-functional-coverage",
        "source_report": str((BASE / "corpus-v2/report.json").relative_to(ROOT)),
        "source_report_sha256": sha(BASE / "corpus-v2/report.json"),
        "compiler_entrypoint": report["compiler_entrypoint"],
        "whole_program_theorem": report["whole_program_theorem"],
        "source_revision": report["source_revision"],
        "original_cases_attempted": 62, "disclosed_adaptations": 2,
        "configurations_attempted": 192,
        "original_configuration_matches": original_matches,
        "adaptation_configuration_matches": adaptation_matches,
        "native_configuration_matches": report["native_configuration_matches"],
        "native_mismatches_or_link_failures": [], "refusals": refusal_rows,
        "observed_guarded_shapes_by_mode": by_mode,
        "standalone_residual_untiled_cases": previous["installed_cases"],
        "additional_untiled_guarded_shape_cases": sorted(
            set(by_mode["untiled"]["union_cases"]) - set(previous["installed_cases"])),
        "earlier_run": {"source_report": str((BASE / "corpus-v1/report.json").relative_to(ROOT)),
                        "matches": earlier["native_configuration_matches"],
                        "refusals": failures(earlier),
                        "typed_installation_counter_available": False},
        "tree_and_typed_counts_are_not_summed": True,
        "original_numeric_types_and_computations_preserved": True,
        "initializer_adaptations_are_separate_sources": True,
        "guarded_shapes_do_not_establish_nonidentity_or_requested_tiling": True,
        "scheduler_model_and_final_candidate_analysis_still_required": True,
        "controlled_cost_comparison": False,
        "standalone_residual_cost_ratio_transferred_to_combined_compiler": False,
        "full_goal_complete": False}
    with PORTABLE.open("x") as output:
        output.write(json.dumps(summary, indent=2) + "\n")
    bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
    WORK.mkdir(parents=True, exist_ok=False)
    (WORK / "report.json").write_text(json.dumps({**summary, "bindings": bindings}, indent=2) + "\n")
    print(json.dumps({"status": summary["status"],
                      "matches": summary["native_configuration_matches"],
                      "untiled_guarded_shape_cases": by_mode["untiled"]["union_count"],
                      "tiled_guarded_shape_cases": by_mode["tiled"]["union_count"],
                      "bindings": len(bindings)}))


if __name__ == "__main__":
    main()
