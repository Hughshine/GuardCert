"""Compare the complete identity-trace successor with the retained corpus run."""
import json
from collections import Counter
from pathlib import Path

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_combined_residual_traced_corpus import checked
import summarize_double_tree_combined_residual_corpus as earlier

SOURCE = ROOT / "build/benchmark-alignment/current-double-combined-residual-quiet-attempts/corpus-v1/report.json"
PRIOR = ROOT / "build/benchmark-alignment/current-double-combined-residual-attempts/corpus-v2/report.json"
WORK = ROOT / "build/double-tree-combined-residual/quiet-corpus-summary-v1"
PORTABLE = ROOT / "docs/double-tree-combined-residual-quiet-corpus.json"


def main():
    bindings = {}
    current = checked(SOURCE, bindings)
    prior = checked(PRIOR, bindings)
    checked(ROOT / "build/double-tree-combined-residual/quiet-summary-v1/report.json", bindings)
    if (current["status"] != "diagnostic_complete"
            or current["original_cases_attempted"] != 62
            or current["source_variants"] != 64
            or not current["identity_trace_erased_by_standard_extraction"]
            or current["native_failures"]):
        raise ValueError("Keep all originals, adaptations and actual compiler results")
    originals = [row for row in current["results"] if row["variant"] == "original"]
    if sum(len(row["configurations"]) for row in current["results"]) != 192:
        raise ValueError("Keep the complete configuration list")
    changes, modes = [], {}
    prior_rows = {(row["case"], row["variant"]): row for row in prior["results"]}
    for row in current["results"]:
        previous = prior_rows[(row["case"], row["variant"])]
        if row["input_sha256"] != previous["input_sha256"]:
            raise ValueError("Changed benchmark input")
        for mode, config in row["configurations"].items():
            before = previous["configurations"][mode]
            if config["source_sha256"] != before["source_sha256"]:
                raise ValueError("Changed compiler input")
            if config["status"] != before["status"]:
                changes.append({"case": row["case"], "variant": row["variant"], "mode": mode,
                                "before": before["status"], "after": config["status"],
                                "previous_compiler_timeout": before["compiler"]["timeout"],
                                "current_compiler_timeout": config["compiler"]["timeout"]})
    for mode in current["modes"]:
        tree = sorted(row["case"] for row in originals
                      if row["configurations"][mode]["installed"]
                      and row["configurations"][mode]["installed"][0] > 0)
        typed = sorted(row["case"] for row in originals
                       if row["configurations"][mode]["typed_installed"]
                       and row["configurations"][mode]["typed_installed"][2] > 0)
        union = sorted(set(tree) | set(typed))
        if mode == "unmarked" and union:
            raise ValueError("Unmarked controls install nothing")
        modes[mode] = {"statuses_including_separate_adaptations": dict(Counter(
            row["configurations"][mode]["status"] for row in current["results"])),
            "tree_cases": tree, "typed_cases": typed, "union_cases": union,
            "union_count": len(union)}
    original_matches = sum(config["status"] == "native_match" for row in originals
                           for config in row["configurations"].values())
    summary = {"status": "incomplete-functional-coverage", "source_report": str(SOURCE.relative_to(ROOT)),
               "source_report_sha256": sha(SOURCE), "prior_report": str(PRIOR.relative_to(ROOT)),
               "compiler_entrypoint": current["compiler_entrypoint"],
               "whole_program_theorem": current["whole_program_theorem"],
               "source_revision": current["source_revision"], "original_cases_attempted": 62,
               "disclosed_adaptations": 2, "configurations_attempted": 192,
               "native_configuration_matches": current["native_configuration_matches"],
               "original_configuration_matches": original_matches,
               "adaptation_configuration_matches": current["native_configuration_matches"] - original_matches,
               "native_mismatches_or_link_failures": [], "refusals": earlier.failures(current),
               "prior_refusals_retained": earlier.failures(prior), "status_changes": changes,
               "observed_guarded_shapes_by_mode": modes,
               "source_bytes_types_and_computations_unchanged": True,
               "identity_trace_erased_by_standard_extraction": True,
               "requested_transformations_and_accepted_paths_require_analysis": True,
               "controlled_compiler_or_guard_cost_comparison": False,
               "new_optimization_or_condition_derivation_algorithm_added": False,
               "full_goal_complete": False}
    for path in [Path(__file__), Path(earlier.__file__)]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    with PORTABLE.open("x") as output:
        output.write(json.dumps(summary, indent=2) + "\n")
    bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
    WORK.mkdir(parents=True, exist_ok=False)
    (WORK / "report.json").write_text(json.dumps({**summary, "bindings": bindings}, indent=2) + "\n")
    print(json.dumps({"status": summary["status"], "matches": summary["native_configuration_matches"],
                      "refusals": len(summary["refusals"]), "changes": changes, "bindings": len(bindings)}))


if __name__ == "__main__":
    main()
