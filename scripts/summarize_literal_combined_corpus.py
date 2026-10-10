"""Compare the completed literal compiler corpus with its pinned quiet baseline."""
import json
from pathlib import Path

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_declared_literal_combined_corpus import checked

WORK = ROOT / "build/declared-literal-double/corpus-summary-v1"
PORTABLE = ROOT / "docs/declared-literal-double-corpus.json"
CURRENT = ROOT / "build/benchmark-alignment/current-declared-literal-combined-attempts/corpus-v1/report.json"
BASELINE = ROOT / "build/benchmark-alignment/current-double-combined-residual-quiet-attempts/corpus-v1/report.json"
BLOCKERS = ROOT / "build/declared-literal-double/codegen-blockers-v1/report.json"


def main():
    bindings = {}
    current, baseline, blockers = [checked(path, bindings) for path in [CURRENT, BASELINE, BLOCKERS]]
    if not current["complete_62_case_corpus"] or current["source_variants"] != 64 or current["native_failures"]:
        raise ValueError("Expected a complete corpus with separate compiler refusals")
    key = lambda row: (row["case"], row["variant"])
    old = {key(row): row for row in baseline["results"]}
    if set(old) != {key(row) for row in current["results"]}:
        raise ValueError("Corpus source sets differ")
    changes = []
    refusals = []
    original_matches = 0
    adapted_matches = 0
    for row in current["results"]:
        previous = old[key(row)]
        if row["input_sha256"] != previous["input_sha256"]:
            raise ValueError("Changed pinned computation")
        for mode, config in row["configurations"].items():
            prior = previous["configurations"][mode]
            if config["status"] == "native_match":
                if row["variant"] == "original":
                    original_matches += 1
                else:
                    adapted_matches += 1
            else:
                refusals.append({"case": row["case"], "variant": row["variant"], "mode": mode,
                    "compiler_returncode": config["compiler"]["returncode"], "timeout": config["compiler"]["timeout"]})
            if config["status"] != prior["status"]:
                changes.append({"case": row["case"], "variant": row["variant"], "mode": mode,
                    "previous": prior["status"], "current": config["status"]})
    if (original_matches, adapted_matches) != (178, 6) or len(refusals) != 8 or len(changes) != 2:
        raise ValueError("Unexpected corpus outcome; review before publishing this summary")
    if {item["case"] for item in changes} != {"fusion10", "fusion2"} or any(item["mode"] != "tiled" for item in changes):
        raise ValueError("Unexpected new regression")
    WORK.mkdir(parents=True, exist_ok=False)
    bindings[str(Path(__file__).relative_to(ROOT))] = sha(Path(__file__))
    report = {"status": "diagnostic_complete", "original_cases": 62, "disclosed_adaptations": 2,
        "configurations": 192, "matching_complete_outputs": original_matches + adapted_matches,
        "matching_original_configurations": original_matches, "matching_adapted_configurations": adapted_matches,
        "baseline_matching_complete_outputs": baseline["native_configuration_matches"],
        "refusals": refusals, "status_changes": changes, "all_source_hashes_preserved": True,
        "native_output_mismatches": 0, "link_failures": 0,
        "old_shape_tree_untiled_cases": current["installed_cases"],
        "old_shape_typed_untiled_cases": current["typed_installed_cases"],
        "old_shape_untiled_union": len(set(current["installed_cases"]) | set(current["typed_installed_cases"])),
        "literal_installations_not_counted_by_old_shape_diagnostic": True,
        "all_requested_transformations_verified_by_replay": False,
        "controlled_cost_comparison": False, "full_goal_complete": False,
        "reports": {"current": str(CURRENT.relative_to(ROOT)), "baseline": str(BASELINE.relative_to(ROOT)),
            "blockers": str(BLOCKERS.relative_to(ROOT))}, "bindings": bindings}
    portable = {k: v for k, v in report.items() if k != "bindings"}
    portable["report"] = str((WORK / "report.json").relative_to(ROOT))
    with PORTABLE.open("x") as out:
        out.write(json.dumps(portable, indent=2) + "\n")
    bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "diagnostic_complete", "matching_outputs": 184,
        "configurations": 192, "new_compiler_regressions": 2, "bindings": len(bindings)}))


if __name__ == "__main__":
    main()
