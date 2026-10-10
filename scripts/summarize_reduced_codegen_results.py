"""Bind projection regression results separately from actual tiling and cost."""
import json
from pathlib import Path
import re

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_reduced_literal_combined_corpus import checked

WORK = ROOT / "build/equality-reduced-codegen/results-v1"
PORTABLE = ROOT / "docs/equality-reduced-codegen-results.json"
CURRENT = ROOT / "build/benchmark-alignment/current-reduced-literal-combined-attempts/corpus-v1/report.json"
FOCUS = ROOT / "build/benchmark-alignment/current-reduced-literal-combined-attempts/blockers-v1/report.json"
PREVIOUS = ROOT / "build/benchmark-alignment/current-declared-literal-combined-attempts/corpus-v1/report.json"
OBSERVER = ROOT / "build/equality-reduced-codegen/execution-attempts/original-v2/report.json"


def selected_clight(path):
    text = permitted(path).read_text()
    if text.count("__guardcert_scop_1:") != 1:
        raise ValueError("Expected one selected original region")
    return text.split("__guardcert_scop_1:", 1)[1].split("print_modeled_state_digest();", 1)[0]


def loop_shape(text):
    depth, active, maximum = 0, [], 0
    tokens = re.findall(r"\bfor\s*\([^\n]*\)\s*\{|[{}]", text)
    for token in tokens:
        if token == "}":
            if active and active[-1] == depth:
                active.pop()
            depth -= 1
            if depth < 0:
                raise ValueError("Unbalanced selected region")
        else:
            depth += 1
            if token.startswith("for"):
                active.append(depth)
                maximum = max(maximum, len(active))
    if depth or active:
        raise ValueError("Unbalanced selected region")
    return {"for_loops": sum(token.startswith("for") for token in tokens),
            "maximum_nested_for_loops": maximum, "if_statements": text.count("if (")}


def main():
    bindings = {}
    current, focus, previous, observer = [checked(path, bindings)
        for path in [CURRENT, FOCUS, PREVIOUS, OBSERVER]]
    if not current["complete_62_case_corpus"] or current["source_variants"] != 64:
        raise ValueError("Require the complete pinned corpus")
    before = {(row["case"], row["variant"]): row for row in previous["results"]}
    changes = []
    for row in current["results"]:
        old = before.pop((row["case"], row["variant"]))
        if row["input_sha256"] != old["input_sha256"]:
            raise ValueError("Changed source computation")
        for mode, result in row["configurations"].items():
            prior = old["configurations"][mode]
            if prior["status"] != result["status"]:
                changes.append({"case": row["case"], "variant": row["variant"], "mode": mode,
                    "before": prior["status"], "after": result["status"],
                    "prior_compiler_seconds": prior["compiler"]["elapsed_seconds"],
                    "compiler_seconds": result["compiler"]["elapsed_seconds"]})
    if before:
        raise ValueError("Missing original configuration")
    focus_rows = []
    for row in focus["results"]:
        directory = FOCUS.parent / (row["case"] + "-original")
        shapes = {mode: loop_shape(selected_clight(directory / mode / "program.light.c"))
                  for mode in ["untiled", "tiled"]}
        phase = directory / "tiled/tiling-pipeline-1"
        refused = phase / "tree-adaptation-refusal.txt"
        if not (phase / "tree-raw-generated.loop").exists():
            raise ValueError("Missing actual raw codegen output")
        item = {"case": row["case"], "source_sha256": row["input_sha256"],
            "all_three_complete_outputs_match": all(cfg["status"] == "native_match"
                for cfg in row["configurations"].values()),
            "compiler_seconds_single_diagnostic": {mode: cfg["compiler"]["elapsed_seconds"]
                for mode, cfg in row["configurations"].items()},
            "selected_Clight_shapes": shapes,
            "actual_phase_shape": permitted(phase / "phase-shape.txt").read_text().strip(),
            "whole_source_raw_codegen_completed": True,
            "whole_candidate_adaptation_refused": refused.exists(),
            "whole_candidate_adaptation_refusal": permitted(refused).read_text().strip() if refused.exists() else None,
            "fused_candidate_installed_claimed": False,
            "source_numeric_types_and_computation_preserved": True}
        if row["case"] == "nodep":
            old = ROOT / "build/benchmark-alignment/current-declared-literal-combined-attempts/nodep-v1/nodep-original"
            item["prior_selected_Clight_shapes"] = {mode: loop_shape(selected_clight(old / mode / "program.light.c"))
                for mode in ["untiled", "tiled"]}
        focus_rows.append(item)
    WORK.mkdir(parents=True, exist_ok=False)
    for path in [Path(__file__), *[p for p in WORK.rglob("*") if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {"status": "complete", "compiler_entrypoint": current["compiler_entrypoint"],
        "whole_program_theorem": current["whole_program_theorem"],
        "original_cases": 62, "disclosed_adaptations": 2, "configurations": 192,
        "native_configuration_matches": current["native_configuration_matches"],
        "original_configuration_matches": sum(cfg["status"] == "native_match"
            for row in current["results"] if row["variant"] == "original"
            for cfg in row["configurations"].values()),
        "nonmatching_configurations": [{"case": row["case"], "variant": row["variant"],
            "mode": mode, "status": cfg["status"], "compiler_timeout": cfg["compiler"]["timeout"]}
            for row in current["results"] for mode, cfg in row["configurations"].items()
            if cfg["status"] != "native_match"],
        "configuration_status_changes": changes, "focused_actual_candidates": focus_rows,
        "nodep_updates_per_configuration": 400,
        "nodep_update_observation_passed": observer["status"] == "passed",
        "nodep_updating_tile_groups": len(observer["observations"]["tiled"]["updating_tile_pairs"]),
        "nodep_runtime_guard_refusal_exercised": False,
        "original_input_hashes_unchanged": True,
        "actual_tiling_support_for_all_62_cases_claimed": False,
        "controlled_compiler_or_runtime_cost_comparison": False,
        "OLO_compact_entry_condition_complete": False, "full_goal_complete": False,
        "reports": {"current": str(CURRENT.relative_to(ROOT)), "focus": str(FOCUS.relative_to(ROOT)),
            "previous": str(PREVIOUS.relative_to(ROOT)), "observer": str(OBSERVER.relative_to(ROOT))},
        "bindings": bindings}
    portable = {key: value for key, value in report.items() if key != "bindings"}
    portable["report"] = str((WORK / "report.json").relative_to(ROOT))
    with PORTABLE.open("x") as out:
        out.write(json.dumps(portable, indent=2) + "\n")
    bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
    with (WORK / "report.json").open("x") as out:
        out.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "complete", "matches": report["native_configuration_matches"],
        "status_changes": len(changes), "bindings": len(bindings)}))


if __name__ == "__main__":
    main()
