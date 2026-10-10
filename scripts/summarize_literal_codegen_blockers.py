"""Bind terminal tiled failures without treating an ongoing corpus as complete."""
import json
from pathlib import Path

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_declared_literal_combined_corpus import checked

WORK = ROOT / "build/declared-literal-double/codegen-blockers-v1"
PORTABLE = ROOT / "docs/literal-tiled-codegen-blockers.json"
CORPUS = ROOT / "build/benchmark-alignment/current-declared-literal-combined-attempts/corpus-v1"
BASELINE = ROOT / "build/benchmark-alignment/current-double-combined-residual-quiet-attempts/corpus-v1/report.json"
STACK = ROOT / "build/declared-literal-double/resource-attempts/fusion10-stack-v1/report.json"


def main():
    bindings = {}
    previous = checked(BASELINE, bindings)
    stack = checked(STACK, bindings)
    retry = checked(ROOT / stack["replay_report"], bindings)
    if stack["stack_after"][0] != 64 * 1024 * 1024 or stack["all_configurations_native_match"]:
        raise ValueError("Expected the unsuccessful recorded stack-capacity retry")
    cases = []
    for case in ["fusion10", "fusion2"]:
        directory = CORPUS / (case + "-original")
        row = json.loads(permitted(directory / "row.json").read_text())
        parent, = [r for r in previous["results"] if r["case"] == case and r["variant"] == "original"]
        if row["input_sha256"] != parent["input_sha256"] or any(
                c["status"] != "native_match" for c in parent["configurations"].values()):
            raise ValueError("Expected the same pinned source and three baseline matches")
        failed = row["configurations"]["tiled"]
        if failed["status"] != "frontend_or_compiler_refusal":
            raise ValueError("Expected terminal compiler failure")
        receipt = directory / "tiled/tiling-pipeline-1"
        shape = permitted(receipt / "phase-shape.txt").read_text()
        log = permitted(directory / "tiled/compiler.stderr").read_text()
        if "added-dimensions=2,2" not in shape or (receipt / "tree-source.loop").exists():
            raise ValueError("Expected real tiled proposal before source-aware adaptation")
        if case == "fusion10" and (failed["compiler"]["returncode"] != 2 or "Stack overflow" not in log):
            raise ValueError("Expected the actual native stack exception")
        if case == "fusion2" and not failed["compiler"]["timeout"]:
            raise ValueError("Expected the 180-second compiler timeout")
        cases.append({"case": case, "source_sha256": row["input_sha256"],
            "baseline_all_three_outputs_match": True,
            "current_unmarked_and_untiled_match": all(row["configurations"][m]["status"] == "native_match"
                for m in ["unmarked", "untiled"]),
            "tiled_compiler": failed["compiler"], "real_phase_added_dimensions": [2, 2],
            "source_aware_adapter_receipt_present": False,
            "native_output_mismatch_observed": False})
        for path in directory.rglob("*"):
            if path.is_file():
                bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    retry_row, = retry["results"]
    if (retry_row["case"] != "fusion10" or retry_row["input_sha256"] != cases[0]["source_sha256"]
            or retry_row["configurations"]["tiled"]["compiler"]["returncode"] != 2):
        raise ValueError("Expected the same failure at the larger stack limit")
    WORK.mkdir(parents=True, exist_ok=False)
    bindings[str(Path(__file__).relative_to(ROOT))] = sha(Path(__file__))
    report = {"status": "diagnostic_complete", "cases": cases,
        "complete_corpus_result_claimed": False, "compiler_algorithmic_stage_fully_localized": False,
        "fusion10_stack_retry_mib": 64, "fusion10_stack_retry_solved": False,
        "compiler_semantic_inputs_changed_for_retry": False,
        "source_adaptations_used": False, "failure_is_not_successful_fallback": True,
        "tiled_support_established_for_these_cases": False, "full_goal_complete": False,
        "reports": {"baseline": str(BASELINE.relative_to(ROOT)), "stack": str(STACK.relative_to(ROOT)),
            "retry": stack["replay_report"]}, "bindings": bindings}
    portable = {k: v for k, v in report.items() if k != "bindings"}
    portable["report"] = str((WORK / "report.json").relative_to(ROOT))
    with PORTABLE.open("x") as out:
        out.write(json.dumps(portable, indent=2) + "\n")
    bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "diagnostic_complete", "terminal_cases": len(cases),
        "stack_retry_solved": False, "bindings": len(bindings)}))


if __name__ == "__main__":
    main()
