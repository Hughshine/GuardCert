"""Validate the first source probe and resolve its CompCert dump-path diagnostic."""

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PARENT = ROOT / "build/benchmark-alignment/probe-v1/report.json"
WORK = ROOT / "build/benchmark-alignment/probe-analysis-v1"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    if WORK.exists():
        raise ValueError("Analysis checkpoint already exists")
    report = json.loads(PARENT.read_text())
    if not report["complete_case_list_attempted"] or report["attempted_cases"] != 62:
        raise ValueError("The full case list was not attempted")
    for path, digest in report["bindings"].items():
        if sha(ROOT / path) != digest:
            raise ValueError(f"Changed probe binding: {path}")
    rows = []
    for case in report["results"]:
        directory = PARENT.parent / case["case"]
        baseline = directory / "disabled/marked.light.c"
        configurations = {}
        for mode, result in case["configurations"].items():
            actual = directory / mode / "marked.light.c"
            parsed = directory / mode / "marked.parsed.c"
            same = actual.exists() and baseline.exists() and actual.read_bytes() == baseline.read_bytes()
            configurations[mode] = {
                "compile_returncode": result["compile"]["returncode"],
                "native_status": result["status"],
                "actual_clight_dump": str(actual.relative_to(ROOT)) if actual.exists() else None,
                "actual_parsed_dump": str(parsed.relative_to(ROOT)) if parsed.exists() else None,
                "actual_clight_equals_disabled": same,
                "pipeline_artifact_count": len(result["phase_artifacts"]),
                "selection_trace_count": len(result["source_selection_trace"]),
                "optimization_status": "disabled_control" if mode == "disabled" else
                    "unchanged_clight_no_pipeline_call" if same and not result["phase_artifacts"] else
                    "frontend_compile_refusal" if result["status"] == "compile_failed" else "requires_analysis",
            }
        rows.append({"case": case["case"], "configurations": configurations})
    bindings = {str(PARENT.relative_to(ROOT)): sha(PARENT), str(Path(__file__).relative_to(ROOT)): sha(Path(__file__))}
    result = {
        "kind": "original_corpus_first_attempt_analysis", "status": "validated",
        "parent_report_sha256": sha(PARENT),
        "raw_dump_path_diagnostic_corrected": "CompCert writes marked.light.c in each invocation cwd; parent expected program.light.c",
        "case_count": 62, "configuration_attempts": sum(len(row["configurations"]) for row in rows),
        "native_matches": sum(mode["native_status"] == "native_match" for row in rows for mode in row["configurations"].values()),
        "active_unchanged_clight_no_pipeline_pairs": sum(mode["optimization_status"] == "unchanged_clight_no_pipeline_call" for row in rows for mode in row["configurations"].values()),
        "frontend_refused_cases": [row["case"] for row in rows if row["configurations"]["disabled"]["compile_returncode"] != 0],
        "requested_optimization_demonstrated": False, "rows": rows, "bindings": bindings,
    }
    WORK.mkdir()
    (WORK / "report.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: value for key, value in result.items() if key not in ["rows", "bindings"]}))


if __name__ == "__main__":
    main()
