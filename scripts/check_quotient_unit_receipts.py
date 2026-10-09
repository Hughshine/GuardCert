"""Check frozen unit runs after correcting an installation-tag observation bug."""
import argparse
import json
from pathlib import Path
import re

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked
from check_verified_prefix_unit_matrix import MATRIX


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--observed-report", required=True, type=Path)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not re.fullmatch("[a-z0-9-]+", args.attempt):
        raise ValueError("Fresh simple attempt required")
    bindings = {}
    observed = checked(permitted(ROOT / args.observed_report), bindings)
    if len(observed["cases"]) != len(MATRIX) or observed["status"] != "rejected":
        raise ValueError("Expected the completed first observer's ten runs")
    work = ROOT / "build/quotient-double-tiling/unit-receipt-attempts" / args.attempt
    work.mkdir(parents=True, exist_ok=False)
    (work / "script.py").write_bytes(permitted(Path(__file__)).read_bytes())
    rows = []
    for original, (case, sizes) in zip(observed["cases"], MATRIX):
        if (original["case"] != case or original["tile_sizes"] != sizes
                or original["quotient_older_divisor"] is not None):
            raise ValueError("Unexpected original observation")
        report_path = permitted(ROOT / original["report"])
        report = checked(report_path, bindings)
        result = report["results"][0]
        trace = permitted(report_path.parent / f"{case}-tile/compiler.stderr")
        tags = re.findall(r"GUARDCERT_QUOTIENT_TILING_INSTALLED regions=(\d+) older_reduction_regions=(\d+) divisor=(\d+)", trace.read_text())
        values = [int(value) for value in tags[-1]] if tags else None
        row = {"case": case, "tile_sizes": sizes, "original_report": original["report"],
               "installed_phase_calls_adaptations": result["installed_phase_calls_adaptations"],
               "quotient_older_divisor": values, "native_match": result["native_match"],
               "passed": original["returncode"] == 0 and report["status"] == "passed"
                         and result["passed"] and values == [2, 0, 1]}
        rows.append(row)
        print(json.dumps(row), flush=True)
    for path in [Path(__file__), ROOT / "scripts/check_verified_prefix_unit_matrix.py",
                 *[p for p in work.rglob("*") if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {"status": "passed" if all(row["passed"] for row in rows) else "rejected",
              "cases": rows, "failed_observer_report": str(args.observed_report),
              "observer_failure": "regex used quotient/older instead of regions/older_reduction_regions",
              "native_compiler_and_successful_runtime_checks_not_rerun": True,
              "all_canonical_rank_three_unit_masks_attempted": True,
              "canonical_rank_two_unit_masks_attempted": True,
              "actual_quotient_installation_checked_independently": True,
              "runtime_cost_established": False, "full_goal_complete": False,
              "bindings": bindings}
    (work / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    if report["status"] != "passed":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
