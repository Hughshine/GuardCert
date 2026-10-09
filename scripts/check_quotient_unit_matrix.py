"""Replay unit tile masks and distinguish quotient from older installations."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked
from check_verified_prefix_unit_matrix import MATRIX


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler-report", required=True, type=Path)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not re.fullmatch("[a-z0-9-]+", args.attempt):
        raise ValueError("Use a new simple attempt name")
    bindings = {}
    build = checked(permitted(ROOT / args.compiler_report), bindings)
    if (build["status"] != "built" or not build["actual_safe_quotient_capture_extracted"]
            or not build["fallback_phase_resolver_reads_actual_intermediate_program"]):
        raise ValueError("Expected the actual quotient compiler")
    work = ROOT / "build/quotient-double-tiling/unit-matrix-attempts" / args.attempt
    work.mkdir(parents=True, exist_ok=False)
    (work / "script.py").write_bytes(permitted(Path(__file__)).read_bytes())
    probe = permitted(ROOT / "scripts/probe_double_tiled_originals.py")
    rows = []
    for index, (case, sizes) in enumerate(MATRIX):
        attempt = f"{args.attempt}-mask-{index}"
        argv = [sys.executable, str(probe), "--compiler-report", str(args.compiler_report),
                "--attempt", attempt, "--cases", case, "--modes", "tile", "--tile-sizes", sizes]
        run = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True)
        (work / f"mask-{index}.log").write_text(run.stdout + run.stderr)
        report_path = ROOT / "build/double-tiling/original-attempts" / attempt / "report.json"
        report = checked(permitted(report_path), bindings)
        result = report["results"][0]
        trace = permitted(report_path.parent / f"{case}-tile/compiler.stderr").read_text()
        tags = re.findall(r"GUARDCERT_QUOTIENT_TILING_INSTALLED quotient=(\d+) older=(\d+) divisor=(\d+)", trace)
        observed = [int(value) for value in tags[-1]] if tags else None
        row = {"case": case, "tile_sizes": sizes, "command": argv,
               "report": str(report_path.relative_to(ROOT)), "returncode": run.returncode,
               "installed_phase_calls_adaptations": result["installed_phase_calls_adaptations"],
               "quotient_older_divisor": observed, "native_match": result["native_match"],
               "passed": run.returncode == 0 and report["status"] == "passed"
                         and result["passed"] and observed == [2, 0, 1]}
        rows.append(row)
        print(json.dumps(row), flush=True)
    for path in [Path(__file__), probe, ROOT / "scripts/check_verified_prefix_unit_matrix.py",
                 *[path for path in work.rglob("*") if path.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {"status": "passed" if all(row["passed"] for row in rows) else "rejected",
              "cases": rows, "all_canonical_rank_three_unit_masks_attempted": True,
              "canonical_rank_two_unit_masks_attempted": True,
              "actual_quotient_installation_checked_independently": True,
              "actual_nonunit_argument_order_retained": True,
              "general_affine_unit_completion_claimed": False,
              "runtime_cost_established": False, "full_goal_complete": False, "bindings": bindings}
    (work / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    if report["status"] != "passed":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
