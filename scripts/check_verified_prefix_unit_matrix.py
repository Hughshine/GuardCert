"""Replay all canonical rank-two/rank-three unit masks on original computations."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked

MATRIX = [("matmul-seq", sizes) for sizes in
          ["1,1,1", "1,32,32", "32,1,32", "32,32,1", "1,1,32", "1,32,1", "32,1,1"]]
MATRIX += [("mvt", sizes) for sizes in ["1,1", "1,32", "32,1"]]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler-report", required=True, type=Path)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not re.fullmatch("[a-z0-9-]+", args.attempt):
        raise ValueError("Use a new simple attempt name")
    bindings = {}
    build = checked(permitted(ROOT / args.compiler_report), bindings)
    if build["status"] != "built" or not build["verified_membership_constructors_extracted_and_called"]:
        raise ValueError("Expected the verified prefix producer")
    work = ROOT / "build/pruned-double-tiling/unit-matrix-attempts" / args.attempt
    work.mkdir(parents=True, exist_ok=False)
    (work / "script.py").write_bytes(Path(__file__).read_bytes())
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
        row = {"case": case, "tile_sizes": sizes, "command": argv,
               "report": str(report_path.relative_to(ROOT)), "returncode": run.returncode,
               "installed_phase_calls_adaptations": result["installed_phase_calls_adaptations"],
               "native_match": result["native_match"],
               "passed": run.returncode == 0 and report["status"] == "passed" and result["passed"]}
        rows.append(row)
        print(json.dumps(row), flush=True)
    for path in [Path(__file__), probe, *[path for path in work.rglob("*") if path.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {"status": "passed" if all(row["passed"] for row in rows) else "rejected",
              "cases": rows, "all_canonical_rank_three_unit_masks_attempted": True,
              "canonical_rank_two_unit_masks_attempted": True,
              "actual_nonunit_argument_order_retained": True,
              "general_affine_unit_completion_claimed": False,
              "runtime_cost_established": False, "full_goal_complete": False, "bindings": bindings}
    (work / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    if report["status"] != "passed":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
