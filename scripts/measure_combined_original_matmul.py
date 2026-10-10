"""Compare complete original-matmul calls from the same compiled corpus.

This is a small process-CPU diagnostic. It includes initialization and output,
does not pin the CPU, and does not isolate the cost of a runtime guard.
"""
import argparse
import json
from pathlib import Path
import random
import re
import resource
import statistics
import subprocess
import time

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_combined_residual_traced_corpus import checked

SOURCE = ROOT / "build/benchmark-alignment/current-double-combined-residual-quiet-attempts/corpus-v1/report.json"
MODES = ["unmarked", "untiled", "tiled"]


def child_cpu():
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    return usage.ru_utime + usage.ru_stime


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not re.fullmatch("[a-z0-9-]+", args.attempt):
        raise ValueError("Use a new simple attempt")
    bindings = {}
    corpus = checked(SOURCE, bindings)
    row = next(x for x in corpus["results"] if x["case"] == "matmul" and x["variant"] == "original")
    if any(row["configurations"][mode]["status"] != "native_match" for mode in MODES):
        raise ValueError("All three unchanged originals must have matching complete output")
    path_report = ROOT / "build/double-tree-combined-residual/matmul-path-attempts/original-v1/report.json"
    path = checked(path_report, bindings)
    if (path["status"] != "passed" or path["tile_triples"] != path["expected_tile_triples"]
            or path["original_input_sha256"] != row["input_sha256"]):
        raise ValueError("Missing bound observation of actual original-matmul tiling")
    binaries = {mode: permitted(SOURCE.parent / "matmul-original" / mode / "program") for mode in MODES}
    expected = permitted(ROOT / row["original_GCC_reference"]).read_bytes()
    work = ROOT / "build/double-tree-combined-residual/matmul-cost-attempts" / args.attempt
    work.mkdir(parents=True, exist_ok=False)
    (work / "script.py").write_bytes(Path(__file__).read_bytes())
    randomizer = random.Random(20261010)
    samples = []
    for batch in range(7):
        order = list(MODES)
        randomizer.shuffle(order)
        for position, mode in enumerate(order):
            before = child_cpu()
            wall = time.monotonic()
            run = subprocess.run([str(binaries[mode])], capture_output=True, timeout=60)
            elapsed = time.monotonic() - wall
            cpu = child_cpu() - before
            label = f"batch-{batch}-{position}-{mode}"
            (work / (label + ".stdout")).write_bytes(run.stdout)
            (work / (label + ".stderr")).write_bytes(run.stderr)
            samples.append({"batch": batch, "position": position, "mode": mode,
                            "returncode": run.returncode, "cpu_seconds": cpu, "wall_seconds": elapsed,
                            "output_matches_reference": run.returncode == 0 and run.stdout == expected})
    medians = {mode: 1000 * statistics.median(s["cpu_seconds"] for s in samples if s["mode"] == mode)
               for mode in MODES}
    ratios = {mode: statistics.median(
        next(s["cpu_seconds"] for s in samples if s["batch"] == batch and s["mode"] == mode)
        / next(s["cpu_seconds"] for s in samples if s["batch"] == batch and s["mode"] == "unmarked")
        for batch in range(7)) for mode in ["untiled", "tiled"]}
    passed = all(s["output_matches_reference"] for s in samples)
    for file in [Path(__file__), *[p for p in work.iterdir() if p.is_file()]]:
        bindings[str(file.relative_to(ROOT))] = sha(permitted(file))
    report = {"status": "diagnostic_complete" if passed else "rejected", "case": "original-matmul",
              "compiler_entrypoint": corpus["compiler_entrypoint"],
              "whole_program_theorem": corpus["whole_program_theorem"],
              "original_input": row["input"], "original_input_sha256": row["input_sha256"],
              "input_dimensions": [96, 96, 96], "tile_size": 32,
              "source_computation_unchanged": True,
              "baseline": "unmarked source compiled through the same CompCert backend",
              "batches": 7, "random_seed": 20261010, "samples": samples,
              "median_cpu_ms": medians, "paired_ratio_medians": ratios, "all_outputs_match": passed,
              "includes_startup_initialization_kernel_digest_and_printing": True,
              "cpu_pinning": False, "isolated_guard_cost": False,
              "dynamic_guard_refusal_exercised": False,
              "cross_program_or_larger_input_speedup_established": False,
              "full_goal_complete": False, "bindings": bindings}
    (work / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "matching_calls": sum(s["output_matches_reference"] for s in samples),
                      "median_cpu_ms": medians, "paired_ratio_medians": ratios}), flush=True)
    if not passed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
