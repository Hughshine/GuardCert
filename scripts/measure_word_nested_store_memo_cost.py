"""Measure complete loaded-loop calls from frozen prepared compiler outputs.

Thirty randomized paired rounds use unmodified CompCert assembly. Every warmup
and final full-memory/public output is checked with the preparation's modular
repeat oracle. Keep all observations, including regressions and outliers.
"""
import argparse
import json
import os
from pathlib import Path
import platform
import random
import statistics
import subprocess

from audit_interface_clight import ROOT, sha
import prepare_word_nested_store_memo_cost as prepared

WORK = ROOT / "build/multi-word-nested-memo/cost-v1"
PREPARED = prepared.WORK
ROUNDS = 30
SEED = 20261008
TARGET_SECONDS = 0.1
MINIMUM_SECONDS = 0.05


def summaries(samples):
    result = {}
    for profile in prepared.PROFILES:
        result[profile] = {}
        for case in prepared.CASES:
            result[profile][case] = {}
            pairs = {mode: {item["round"]: item["ns_per_call"] for item in samples
                     if item["profile"] == profile and item["case"] == case and item["mode"] == mode}
                     for mode in prepared.MODES}
            for mode in prepared.MODES:
                values = list(pairs[mode].values())
                quartiles = statistics.quantiles(values, n=4, method="inclusive")
                ratios = [pairs[mode][r] / pairs["source"][r] for r in range(ROUNDS)]
                result[profile][case][mode] = {"median_ns_per_call": statistics.median(values),
                    "iqr_ns_per_call": quartiles[2] - quartiles[0],
                    "median_paired_cost_over_source": statistics.median(ratios)}
            ratios = [pairs["memo"][r] / pairs["shared"][r] for r in range(ROUNDS)]
            quartiles = statistics.quantiles(ratios, n=4, method="inclusive")
            result[profile][case]["memo_over_shared"] = {"median": statistics.median(ratios),
                "iqr": quartiles[2] - quartiles[0]}
    return result


def validate(work=WORK):
    parent = prepared.validate(PREPARED)
    report = json.loads((work / "report.json").read_text())
    assert report["status"] == "measured" and report["prepared_report_sha256"] == sha(PREPARED / "report.json")
    assert report["cases"] == parent["cases"] and report["profiles"] == parent["profiles"]
    assert report["protocol"]["rounds"] == ROUNDS and report["protocol"]["seed"] == SEED
    for path, digest in report["bindings"].items():
        assert sha(ROOT / path) == digest, path
    samples = [json.loads(line) for line in (work / "samples.jsonl").read_text().splitlines()]
    assert report["samples"] == len(samples) and report["summaries"] == summaries(samples)
    assert {(s["profile"], s["case"], s["mode"], s["round"]) for s in samples} == \
        {(p, c, m, r) for p in prepared.PROFILES for c in prepared.CASES for m in prepared.MODES for r in range(ROUNDS)}
    assert len(samples) == len(prepared.PROFILES) * len(prepared.CASES) * len(prepared.MODES) * ROUNDS
    for item in [*report["calibration"], *samples]:
        lines = (ROOT / item["output_path"]).read_text().splitlines()
        assert len(lines) == 3 and lines[1].startswith("TIME ")
        count, ticks, frequency = map(int, lines[1].split()[1:])
        assert [count, ticks, frequency] == [item["repetitions"], item["cpu_ticks"], item["ticks_per_second"]]
        assert lines[0] == prepared.expected(item["profile"], item["case"], 1)
        assert lines[2] == prepared.expected(item["profile"], item["case"], count + 1)
        assert item["cpu_seconds"] == ticks / frequency
        assert item["ns_per_call"] == 1e9 * ticks / frequency / count
    for item in samples:
        assert item["cpu_seconds"] >= MINIMUM_SECONDS
    return report


def main():
    global WORK, PREPARED
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, default=WORK)
    parser.add_argument("--prepared", type=Path, default=PREPARED)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    WORK, PREPARED = args.work.resolve(), args.prepared.resolve()
    assert WORK.is_relative_to(ROOT / "build/multi-word-nested-memo")
    assert PREPARED.is_relative_to(ROOT / "build/multi-word-nested-memo")
    if args.validate or (WORK / "report.json").exists():
        report = validate(WORK)
        print(json.dumps({"status": "validated", "samples": report["samples"],
                          "report_sha256": sha(WORK / "report.json")}))
        return
    assert not WORK.exists(), "Refusing to overwrite timing observations"
    parent = prepared.validate(PREPARED)
    parent_digest = sha(PREPARED / "report.json")
    WORK.mkdir()
    (WORK / "outputs").mkdir()
    cpus = sorted(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else []
    cpu = cpus[0] if cpus else None
    batches = [(p, c, m) for p in prepared.PROFILES for c in prepared.CASES for m in prepared.MODES]
    calibration, repetitions, samples = [], {}, []
    try:
        for profile, case, mode in batches:
            count = 1000
            for attempt in range(8):
                output = WORK / "outputs" / f"cal-{profile}-{case}-{mode}-{attempt}.txt"
                trial = prepared.sample(PREPARED, profile, mode, case, count, cpu, output)
                calibration.append({"profile": profile, "case": case, "mode": mode,
                    "output_path": str(output.relative_to(ROOT)), **trial})
                if trial["cpu_seconds"] >= TARGET_SECONDS:
                    break
                count = min(100000000, max(count * 2,
                    int(count * TARGET_SECONDS * 1.3 / max(trial["cpu_seconds"], 1e-6))))
            else:
                raise AssertionError((profile, case, mode, "Calibration below protocol target"))
            repetitions[(profile, case, mode)] = count
            print(json.dumps({"profile": profile, "case": case, "mode": mode,
                              "status": "calibrated", "ns_per_call": trial["ns_per_call"]}), flush=True)
        rng = random.Random(SEED)
        with (WORK / "samples.jsonl").open("x") as raw:
            for round_id in range(ROUNDS):
                order = list(batches)
                rng.shuffle(order)
                for sequence, (profile, case, mode) in enumerate(order):
                    output = WORK / "outputs" / f"round-{round_id}-order-{sequence}.txt"
                    item = {"profile": profile, "case": case, "mode": mode, "round": round_id,
                            "order": sequence, "output_path": str(output.relative_to(ROOT)),
                            **prepared.sample(PREPARED, profile, mode, case,
                                repetitions[(profile, case, mode)], cpu, output)}
                    # Retain the observation even if it violates the minimum;
                    # fail the protocol rather than deleting a fast sample.
                    raw.write(json.dumps(item) + "\n")
                    raw.flush()
                    samples.append(item)
                    assert item["cpu_seconds"] >= MINIMUM_SECONDS, (profile, case, mode, "Short batch")
                print(json.dumps({"status": "measuring", "round": round_id + 1, "rounds": ROUNDS}), flush=True)
    except Exception as error:
        (WORK / "failure.json").write_text(json.dumps({"status": "failed", "error": repr(error),
            "calibration_count": len(calibration), "completed_samples": len(samples)}, indent=2) + "\n")
        raise
    assert parent_digest == sha(PREPARED / "report.json")
    prepared.validate(PREPARED)
    bindings = {PREPARED / "report.json": parent_digest, Path(__file__): sha(Path(__file__)),
                ROOT / "scripts/prepare_word_nested_store_memo_cost.py": sha(ROOT / "scripts/prepare_word_nested_store_memo_cost.py")}
    bindings |= {path: sha(path) for path in WORK.rglob("*") if path.is_file()}
    report = {"status": "measured", "prepared_report": str((PREPARED / "report.json").relative_to(ROOT)),
              "prepared_report_sha256": parent_digest, "cases": parent["cases"], "profiles": parent["profiles"],
              "configurations": parent["configurations"], "calibration": calibration,
              "samples": len(samples), "summaries": summaries(samples),
              "protocol": {"rounds": ROUNDS, "seed": SEED, "target_batch_cpu_seconds": TARGET_SECONDS,
                  "minimum_batch_cpu_seconds": MINIMUM_SECONDS, "fresh_process_per_batch": True,
                  "pinned_cpu": cpu, "clock": "C clock() process CPU time", "warmup_calls": 1,
                  "inclusive_per_call_header_reset": True, "all_compiler_guard_and_region_code_included": True,
                  "array_initialization_and_output_validation_timed": False,
                  "independent_repetition_calibration_per_mode": True, "discarded_samples": 0},
              "environment": {"platform": platform.platform(), "available_cpus": cpus,
                  "cpu_model": next((line.split(":", 1)[1].strip() for line in Path("/proc/cpuinfo").read_text().splitlines()
                                     if line.startswith("model name")), "unknown"),
                  "gcc": subprocess.check_output(["gcc", "--version"], text=True).splitlines()[0]},
              "scope": "Three warm loaded rectangular two-store kernels, nine selected inputs; source versus shared setup and readonly probe elimination",
              "new_compiler_or_semantic_theorem": False, "representative_workload_speedup_claim": False,
              "general_affine_domain_coverage_added": False, "full_goal_complete": False,
              "limitations": ["Selected warm inputs and fixed profile cap eight; not workload frequencies or representative benchmark speedups",
                  "Process CPU time with affinity; no core isolation or confidence interval",
                  "Modes have independently calibrated repetition counts; arrays change modularly without changing branch decisions",
                  "Guard if-counts are separate GCC Clight diagnostics, not timed assembly operation counts",
                  "Compile time uses already built compilers; proof and extraction setup excluded"],
              "bindings": {str(path.relative_to(ROOT)): digest for path, digest in bindings.items()}}
    with (WORK / "report.json").open("x") as out:
        out.write(json.dumps(report, indent=2) + "\n")
    validate(WORK)
    print(json.dumps({"status": "measured", "samples": report["samples"],
                      "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
