"""Measure complete column-traversal tensor calls and diagnose the emitted guard separately.

Each batch validates the accumulated RMW result at its actual repetition count.
No array reset or diagnostic counter is added to the measured compiler assembly.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
import os
import platform
import random
import re
import statistics
import subprocess
import time

from audit_interface_clight import ROOT, sha
import native_tensor_affine_region as native
from native_nested_compact_cost import instrument_decisions
from native_memory_layout_sequence_paths import printer_for_gcc

WORK = ROOT / "build/tensor-affine-region/cost"
SOURCE = WORK / "cost.c"
MODES = ["disabled", "identity", "interchange", "tile-2-3"]
CASES = [(0, 3, 31, 2, 5, 7), (0, 31, 31, 31, 5, 7),
         (0, 31, 1024, 31, 5, 2**31-1), (0, 32, 31, 2, 5, -2),
         (1, 31, 31, 31, 5, 7), (0, 0, 1001, 99, 99, 2**31-1),
         (0, 31, 31, 31, 0, 7), (0, 1, 2048, 2, 5, 7)]
CASE_NAMES = ["small-accepted", "dense-accepted", "conflict-strided-wrapped-accepted",
              "coordinate-refusal", "nonzero-root-refusal", "empty-outer-null",
              "empty-inner", "stride-profile-refusal"]
SIZE, CENTER = 160000, 128
ROUNDS, SEED, TARGET_SECONDS = 30, 20261007, 0.1
HELPERS = list(dict.fromkeys(["scripts/native_tensor_affine_region_cost.py",
    "scripts/native_nested_compact_cost.py", *native.HELPERS]))


def digest_text(text):
    return hashlib.sha256(text.encode()).hexdigest()


def source_text():
    # Preserve the same single-site function used by the native matrix.
    prefix = native.source_text().split("void tensor_twice(", 1)[0]
    rows = ",\n".join("{"+",".join(map(native.literal, row))+"}" for row in CASES)
    return prefix+'''
#include <stdlib.h>
#include <time.h>
int A[160000],which,start,n,ld,columns,components,alpha;
int inputs[][6]={
'''+rows+'''};
void initialize(int selected){int x;which=selected;start=inputs[which][0];n=inputs[which][1];
ld=inputs[which][2];columns=inputs[which][3];components=inputs[which][4];alpha=inputs[which][5];
for(x=0;x<160000;x++)A[x]=3*x+1;tensor_pre=100;tensor_post=200;}
void invoke(void){tensor_single(n==0?0:A+128,n,ld,columns,components,alpha,start);}
void show(void){int x;printf("RESULT %d %d %d %d %d %d %d %d %d",which,tensor_i,tensor_j,tensor_k,
tensor_first_i,tensor_first_j,tensor_first_k,tensor_pre,tensor_post);
for(x=0;x<160000;x++)printf(" %d",A[x]);printf("\\n");}
int main(int argc,char**argv){int repetitions,r;clock_t before,after;
if(argc!=3)return 2;which=atoi(argv[1]);repetitions=atoi(argv[2]);
if(which<0||which>='''+str(len(CASES))+'''||repetitions<1)return 3;
initialize(which);invoke();show();before=clock();
for(r=0;r<repetitions;r++)invoke();after=clock();
printf("TIME %d %lu %lu\\n",repetitions,(unsigned long)(after-before),(unsigned long)CLOCKS_PER_SEC);
show();return 0;}
'''


@lru_cache(maxsize=None)
def source_effect(case):
    start, n, ld, columns, components, _alpha = CASES[case]
    public = [start, 77, 88]
    counts = Counter()
    while public[0] < n:
        public[1] = 0
        while public[1] < columns:
            public[2] = 0
            while public[2] < components:
                i, j, k = public
                index = CENTER+native.word(native.word(native.word(j*ld)+i)*5+k)
                assert 0 <= index < SIZE, (case, index)
                counts[index] += 1
                public[2] += 1
            public[1] += 1
        public[0] += 1
    return public, counts


@lru_cache(maxsize=64)
def expected_result(case, calls):
    public, counts = source_effect(case)
    alpha = CASES[case][5]
    array = [native.word(3*x+1+calls*alpha*counts[x]) for x in range(SIZE)]
    words = [case, *public, *public, native.word(100+7*calls), native.word(200+11*calls), *array]
    return "RESULT "+" ".join(map(str, words))


def expected_accept(case):
    start, n, ld, columns, components, _alpha = CASES[case]
    return start == 0 and 1 <= n <= 32 and 1 <= columns <= 32 and 1 <= components <= 5 and 1 <= ld < 2048 and n <= ld


def sample(mode, case, repetitions, cpu):
    command = [str(WORK/mode/"program"), str(case), str(repetitions)]
    if cpu is not None:
        command = ["taskset", "-c", str(cpu), *command]
    lines = subprocess.check_output(command, text=True, timeout=60).splitlines()
    assert len(lines) == 3 and lines[1].startswith("TIME "), (mode, case)
    warm, final = expected_result(case, 1), expected_result(case, repetitions+1)
    assert lines[0] == warm and lines[2] == final, (mode, case, "memory/public mismatch")
    count, ticks, frequency = map(int, lines[1].split()[1:])
    assert count == repetitions and ticks >= 0 and frequency > 0
    return {"repetitions": count, "cpu_ticks": ticks, "ticks_per_second": frequency,
            "cpu_seconds": ticks/frequency, "ns_per_call": 1e9*ticks/frequency/count,
            "warmup_result_sha256": digest_text(warm), "final_result_sha256": digest_text(final)}


def compile_one(mode):
    directory = WORK/mode
    directory.mkdir(parents=True, exist_ok=True)
    env = {k: v for k, v in os.environ.items() if not k.startswith("GUARDCERT_")}
    env.update(GUARDCERT_TENSOR_MODE=mode, GUARDCERT_TENSOR_DIAGNOSTICS="1",
               GUARDCERT_TENSOR_CAP="32", GUARDCERT_TENSOR_STRIDE_HIGH="2048")
    started = time.monotonic()
    with (directory/"compile.log").open("w") as out:
        subprocess.run([str(native.COMPILER), "-conf", str(native.COMPILER.parent/"compcert.ini"),
                        "-stdlib", str(native.COMPILER.parent/"runtime"), "-dclight", "-S", "-o",
                        str(directory/"program.s"), str(SOURCE)], cwd=directory, env=env,
                       stdout=out, stderr=subprocess.STDOUT, check=True, timeout=300)
    compile_seconds = time.monotonic()-started
    started = time.monotonic()
    subprocess.run(["gcc", "-no-pie", str(directory/"program.s"), "-o", str(directory/"program")],
                   capture_output=True, check=True)
    link_seconds = time.monotonic()-started
    body = native.function_body((directory/"cost.light.c").read_text(), "tensor_single")
    assert len(list(native.dispatch_sites(body))) == int(mode != "disabled"), mode
    assert re.search(r"\bcall\s+tensor_single\b", (directory/"program.s").read_text()), "call boundary was inlined"
    print("Compiled", mode, flush=True)
    return {"compile_wall_seconds": compile_seconds, "link_wall_seconds": link_seconds,
            "kernel_bytes": native.machine_bytes(directory/"program", "tensor_single"),
            "artifacts": {name: sha(directory/name) for name in ["program.s", "program", "cost.light.c", "compile.log"]}}


def guard_diagnostic(mode):
    directory = WORK/mode
    dump = (directory/"cost.light.c").read_text()
    main = re.search(r"^int main\([^;\n]*\)\n\{", dump, re.MULTILINE)
    assert main
    prefix = re.sub(r"^int main\([^;\n]*\);\n", "", dump[:main.start()], flags=re.MULTILINE)
    repaired = printer_for_gcc(prefix+"\nint main(void)\n{\nreturn 0;\n}\n")
    body = native.function_body(repaired, "tensor_single")
    sites = list(native.dispatch_sites(body))
    assert len(sites) == 1, mode
    opening, _fallback = sites[0]
    last = body.rfind("if (", 0, opening)
    answer = re.fullmatch(r"if \((\$[0-9]+)\) \{", body[last:opening+1]).group(1)
    actual_prefix = body[:last]
    assert "for (" not in actual_prefix and "while (" not in actual_prefix, "unexpected guard scan"
    assert not re.search(r"\*\s*\(\s*\$a\b|\*\s*\$a\b", actual_prefix), "unexpected input-array probe"
    marked, decisions = instrument_decisions(actual_prefix)
    derivative = repaired.replace(body, marked+f"guard_answer={answer};\n", 1)
    derivative = "unsigned long guard_decisions;int guard_answer;\n"+derivative
    derivative += "\nint main(void){int selected,x,unchanged;for(selected=0;selected<"+str(len(CASES))+";selected++){"+ \
        'initialize(selected);guard_decisions=0;invoke();unchanged=1;for(x=0;x<160000;x++)if(A[x]!=3*x+1)unchanged=0;' + \
        'printf("GUARD %d %d %lu %d %d %d\\n",selected,guard_answer,guard_decisions,unchanged,tensor_pre,tensor_post);}' + \
        'return 0;}\n'
    path = directory/"guard-diagnostic.c"
    path.write_text(derivative)
    subprocess.run(["gcc", "-O0", "-fwrapv", "-Wno-builtin-declaration-mismatch", "-Wno-discarded-qualifiers",
                    str(path), "-o", str(directory/"guard-diagnostic")], check=True, capture_output=True)
    output = subprocess.check_output([str(directory/"guard-diagnostic")], text=True, timeout=60)
    (directory/"guard-diagnostic.txt").write_text(output)
    lines = output.splitlines()
    assert len(lines) == len(CASES)
    actual = []
    for case, line in enumerate(lines):
        index, accepted, dynamic, unchanged, pre, post = map(int,line.split()[1:])
        assert index == case and accepted == int(expected_accept(case)) and unchanged == 1
        assert [pre, post] == [107, 200], "unexpected prefix context effect"
        actual.append({"case": case, "accepted": bool(accepted), "if_decisions": dynamic,
                       "source_point_count": sum(source_effect(case)[1].values())})
    return {"dynamic": actual, "static_if_sites": decisions, "guard_loops": 0, "input_array_load_sites": 0,
            "production_assembly": False, "scope": "guard prefix if-condition evaluations; excludes final dispatch and machine-operation counts",
            "artifacts": {name: sha(directory/name) for name in ["guard-diagnostic.c", "guard-diagnostic", "guard-diagnostic.txt"]}}


def bindings():
    return {"policy_environment": {"GUARDCERT_TENSOR_CAP": "32", "GUARDCERT_TENSOR_STRIDE_HIGH": "2048"},
            "compiler_sha256": sha(native.COMPILER), "compiler_stamp_sha256": sha(native.COMPILER.parent/".guard-build.json"),
            "proof_report_sha256": sha(native.PROOF), "native_report_sha256": sha(native.WORK/"report.json"),
            "source_sha256": sha(SOURCE), "helper_sources": {name: sha(ROOT/name) for name in HELPERS},
            "toolchain_lock_sha256": sha(ROOT/"toolchain.lock.json")}


def summaries(samples):
    rows = {}
    for case in range(len(CASES)):
        rows[str(case)] = {}
        source = {s["round"]: s["ns_per_call"] for s in samples if s["case"] == case and s["mode"] == "disabled"}
        for mode in MODES:
            selected = [s for s in samples if s["case"] == case and s["mode"] == mode]
            values = [s["ns_per_call"] for s in selected]
            quartiles = statistics.quantiles(values, n=4, method="inclusive")
            rows[str(case)][mode] = {"median_ns_per_call": statistics.median(values),
                "iqr_ns_per_call": quartiles[2]-quartiles[0],
                "median_paired_cost_over_source": statistics.median(s["ns_per_call"]/source[s["round"]] for s in selected)}
    return rows


def validate_configurations(configurations):
    assert set(configurations) == set(MODES)
    for mode, facts in configurations.items():
        directory = WORK/mode
        for name, digest in (facts["artifacts"] | facts.get("guard_diagnostic", {}).get("artifacts", {})).items():
            assert sha(directory/name) == digest, (mode, name)
        assert facts["kernel_bytes"] == native.machine_bytes(directory/"program", "tensor_single")
        if mode != "disabled":
            assert facts["guard_diagnostic"]["dynamic"] == configurations["identity"]["guard_diagnostic"]["dynamic"]
            assert not facts["guard_diagnostic"]["production_assembly"]
    assert SOURCE.read_text() == source_text()


def validate(report):
    native.validate(json.loads((native.WORK/"report.json").read_text()))
    assert report["status"] == "measured" and report["bindings"] == bindings()
    assert report["cases"] == [list(row) for row in CASES]
    validate_configurations(report["configurations"])
    samples = [json.loads(line) for line in (WORK/"samples.jsonl").read_text().splitlines()]
    assert report["samples_sha256"] == sha(WORK/"samples.jsonl") and report["samples"] == len(samples)
    assert report["summaries"] == summaries(samples)
    assert {(s["case"], s["mode"], s["round"]) for s in samples} == {(c, m, r) for c in range(len(CASES)) for m in MODES for r in range(ROUNDS)}
    for item in samples:
        assert item["cpu_seconds"] >= TARGET_SECONDS/2
        case, count = item["case"], item["repetitions"]
        assert item["warmup_result_sha256"] == digest_text(expected_result(case, 1))
        assert item["final_result_sha256"] == digest_text(expected_result(case, count+1))


def prepare():
    assert not (WORK/"report.json").exists(), "Refusing to replace an existing timing report"
    WORK.mkdir(parents=True, exist_ok=True)
    SOURCE.write_text(source_text())
    configs = {mode: compile_one(mode) for mode in MODES}
    for mode in MODES[1:]:
        configs[mode]["guard_diagnostic"] = guard_diagnostic(mode)
    validate_configurations(configs)
    (WORK/"prepared.json").write_text(json.dumps({"bindings": bindings(), "configurations": configs},indent=2)+"\n")
    print("All compilers and guard diagnostics prepared", flush=True)


def measure():
    assert not (WORK/"report.json").exists(), "Refusing to replace an existing timing report"
    prepared = json.loads((WORK/"prepared.json").read_text())
    assert prepared["bindings"] == bindings()
    configs = prepared["configurations"]
    validate_configurations(configs)
    cpus = sorted(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else []
    cpu = cpus[0] if cpus else None
    repetitions, calibration = {}, []
    for case in range(len(CASES)):
        for mode in MODES:
            count = 1000
            for _ in range(8):
                trial = sample(mode, case, count, cpu)
                calibration.append({"case": case, "mode": mode, **trial})
                if trial["cpu_seconds"] >= TARGET_SECONDS:
                    break
                count = min(100000000, max(count*2, int(count*(TARGET_SECONDS*1.2)/max(trial["cpu_seconds"], 1e-6))))
            else:
                raise AssertionError((case, mode, "calibration failed"))
            repetitions[(case, mode)] = count
        print("Calibrated case", case, flush=True)
    rng = random.Random(SEED)
    samples = []
    with (WORK/"samples.jsonl").open("w") as raw:
        for round_id in range(ROUNDS):
            order = [(c, m) for c in range(len(CASES)) for m in MODES]
            rng.shuffle(order)
            for sequence, (case, mode) in enumerate(order):
                result = sample(mode, case, repetitions[(case, mode)], cpu)
                assert result["cpu_seconds"] >= TARGET_SECONDS/2, (case, mode, "batch shorter than protocol minimum")
                item = {"round": round_id, "order": sequence, "case": case, "mode": mode, **result}
                raw.write(json.dumps(item)+"\n"); raw.flush(); samples.append(item)
            print("Timing round", round_id+1, "/", ROUNDS, flush=True)
    report = {"status": "measured", "bindings": bindings(), "cases": [list(row) for row in CASES], "case_names": CASE_NAMES,
        "protocol": {"rounds": ROUNDS, "seed": SEED, "target_batch_cpu_seconds": TARGET_SECONDS,
            "minimum_batch_cpu_seconds": TARGET_SECONDS/2, "fresh_process_per_batch": True, "pinned_cpu": cpu,
            "clock": "C clock() process CPU time", "warmup_calls": 1, "array_reset_per_call": False,
            "array_initialization_and_validation_timed": False, "accumulated_result_checked_at_actual_call_count": True},
        "environment": {"platform": platform.platform(), "available_cpus": cpus,
            "cpu_model": next((line.split(":",1)[1].strip() for line in open("/proc/cpuinfo") if line.startswith("model name")), "unknown"),
            "gcc": subprocess.check_output(["gcc","--version"],text=True).splitlines()[0]},
        "configurations": configs, "calibration": calibration, "samples": len(samples),
        "samples_sha256": sha(WORK/"samples.jsonl"), "summaries": summaries(samples),
        "scope": "one actual column-traversal Horner RMW source; count cap 32 and stride profile below 2048; exploratory complete-call measurement",
        "limitations": ["warm repeated input; no representative workload acceptance frequency or benchmark speedup claim",
            "Clight diagnostic decisions are not production machine-operation counts",
            "complete-call differences include guard, candidate lowering, public exits and backend layout",
            "no confidence intervals or break-even inference; compiler time excludes proof/extraction setup"]}
    validate(report)
    (WORK/"report.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"status":"measured", "samples":len(samples), "report_sha256":sha(WORK/"report.json")}), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate",action="store_true")
    parser.add_argument("--prepare",action="store_true")
    parser.add_argument("--measure",action="store_true")
    args = parser.parse_args()
    assert sum([args.validate,args.prepare,args.measure]) <= 1
    native.validate(json.loads((native.WORK/"report.json").read_text()))
    if args.validate:
        validate(json.loads((WORK/"report.json").read_text()))
        print(json.dumps({"status":"validated", "report_sha256":sha(WORK/"report.json")}))
    elif args.prepare:
        prepare()
    elif args.measure:
        measure()
    else:
        prepare(); measure()


if __name__ == "__main__":
    main()
