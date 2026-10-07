"""Measure complete kernel calls and count decisions in the actual guard.

Timing uses unmodified compiler assembly, including capture, dispatch, the
candidate/fallback, public exits and per-call header reset. Diagnostic counters
use a GCC build of the printed Clight guard prefix and are recorded separately.
Historical proof/native reports are inputs with checked hashes, never replaced.
"""
import argparse
import json
import os
import platform
import random
import re
import statistics
import subprocess
import time

from audit_interface_clight import ROOT, sha
from native_memory_layout_sequence_paths import printer_for_gcc
import native_nested_stability_large as fixture

WORK = ROOT / "build/nested-stability-shared/cost"
SOURCE = WORK / "cost.c"
MODES = ["disabled", "identity", "interchange", "tile-2-3", "legacy-interchange"]
CASE_IDS = [0, 1, 2, 3, 4, 6, 7, 9]
CASES = [fixture.CASES[i] for i in CASE_IDS]
HELPERS = list(dict.fromkeys(["scripts/native_nested_stability_cost.py", *fixture.HELPERS]))
SEED = 20261007
ROUNDS = 30
TARGET_SECONDS = 0.2


def source_text():
    prefix = fixture.source_text().split("void nested_case(", 1)[0]
    rows = ",\n".join("{" + ",".join(map(fixture.native.coverage.literal, row)) + "}" for row in CASES)
    return prefix + """
#include <stdlib.h>
#include <time.h>
int A[6144],B[2048],C[2048],dims[2],single[1];
int *a,*b,*c,*shape;
int selected,view,start,u,v,alpha;
int inputs[][7]={
""" + rows + """};
void reset_headers(void){shape[0]=u;if(view!=7)shape[1]=v;}
void initialize(int which){int x;selected=which;view=inputs[which][1];start=inputs[which][2];
u=inputs[which][3];v=inputs[which][4];alpha=inputs[which][5];
for(x=0;x<6144;x++)A[x]=3*x+1;
for(x=0;x<2048;x++){B[x]=3*x+18;C[x]=3*x+35;}
a=A+128;b=B+128;c=C+128;shape=dims;
if(view==1)shape=a;if(view==2)shape=a+5;
if(view==7){shape=single;a=0;b=0;c=0;}
if(view==8){a=0;b=0;c=0;}
nc_pre=100;nc_post=200;reset_headers();}
void show(void){int x;
printf("RESULT %d %d %d %d %d %d %d %d %d %d %d %d %d %d",3,view,start,u,v,alpha,1,
nc_row,nc_column,nc_component,nc_pre,nc_post,shape[0],view==7?99:shape[1]);
for(x=0;x<6144;x++)printf(" %d",A[x]);
for(x=0;x<2048;x++)printf(" %d",B[x]);
for(x=0;x<2048;x++)printf(" %d",C[x]);printf("\\n");}
int main(int argc,char **argv){int r,count,which;clock_t before,after;
if(argc!=3)return 2;which=atoi(argv[1]);count=atoi(argv[2]);
if(which<0 || which>=""" + str(len(CASES)) + """ || count<1)return 3;
initialize(which);nested_write(a,b,c,shape,start,alpha,1);show();
before=clock();for(r=0;r<count;r++){reset_headers();nested_write(a,b,c,shape,start,alpha,1);}
after=clock();printf("TIME %d %lu %lu\\n",count,(unsigned long)(after-before),(unsigned long)CLOCKS_PER_SEC);
show();return 0;}
"""


def environment(mode):
    actual = "interchange" if mode == "legacy-interchange" else mode
    return {k: v for k, v in os.environ.items() if not k.startswith("GUARDCERT_")} | {
        "GUARDCERT_AFFINE_MODE": actual, "GUARDCERT_AFFINE_CAP": "16",
        "GUARDCERT_AFFINE_BOUND_LOW": "1", "GUARDCERT_AFFINE_BOUND_HIGH": "17",
        "GUARDCERT_AFFINE_DIAGNOSTICS": "1"}


def compile_one(mode):
    compiler = fixture.native.LEGACY if mode.startswith("legacy") else fixture.native.COMPILER
    directory = WORK / mode
    directory.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    with (directory / "compile.log").open("w") as log:
        subprocess.run([str(compiler), "-conf", str(compiler.parent / "compcert.ini"), "-stdlib",
                        str(compiler.parent / "runtime"), "-dclight", "-S", "-o",
                        str(directory / "program.s"), str(SOURCE)], cwd=directory,
                       env=environment(mode), stdout=log, stderr=subprocess.STDOUT, check=True, timeout=300)
    compile_seconds = time.monotonic() - started
    started = time.monotonic()
    subprocess.run(["gcc", "-no-pie", str(directory / "program.s"), "-o", str(directory / "program")],
                   capture_output=True, check=True)
    link_seconds = time.monotonic() - started
    body = fixture.native.coverage.function_body((directory / "cost.light.c").read_text(), "nested_write")
    assert (body.count("for (") > 3) == (mode != "disabled"), mode
    print("Compiled", mode, flush=True)
    return {"compiler_sha256": sha(compiler), "compile_wall_seconds": compile_seconds,
            "link_wall_seconds": link_seconds, "kernel_bytes": fixture.native.frontend.machine_bytes(directory / "program", "nested_write"),
            "artifacts": {p: sha(directory / p) for p in ["program.s", "program", "cost.light.c", "compile.log"]}}


def sample(mode, case, repetitions, cpu):
    command = [str(WORK / mode / "program"), str(case), str(repetitions)]
    if cpu is not None:
        command = ["taskset", "-c", str(cpu), *command]
    output = subprocess.check_output(command, text=True, timeout=60)
    lines = output.splitlines()
    assert len(lines) == 3 and lines[1].startswith("TIME "), (mode, case, lines[:2])
    expected = "RESULT " + fixture.run_model(CASES[case])[0].strip()
    assert lines[0] == lines[2] == expected, (mode, case, "full memory/public mismatch")
    count, ticks, frequency = map(int, lines[1].split()[1:])
    assert count == repetitions and ticks >= 0 and frequency > 0
    return {"repetitions": count, "cpu_ticks": ticks, "ticks_per_second": frequency,
            "cpu_seconds": ticks / frequency, "ns_per_call": 1e9 * ticks / frequency / count,
            "warmup_and_final_result_sha256": sha_text(expected)}


def sha_text(text):
    import hashlib
    return hashlib.sha256(text.encode()).hexdigest()


def guard_prefix(dump):
    main = re.search(r"^int main\([^;\n]*\)\n\{", dump, re.MULTILINE)
    assert main
    prefix = re.sub(r"^int main\([^;\n]*\);\n", "", dump[:main.start()], flags=re.MULTILINE)
    repaired = printer_for_gcc(prefix + "\nint main(void)\n{\nreturn 0;\n}\n")
    body = fixture.native.coverage.function_body(repaired, "nested_write")
    choices = list(re.finditer(r"if \((\$[0-9]+)\) \{", body))
    assert choices
    last = choices[-1]
    prefix = body[:last.start()]
    # The final choice is the actual source/candidate dispatch. Inspect its
    # balanced block and require an else containing the original loaded loop.
    opening = body.index("{", last.start())
    depth, closing = 1, opening + 1
    while depth:
        depth += (body[closing] == "{") - (body[closing] == "}")
        closing += 1
    assert re.match(r"\s*else\s*\{", body[closing:])
    assert "$shape" in body[closing:] and "15" in body[closing:]
    return repaired, body, prefix, last.group(1)


def instrument_decisions(code):
    # Instrument every if-condition in the guard, including loop exit and
    # refusal tests. Balanced parentheses avoid truncating address expressions.
    result, position, sites = [], 0, 0
    while True:
        match = re.search(r"\bif\s*\(", code[position:])
        if match is None:
            result.append(code[position:])
            break
        opening = position + match.end() - 1
        result.append(code[position:opening+1])
        depth, closing = 1, opening+1
        while depth:
            depth += (code[closing] == "(") - (code[closing] == ")")
            closing += 1
        expression = code[opening+1:closing-1]
        result.append("(++guard_decisions, (" + expression + "))")
        result.append(")")
        position, sites = closing, sites+1
    return "".join(result), sites


def guard_diagnostic(mode):
    directory = WORK / mode
    repaired, body, prefix, answer = guard_prefix((directory / "cost.light.c").read_text())
    marked, sites = instrument_decisions(prefix)
    marked, loads = re.subn(r"\*\$shape(?:__[0-9]+)?\b|\*\(\$shape(?:__[0-9]+)? \+ 1\)",
                            lambda m: "(++guard_loads, " + m[0] + ")", marked)
    assert loads == 2, (mode, loads)
    derivative = repaired.replace(body, marked + f"guard_answer={answer};\n", 1)
    derivative = "unsigned long guard_decisions,guard_loads;int guard_answer;\n" + derivative
    # The diagnostic stops before candidate/fallback and checks the result and
    # that no input memory changed. It is not the certified production output.
    derivative += "\nint main(void){int which;for(which=0;which<" + str(len(CASES)) + ";which++){" + \
        'initialize(which);guard_decisions=guard_loads=0;nested_write(a,b,c,shape,start,alpha,1);' + \
        'printf("GUARD %d %d %lu %lu %d %d\\n",which,guard_answer,guard_decisions,guard_loads,shape[0],view==7?99:shape[1]);' + \
        'show();}return 0;}\n'
    path = directory / "guard-diagnostic.c"
    path.write_text(derivative)
    subprocess.run(["gcc", "-O0", "-fwrapv", "-Wno-builtin-declaration-mismatch", "-Wno-discarded-qualifiers",
                    str(path), "-o", str(directory / "guard-diagnostic")], capture_output=True, check=True)
    output = subprocess.check_output([str(directory / "guard-diagnostic")], text=True, timeout=60)
    (directory / "guard-diagnostic.txt").write_text(output)
    actual = []
    initial_arrays = [fixture.native.coverage.word(3*x+1) for x in range(6144)] + \
        [fixture.native.coverage.word(3*x+18) for x in range(2048)] + \
        [fixture.native.coverage.word(3*x+35) for x in range(2048)]
    lines = output.splitlines()
    assert len(lines) == 2*len(CASES)
    for case, row in enumerate(CASES):
        fields = list(map(int, lines[2*case].split()[1:]))
        index, accepted, decisions, header_loads, root, child = fields
        assert index == case and [root, child] == [row[3], 99 if row[1] == 7 else row[4]]
        expected_accept = fixture.expected_dispatch(mode, row)[0]
        if mode.startswith("legacy") and row[1] in [1, 2]:
            expected_accept = 0
        assert accepted == expected_accept and header_loads == (1 if row[1] == 7 else 0 if row[2] else 2), fields
        observed = list(map(int, lines[2*case+1].split()[1:]))
        expected_arrays = list(initial_arrays)
        if row[1] in [1, 2]:
            offset = 128 + (0 if row[1] == 1 else 5)
            expected_arrays[offset:offset+2] = list(row[3:5])
        assert observed[14:] == expected_arrays, (mode, case, "guard changed memory")
        actual.append({"case": case, "accepted": bool(accepted), "if_decisions": decisions, "header_loads": header_loads})
    return {"dynamic": actual, "static_if_sites": sites, "static_header_load_sites": loads,
            "production_assembly": False, "scope": "all if-condition evaluations in guard prefix; not all machine operations",
            "artifacts": {p: sha(directory / p) for p in ["guard-diagnostic.c", "guard-diagnostic", "guard-diagnostic.txt"]}}


def bindings():
    return {"compiler_sha256": sha(fixture.native.COMPILER), "legacy_compiler_sha256": sha(fixture.native.LEGACY),
            "proof_report_sha256": sha(fixture.native.PROOF), "native_report_sha256": sha(fixture.WORK / "report.json"),
            "source_sha256": sha(SOURCE), "helper_sources": {p: sha(ROOT / p) for p in HELPERS},
            "toolchain_lock_sha256": sha(ROOT / "toolchain.lock.json")}


def summaries(samples):
    rows = {}
    for case in range(len(CASES)):
        rows[str(case)] = {}
        source = {s["round"]: s["ns_per_call"] for s in samples if s["case"] == case and s["mode"] == "disabled"}
        for mode in MODES:
            selected = [s for s in samples if s["case"] == case and s["mode"] == mode]
            values = [s["ns_per_call"] for s in selected]
            ratios = [s["ns_per_call"]/source[s["round"]] for s in selected]
            quartiles = statistics.quantiles(values, n=4, method="inclusive")
            rows[str(case)][mode] = {"median_ns_per_call": statistics.median(values),
                "iqr_ns_per_call": quartiles[2]-quartiles[0], "median_paired_cost_over_source": statistics.median(ratios)}
    return rows


def validate(report):
    fixture.configure()
    fixture.validate(json.loads((fixture.WORK / "report.json").read_text()))
    assert report["bindings"] == bindings() and report["status"] == "measured"
    assert report["cases"] == [list(row) for row in CASES]
    for mode, data in report["configurations"].items():
        assert mode in MODES
        for name, digest in (data["artifacts"] | data.get("guard_diagnostic", {}).get("artifacts", {})).items():
            assert sha(WORK / mode / name) == digest, (mode, name)
        assert data["kernel_bytes"] == fixture.native.frontend.machine_bytes(WORK / mode / "program", "nested_write")
    samples = [json.loads(line) for line in (WORK / "samples.jsonl").read_text().splitlines()]
    assert report["samples_sha256"] == sha(WORK / "samples.jsonl") and report["samples"] == len(samples)
    assert report["summaries"] == summaries(samples)
    assert {(s["case"], s["mode"], s["round"]) for s in samples} == \
        {(c, m, r) for c in range(len(CASES)) for m in MODES for r in range(report["protocol"]["rounds"])}
    for item in samples:
        assert item["cpu_seconds"] >= report["protocol"]["minimum_batch_cpu_seconds"]
        expected = "RESULT " + fixture.run_model(CASES[item["case"]])[0].strip()
        assert item["warmup_and_final_result_sha256"] == sha_text(expected)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    fixture.configure()
    fixture.validate(json.loads((fixture.WORK / "report.json").read_text()))
    if args.validate:
        validate(json.loads((WORK / "report.json").read_text()))
        print(json.dumps({"status": "validated", "report_sha256": sha(WORK / "report.json")}))
        return
    assert not (WORK / "report.json").exists(), "Refusing to replace an existing timing report"
    WORK.mkdir(parents=True, exist_ok=True)
    SOURCE.write_text(source_text())
    configs = {mode: compile_one(mode) for mode in MODES}
    for mode in MODES[1:]:
        configs[mode]["guard_diagnostic"] = guard_diagnostic(mode)
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
    with (WORK / "samples.jsonl").open("w") as raw:
        for round_id in range(ROUNDS):
            order = [(c, m) for c in range(len(CASES)) for m in MODES]
            rng.shuffle(order)
            for sequence, (case, mode) in enumerate(order):
                count = repetitions[(case, mode)]
                result = sample(mode, case, count, cpu)
                # Retain the actual batch; do not discard a faster observation.
                if result["cpu_seconds"] < TARGET_SECONDS/2:
                    raise AssertionError((case, mode, "batch shorter than protocol minimum"))
                item = {"round": round_id, "order": sequence, "case": case, "mode": mode, **result}
                raw.write(json.dumps(item) + "\n")
                raw.flush()
                samples.append(item)
            print("Timing round", round_id+1, "/", ROUNDS, flush=True)
    report = {"status": "measured", "bindings": bindings(), "cases": [list(row) for row in CASES],
        "protocol": {"rounds": ROUNDS, "seed": SEED, "target_batch_cpu_seconds": TARGET_SECONDS,
            "minimum_batch_cpu_seconds": TARGET_SECONDS/2, "fresh_process_per_batch": True,
            "pinned_cpu": cpu, "clock": "C clock() process CPU time", "warmup_calls": 1,
            "inclusive_per_call_header_reset": True, "array_initialization_and_validation_timed": False},
        "environment": {"platform": platform.platform(), "available_cpus": cpus,
            "cpu_model": next((line.split(":", 1)[1].strip() for line in open("/proc/cpuinfo") if line.startswith("model name")), "unknown"),
            "gcc": subprocess.check_output(["gcc", "--version"], text=True).splitlines()[0]},
        "configurations": configs, "calibration": calibration, "samples": len(samples),
        "samples_sha256": sha(WORK / "samples.jsonl"), "summaries": summaries(samples),
        "scope": "one fixed-layout literal-store kernel with matched inputs; exploratory mechanism measurement",
        "limitations": ["not representative benchmark speedups or real-world acceptance frequencies",
            "warm repeated input and fixed profile up to 16; no confidence interval or break-even inference",
            "decision counts are diagnostic printed Clight; timing is unmodified CompCert assembly",
            "compile costs use already built compilers; proof/extraction setup is not included"]}
    validate(report)
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "measured", "samples": len(samples), "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
