"""Measure frozen loaded-word assembly; count guard work in a separate Clight derivative.

The baseline is the unmarked function in the same C/assembly configuration.
No source, compiler, proof object, or prior report is rebuilt or overwritten.
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

from audit_interface_clight import ROOT, sha
import native_zero_loaded_word_pipeline as native
import native_loaded_word_pipeline_v3 as historical
from native_nested_compact_cost import instrument_decisions

WORK = ROOT / "build/loaded-word-zero-cost"
LAYOUTS = ["old-row-tile", "old-column-tile", "new-row-tile", "new-column-tile"]
MODES = ["source", "guarded"]
CASES = [(0,3,31,2,5,7), (0,31,31,31,5,7), (0,2,31,32,5,-2),
         (1,3,31,2,5,7), (0,0,1001,99,-8,7), (0,3,31,0,5,7),
         (0,1,1001,2,5,7), (0,2,3,2,-7,-1), (0,2,3,2,-7,0), (0,3,31,2,5,0), (0,31,31,31,5,0), (0,2,3,3,-7,0)]
CASE_NAMES = ["small-accepted", "dense-accepted", "row-layout-refusal-column-acceptance",
              "nonzero-start-refusal", "empty-root-null-unavailable-child", "empty-child",
              "stride-profile-refusal-after-scan", "changing-header-alias-refusal",
              "zero-increment-alias", "small-zero", "dense-zero", "two-distinct-header-words-zero-alias"]
SIZE, CENTER, ROUNDS, SEED, TARGET_SECONDS = 6144, 128, 12, 20261007, 0.04


def configuration_path(layout):
    generation,name = layout.split("-",1)
    return (historical.WORK if generation == "old" else native.WORK)/name


def digest_text(value):
    return hashlib.sha256(value.encode()).hexdigest()


def word(value):
    return (value + 2**31) % 2**32 - 2**31


@lru_cache(maxsize=None)
def effect(layout, case):
    start,n,ld,columns,components,alpha = CASES[case]
    alias = components == -7
    array = [word(3*x+1) for x in range(SIZE)]
    if alias:
        array[CENTER:CENTER+2] = [n,columns]
    public, counts = [start,77,88], Counter()
    while public[0] < (array[CENTER] if alias else n):
        public[1] = 0
        while public[1] < (array[CENTER+1] if alias else columns):
            public[2] = 0
            while public[2] < 5:
                i,j,k = public
                major,minor = (j,i) if layout.endswith("column-tile") else (i,j)
                index = CENTER+word(word(word(major*ld)+minor)*5+k)
                assert 0 <= index < SIZE, (layout,case,index)
                counts[index] += 1
                array[index] = word(array[index]+alpha)
                public[2] += 1
            public[1] += 1
        public[0] += 1
    return public, counts, array[CENTER:CENTER+2]


@lru_cache(maxsize=256)
def expected_result(layout, case, calls):
    public,counts,headers = effect(layout,case)
    alpha = CASES[case][5]
    array = [word(3*x+1+calls*alpha*counts[x]) for x in range(SIZE)]
    if CASES[case][4] == -7:
        # The actual function resets these two cells before every invocation.
        array[CENTER:CENTER+2] = headers
    return "RESULT " + " ".join(map(str,[case,*public,*public,word(100+7*calls),word(200+11*calls),*array]))


def harness_text():
    rows = ",\n".join("{"+",".join(map(str,row))+"}" for row in CASES)
    return '''#include <stdio.h>
#include <stdlib.h>
#include <time.h>
extern int tensor_i,tensor_j,tensor_k,tensor_first_i,tensor_first_j,tensor_first_k,tensor_pre,tensor_post;
extern void selected_one(int*,int,int,int,int,int,int),unmarked(int*,int,int,int,int,int,int);
int A[6144],which;
int inputs[][6]={'''+rows+'''};
void initialize(int c){int x;which=c;for(x=0;x<6144;x++)A[x]=3*x+1;tensor_pre=100;tensor_post=200;}
void invoke(int mode){int*p=inputs[which];int*a=p[1]==0?0:A+128;
if(mode)selected_one(a,p[1],p[2],p[3],p[4],p[5],p[0]);
else unmarked(a,p[1],p[2],p[3],p[4],p[5],p[0]);}
void show(void){int x;printf("RESULT %d %d %d %d %d %d %d %d %d",which,tensor_i,tensor_j,tensor_k,
tensor_first_i,tensor_first_j,tensor_first_k,tensor_pre,tensor_post);
for(x=0;x<6144;x++)printf(" %d",A[x]);printf("\\n");}
int main(int argc,char**argv){int c,mode,r,count;clock_t before,after;
if(argc!=4)return 2;c=atoi(argv[1]);mode=atoi(argv[2]);count=atoi(argv[3]);
if(c<0||c>='''+str(len(CASES))+'''||mode<0||mode>1||count<1)return 3;
initialize(c);invoke(mode);show();before=clock();for(r=0;r<count;r++)invoke(mode);after=clock();
printf("TIME %d %lu %lu\\n",count,(unsigned long)(after-before),(unsigned long)CLOCKS_PER_SEC);show();return 0;}
'''


def kernel_bytes(path, symbol):
    output = subprocess.check_output(["nm","-S",str(path)],text=True)
    matches = re.findall(r"^\S+ ([0-9a-f]+) [Tt] "+re.escape(symbol)+r"$",output,re.MULTILINE)
    assert len(matches) == 1, symbol
    return int(matches[0],16)


def expected_guard(layout, case):
    start,n,ld,columns,components,alpha = CASES[case]
    reached = start == 0 and 1 <= n <= 32 and 1 <= columns <= 32
    shortcut = layout.startswith("new-") and alpha == 0
    points = 0 if shortcut else 1 if reached and components == -7 else n*columns*5 if reached else 0
    accepted = reached and (components != -7 or shortcut) and 1 <= ld < 1000 and (n if layout.endswith("column-tile") else columns) <= ld
    return points,accepted


def diagnostic(layout):
    directory = WORK/layout
    dump = native.fixtures.printer_for_gcc((configuration_path(layout)/"regions.light.c").read_text())
    main = re.search(r"^int guard_original_main\(void\)\n\{",dump,re.MULTILINE)
    assert main
    dump = re.sub(r"^int main\(void\);\n", "",dump[:main.start()],flags=re.MULTILINE)
    body = native.fixtures.function_body(dump,"selected_one")
    [(yes,no)] = list(native.fixtures.dispatch_sites(body))
    dispatch = body.rfind("if (",0,yes)
    assert re.fullmatch(r"if \(\$[0-9]+\) \{",body[dispatch:yes+1])
    begin = body.index("if ($i == 0U)")
    marked,static = instrument_decisions(body[begin:dispatch])
    point = "if ((++guard_decisions, ($117 < $118))) {"
    assert marked.count(point) == 1
    marked = marked.replace(point,point+"guard_points++;",1)
    yescode = "guard_fast++;"
    nocode = "guard_refusal++;"
    suffix = body[dispatch:]
    suffix = suffix[:no-dispatch+1]+nocode+suffix[no-dispatch+1:]
    suffix = suffix[:yes-dispatch+1]+yescode+suffix[yes-dispatch+1:]
    changed = body[:begin]+marked+suffix
    dump = dump.replace(body,changed,1)
    prefix = harness_text().split("int main(",1)[0]
    prefix = re.sub(r"^extern .*;\n", "",prefix,flags=re.MULTILINE)
    prefix = prefix.replace("#include <stdio.h>\n", "")
    source = "unsigned long guard_decisions,guard_points;int guard_fast,guard_refusal;\n"+dump+prefix
    source += "int main(void){int c;for(c=0;c<"+str(len(CASES))+";c++){initialize(c);guard_decisions=guard_points=0;guard_fast=guard_refusal=0;invoke(1);show();printf(\"GUARD %d %lu %lu %d %d\\n\",c,guard_decisions,guard_points,guard_fast,guard_refusal);}return 0;}\n"
    (directory/"diagnostic.c").write_text(source)
    subprocess.run(["gcc","-O0","-fwrapv","-Wno-builtin-declaration-mismatch","-Wno-discarded-qualifiers",
                    str(directory/"diagnostic.c"),"-o",str(directory/"diagnostic")],capture_output=True,check=True)
    output = subprocess.check_output([str(directory/"diagnostic")],text=True)
    (directory/"diagnostic.txt").write_text(output)
    lines = output.splitlines()
    assert len(lines) == len(CASES)*2
    facts = []
    for c in range(len(CASES)):
        assert lines[2*c] == expected_result(layout,c,1)
        index,decisions,points,fast,refusal = map(int,lines[2*c+1].split()[1:])
        wanted,accepted = expected_guard(layout,c)
        assert (index,points,fast,refusal) == (c,wanted,int(accepted),int(not accepted))
        facts.append({"case":c,"scan_points":points,"guard_if_evaluations":decisions,"accepted":bool(fast),
                      "original_body_points":sum(effect(layout,c)[1].values())})
    return {"static_guard_if_sites":static,"cases":facts,"production_assembly":False,
            "scope":"Clight if evaluations from root-start test to final dispatch; scan points exclude failed loop-exit tests"}


def bindings():
    paths = [ROOT/"scripts/native_zero_loaded_word_cost.py",native.WORK/"report.json",native.COMPILER,
             native.COMPILER.parent/".guard-build.json",ROOT/"toolchain.lock.json"]
    paths += [historical.WORK/"report.json",historical.COMPILER,historical.COMPILER.parent/".guard-build.json",
              ROOT/"scripts/native_loaded_word_cost.py"]
    paths += [configuration_path(layout)/file for layout in LAYOUTS for file in ["program.s","regions.light.c"]]
    return {str(p.relative_to(ROOT)):sha(p) for p in paths}


def artifact_bindings():
    return {str(p.relative_to(WORK)):sha(p) for p in WORK.rglob("*") if p.is_file() and p.name not in ["prepared.json","report.json","samples.jsonl"]}


def prepare():
    assert not WORK.exists(), "Refusing to reuse a cost checkpoint"
    WORK.mkdir()
    (WORK/"harness.c").write_text(harness_text())
    configurations = {}
    for layout in LAYOUTS:
        directory = WORK/layout
        directory.mkdir()
        subprocess.run(["gcc","-c",str(configuration_path(layout)/"program.s"),"-o",str(directory/"fixture.o")],check=True,capture_output=True)
        subprocess.run(["objcopy","--redefine-sym","main=guard_fixture_main",str(directory/"fixture.o"),str(directory/"kernels.o")],check=True)
        subprocess.run(["gcc","-O2","-fwrapv","-no-pie",str(WORK/"harness.c"),str(directory/"kernels.o"),"-o",str(directory/"program")],check=True,capture_output=True)
        configurations[layout] = {"kernel_bytes":{mode:kernel_bytes(directory/"program",symbol)
            for mode,symbol in zip(MODES,["unmarked","selected_one"])},"diagnostic":diagnostic(layout)}
        print("Prepared",layout,flush=True)
    prepared = {"bindings":bindings(),"configurations":configurations,"artifacts":artifact_bindings()}
    (WORK/"prepared.json").write_text(json.dumps(prepared,indent=2)+"\n")


def sample(layout, mode, case, repetitions, cpu):
    command = [str(WORK/layout/"program"),str(case),str(MODES.index(mode)),str(repetitions)]
    if cpu is not None:
        command = ["taskset","-c",str(cpu),*command]
    lines = subprocess.check_output(command,text=True,timeout=60).splitlines()
    assert len(lines) == 3
    warm,final = expected_result(layout,case,1),expected_result(layout,case,repetitions+1)
    assert lines[0] == warm and lines[2] == final,(layout,mode,case,"complete result mismatch")
    count,ticks,frequency = map(int,lines[1].split()[1:])
    assert count == repetitions and ticks >= 0 and frequency > 0
    return {"repetitions":count,"cpu_ticks":ticks,"ticks_per_second":frequency,
            "cpu_seconds":ticks/frequency,"ns_per_call":1e9*ticks/frequency/count,
            "warmup_result_sha256":digest_text(warm),"final_result_sha256":digest_text(final)}


def summaries(samples):
    output = {}
    for layout in LAYOUTS:
        output[layout] = {}
        for case in range(len(CASES)):
            source = {s["round"]:s["ns_per_call"] for s in samples if (s["layout"],s["mode"],s["case"]) == (layout,"source",case)}
            rows = [s for s in samples if (s["layout"],s["mode"],s["case"]) == (layout,"guarded",case)]
            ratios = [r["ns_per_call"]/source[r["round"]] for r in rows]
            quartiles = statistics.quantiles(ratios,n=4,method="inclusive")
            output[layout][str(case)] = {"source_median_ns":statistics.median(source.values()),
                "guarded_median_ns":statistics.median(r["ns_per_call"] for r in rows),
                "median_paired_cost_over_source":statistics.median(ratios),"paired_ratio_iqr":quartiles[2]-quartiles[0]}
    return output


def measure():
    assert not (WORK/"report.json").exists(), "Refusing to replace timing evidence"
    prepared = json.loads((WORK/"prepared.json").read_text())
    assert prepared["bindings"] == bindings() and prepared["artifacts"] == artifact_bindings()
    cpus = sorted(os.sched_getaffinity(0)) if hasattr(os,"sched_getaffinity") else []
    cpu = cpus[0] if cpus else None
    repetitions,calibration = {},[]
    for layout in LAYOUTS:
        for case in range(len(CASES)):
            for mode in MODES:
                count = 1000
                for _ in range(10):
                    trial = sample(layout,mode,case,count,cpu)
                    calibration.append({"layout":layout,"mode":mode,"case":case,**trial})
                    if trial["cpu_seconds"] >= TARGET_SECONDS:
                        break
                    count = min(100000000,max(2*count,int(count*TARGET_SECONDS*1.2/max(trial["cpu_seconds"],1e-6))))
                else:
                    raise AssertionError((layout,mode,case,"calibration failed"))
                repetitions[(layout,mode,case)] = count
            print("Calibrated",layout,case,flush=True)
    rng,samples = random.Random(SEED),[]
    with (WORK/"samples.jsonl").open("x") as raw:
        for round_id in range(ROUNDS):
            # Adjacent pairs share a layout/input; baseline order varies by round.
            pairs = [(layout,c) for layout in LAYOUTS for c in range(len(CASES))]
            rng.shuffle(pairs)
            for order,(layout,case) in enumerate(pairs):
                modes = MODES[:]
                rng.shuffle(modes)
                for mode in modes:
                    result = sample(layout,mode,case,repetitions[(layout,mode,case)],cpu)
                    assert result["cpu_seconds"] >= TARGET_SECONDS/2
                    item = {"round":round_id,"pair_order":order,"layout":layout,"mode":mode,"case":case,**result}
                    raw.write(json.dumps(item)+"\n");raw.flush();samples.append(item)
            print("Timing round",round_id+1,"/",ROUNDS,flush=True)
    report = {"status":"measured",**prepared,"cases":[list(c) for c in CASES],"case_names":CASE_NAMES,
        "protocol":{"rounds":ROUNDS,"seed":SEED,"target_batch_cpu_seconds":TARGET_SECONDS,
                    "minimum_batch_cpu_seconds":TARGET_SECONDS/2,"pinned_cpu":cpu,"clock":"C clock() process CPU time",
                    "fresh_process_per_batch":True,"warmup_calls":1,"array_reset_per_call":False,
                    "array_initialization_and_validation_timed":False,"actual_call_count_results_validated":True,
                    "assembly_instrumented":False,"baseline":"unmarked function in the same frozen source/compiler/assembly configuration"},
        "environment":{"platform":platform.platform(),"available_cpus":cpus,
                       "cpu_model":next((line.split(":",1)[1].strip() for line in open("/proc/cpuinfo") if line.startswith("model name")),"unknown"),
                       "gcc":subprocess.check_output(["gcc","--version"],text=True).splitlines()[0]},
        "calibration":calibration,"samples":len(samples),"samples_sha256":sha(WORK/"samples.jsonl"),"summaries":summaries(samples),
        "scope":"paired old/new exploratory whole-function cost of the installed loaded-word RMW tiling family; per-call loaded header construction/capture, guard, candidate/fallback, counters and backend all included",
        "limitations":["warm repeated inputs; not a benchmark suite, acceptance frequency, general speedup or break-even claim",
                       "Clight work counts are separate from assembly timing and do not count machine instructions",
                       "no confidence intervals; shared host noise and function placement can affect ratios",
                       "no compiler-time measurement; both installed assembly checkpoints reused without recompilation"]}
    (WORK/"report.json").write_text(json.dumps(report,indent=2)+"\n")
    validate()
    print(json.dumps({"status":"measured","samples":len(samples),"report_sha256":sha(WORK/"report.json")}),flush=True)


def validate():
    native.validate()
    historical.validate()
    report = json.loads((WORK/"report.json").read_text())
    assert report["status"] == "measured" and report["bindings"] == bindings()
    assert report["cases"] == [list(c) for c in CASES] and report["case_names"] == CASE_NAMES
    assert report["artifacts"] == artifact_bindings()
    samples = [json.loads(line) for line in (WORK/"samples.jsonl").read_text().splitlines()]
    assert report["samples"] == len(samples) and report["samples_sha256"] == sha(WORK/"samples.jsonl")
    assert report["summaries"] == summaries(samples)
    assert {(s["layout"],s["mode"],s["case"],s["round"]) for s in samples} == {(l,m,c,r) for l in LAYOUTS for m in MODES for c in range(len(CASES)) for r in range(ROUNDS)}
    for s in samples:
        assert s["cpu_seconds"] >= TARGET_SECONDS/2
        assert s["warmup_result_sha256"] == digest_text(expected_result(s["layout"],s["case"],1))
        assert s["final_result_sha256"] == digest_text(expected_result(s["layout"],s["case"],s["repetitions"]+1))
    for layout,config in report["configurations"].items():
        assert config["kernel_bytes"] == {m:kernel_bytes(WORK/layout/"program",symbol) for m,symbol in zip(MODES,["unmarked","selected_one"])}
        assert not config["diagnostic"]["production_assembly"]
        for row in config["diagnostic"]["cases"]:
            assert (row["scan_points"],row["accepted"]) == expected_guard(layout,row["case"])
    assert (WORK/"harness.c").read_text() == harness_text()
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare",action="store_true")
    parser.add_argument("--measure",action="store_true")
    parser.add_argument("--validate",action="store_true")
    args = parser.parse_args()
    assert sum([args.prepare,args.measure,args.validate]) <= 1
    native.validate()
    historical.validate()
    if args.validate:
        validate();print(json.dumps({"status":"validated","report_sha256":sha(WORK/"report.json")}))
    elif args.prepare:
        prepare()
    elif args.measure:
        measure()
    else:
        prepare();measure()


if __name__ == "__main__":
    main()
