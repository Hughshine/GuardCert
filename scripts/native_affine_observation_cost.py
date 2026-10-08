"""Measure complete calls to unchanged compiled kernels, checking every final cell."""
import functools
import json
import random
import statistics
import subprocess
import time
from pathlib import Path

import affine_observation_fixtures as fixtures
import native_affine_observation as current
import native_affine_observation_comparison as comparison
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/affine-observation/cost-v2"
REPETITIONS, BATCHES = 65536, 7
# kind, N, M, alpha; start is zero, q equals p, and the triangle is measured.
CASES = [
    ("separated-zero", 0, 3, 1, 0),
    ("N-overlap-zero", 2, 3, 1, 0),
    ("M-overlap-zero", 3, 3, 1, 0),
    ("N-overlap-nonzero", 2, 3, 1, 1),
    ("separated-nonzero", 0, 3, 1, 1),
    ("body-empty", 0, 1, 0, 0),
    ("cap-refusal", 0, 5, 1, 7),
    ("first-empty", 0, 3, 0, 0),
]


def driver():
    controls = ",\n".join("{" + ",".join(map(str, row[1:])) + "}" for row in CASES)
    return f'''#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
extern int public_i,public_j,public_k,public_rp,public_rq,public_snapshot,public_context;
extern void rmw_snapshot_triangle(int*,int*,int*,int*,int,int);
static int storage[{fixtures.SIZE}],other[{fixtures.SIZE}];
static const int controls[][4]={{
{controls}
}};
static uint64_t nanos(void) {{
  struct timespec now;
  if(clock_gettime(CLOCK_PROCESS_CPUTIME_ID,&now)) abort();
  return (uint64_t)now.tv_sec*1000000000ULL+(uint64_t)now.tv_nsec;
}}
int main(int argc,char **argv) {{
  if(argc!=3) return 2;
  int slot=atoi(argv[1]);
  uint64_t repetitions=strtoull(argv[2],0,10),iteration;
  if(slot<0 || slot>=8 || repetitions==0) return 3;
  int kind=controls[slot][0],n=controls[slot][1],m=controls[slot][2],a=controls[slot][3];
  int value=n,height_value=m,x;
  int *p=storage+{fixtures.BASE},*bound=&value,*height=&height_value;
  if(kind==2) bound=p+32;
  if(kind==3) height=p+32;
  for(x=0;x<{fixtures.SIZE};++x) {{storage[x]=x;other[x]=3*x+7;}}
  uint64_t start=nanos();
  for(iteration=0;iteration<repetitions;++iteration) {{
    *bound=n;*height=m;
    rmw_snapshot_triangle(p,p,bound,height,0,a);
    public_context=31+public_i+public_j+public_k;
  }}
  uint64_t elapsed=nanos()-start;
  printf("elapsed %llu\\n",(unsigned long long)elapsed);
  printf("%d %llu %d %d %d %d %d %d %d %d %d",slot,(unsigned long long)repetitions,
    public_i,public_j,public_k,public_rp,public_rq,public_snapshot,public_context,*bound,*height);
  for(x=0;x<{fixtures.SIZE};++x) printf(" %d %d",storage[x],other[x]);
  printf("\\n");
  return 0;
}}
'''


@functools.lru_cache(None)
def expected(slot, repetitions):
    _, kind, n, m, alpha = CASES[slot]
    storage, other = list(range(fixtures.SIZE)), [3*x+7 for x in range(fixtures.SIZE)]
    base = fixtures.BASE
    for _ in range(repetitions):
        if kind == 2:
            storage[base+32] = n
        if kind == 3:
            storage[base+32] = m
        rp = storage[base]
        i, j, k = 0, 77, 91
        while i < (storage[base+32] if kind == 2 else n):
            k = fixtures.word(i+(storage[base+32] if kind == 3 else m))
            j = 0
            while j < k:
                address = base+32+64*i+j
                assert 0 <= address < fixtures.SIZE
                storage[address] = fixtures.word(storage[address]+alpha)
                j += 1
            i = fixtures.word(i+1)
        storage[base] = fixtures.word(rp+19)
    outputs = [slot,repetitions,i,j,k,rp,rp,123,31+i+j+k,
               storage[base+32] if kind == 2 else n,
               storage[base+32] if kind == 3 else m]
    return " ".join(map(str,outputs+[v for pair in zip(storage,other) for v in pair]))+"\n"


def main():
    bindings = current.check_build()
    native = current.validate(current.WORK)
    prior = json.loads((comparison.WORK / "report.json").read_text())
    assert prior["status"] == "passed" and prior["same_C_sources_and_inputs"]
    for path,digest in prior["bindings"].items():
        assert sha(ROOT / path) == digest, path
    if (WORK / "report.json").exists():
        report=json.loads((WORK / "report.json").read_text())
        assert report["status"] == "passed"
        for path,digest in report["bindings"].items():
            assert sha(ROOT / path) == digest,path
        print(json.dumps({"status":"validated","report_sha256":sha(WORK / "report.json")}))
        return
    WORK.mkdir(parents=True,exist_ok=False)
    source=WORK / "driver.c"
    source.write_text(driver())
    assemblies={}
    for mode in ("tile","schedule"):
        assemblies[(mode,"current")]=current.WORK / mode / "program.s"
        assemblies[(mode,"before")]=comparison.WORK / mode / "program.s"
        assemblies[(mode,"source")]=current.WORK / "disabled/program.s"
    binaries={}
    commands=[]
    with (WORK / "build.log").open("x") as log:
        for key,assembly in assemblies.items():
            name="-".join(key)
            directory=WORK / name
            directory.mkdir()
            obj,renamed=directory / "program.o",directory / "renamed.o"
            def run(argv):
                commands.append(argv)
                subprocess.run(argv,stdout=log,stderr=subprocess.STDOUT,check=True)
            run(["gcc","-c",str(assembly),"-o",str(obj)])
            run(["objcopy","--redefine-sym","main=guard_fixture_main",str(obj),str(renamed)])
            run(["objcopy","--dump-section",".text="+str(directory / "before.text"),str(obj)])
            run(["objcopy","--dump-section",".text="+str(directory / "after.text"),str(renamed)])
            assert (directory / "before.text").read_bytes()==(directory / "after.text").read_bytes()
            binary=directory / "cost"
            run(["gcc","-O2","-no-pie",str(source),str(renamed),"-o",str(binary)])
            binaries[key]=binary
    (WORK / "build-commands.json").write_text(json.dumps(commands,indent=2)+"\n")
    paths={mode:{tuple(row["input"]):row for row in native["configurations"][mode]["paths"]}
           for mode in ("tile","schedule")}
    old_paths={mode:{tuple(row["input"]):row for row in prior["baseline_configurations"][mode]["paths"]}
               for mode in ("tile","schedule")}
    order=[(mode,variant,slot,batch) for mode in ("tile","schedule")
           for variant in ("current","before","source") for slot in range(len(CASES))
           for batch in range(BATCHES)]
    random.Random(1791500000).shuffle(order)
    (WORK / "order.json").write_text(json.dumps(order)+"\n")
    samples={}
    started=time.monotonic()
    for mode,variant,slot,batch in order:
        output=subprocess.check_output([str(binaries[(mode,variant)]),str(slot),str(REPETITIONS)],text=True,timeout=60)
        first,rest=output.split("\n",1)
        assert rest==expected(slot,REPETITIONS),(mode,variant,slot,batch,"full repeated-call outputs")
        elapsed=int(first.split()[1])
        assert elapsed>0
        (WORK / ("-".join(map(str,(mode,variant,slot,batch)))+".txt")).write_text(output)
        samples.setdefault((mode,variant,slot),[]).append(elapsed/REPETITIONS)
    rows=[]
    for mode in ("tile","schedule"):
        for slot,(name,kind,n,m,alpha) in enumerate(CASES):
            case=(0,kind,0,n,m,alpha)
            medians={variant:statistics.median(samples[(mode,variant,slot)]) for variant in ("current","before","source")}
            row={"mode":mode,"case":name,"input":list(case),"ns_per_complete_call":medians,
                "current_vs_before_ratio":medians["current"]/medians["before"],
                "current_vs_source_ratio":medians["current"]/medians["source"],
                "current_fast":paths[mode][case]["fast"],"before_fast":old_paths[mode][case]["fast"],
                "samples":{variant:samples[(mode,variant,slot)] for variant in medians}}
            rows.append(row)
            print(json.dumps({key:value for key,value in row.items() if key!="samples"}),flush=True)
    bindings |= {ROOT / path:digest for path,digest in prior["bindings"].items()}
    helpers=[Path(__file__),ROOT / "scripts/native_affine_observation.py",ROOT / "scripts/affine_observation_fixtures.py"]
    bindings |= {path:sha(path) for path in helpers+list(assemblies.values())}
    bindings |= {current.WORK / "report.json":sha(current.WORK / "report.json"),
                 comparison.WORK / "report.json":sha(comparison.WORK / "report.json")}
    bindings |= {path:sha(path) for path in WORK.rglob("*") if path.is_file()}
    failed=ROOT / "build/affine-observation/cost-v1"
    bindings |= {path:sha(path) for path in failed.rglob("*") if path.is_file()}
    report={"status":"passed","rows":rows,"batches":len(order),"repetitions_per_batch":REPETITIONS,
        "full_final_memory_public_controls_and_continuation_checked_every_batch":True,
        "kernel_machine_text_unchanged_when_original_main_symbol_renamed":True,
        "check_only_cost_claimed":False,"check_plus_candidate_or_fallback_measured":True,
        "clock":"CLOCK_PROCESS_CPUTIME_ID; seven randomized process batches per variant/case/mode",
        "scope":"complete triangle calls include resetting N/M and public-context update in the shared driver; no printing or storage initialization inside the timer; original kernels from bound native assembly",
        "source_is_same_successor_compiler_with_transformation_disabled":True,
        "selected_profile":{"row_cap":4,"column_cap":8,"geometry_cap":4,"extent":8192},
        "all_current_medians_faster_than_source":all(row["current_vs_source_ratio"]<1 for row in rows),
        "representative_workload_profitability_claimed":False,"full_goal_complete":False,
        "preserved_failed_harness":"build/affine-observation/cost-v1/failure.json; all 336 final outputs matched before a missing native-path key prevented report construction",
        "elapsed_harness_seconds":time.monotonic()-started,
        "bindings":{str(path.relative_to(ROOT)):digest for path,digest in bindings.items()}}
    (WORK / "report.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"status":"passed","batches":len(order),"report_sha256":sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
