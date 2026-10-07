"""Check an adapted OLO motivating source and record its frontend coverage gap."""
import argparse
import json
import os
from pathlib import Path
import subprocess

import loaded_affine_reduced as stage
from audit_interface_clight import sha

ROOT = stage.suite.ROOT
SOURCE = ROOT/"examples/olo_figure2_adapted.c"
WORK = ROOT/"build/loaded-affine-multi-reduced/olo-figure2"
CASES = [(0,2,2),(0,0,0),(1,2,2),(2,2,2),(3,-1,99),
         (3,2147483647,99),(4,2,-1),(0,-2,1)]
PAPER = "https://pollylabs.org/publications/grosser-2017-Optimistic-Loop-Optimization.pdf"


def source_text():
    text = '''/* Independent adaptation of the OLO Figure 1/2 motivating shape.
   Fixed 16x16x5 layout; flat signed32 data and a replacement arithmetic body.
   This is an excerpt coverage probe, not the NPB BT benchmark. */
#include <stdio.h>
int bt_j,bt_i,bt_c;
void bt_excerpt(int *output,int *shape){
  int row=0,column=77,component=91;
  for(row=0;row<shape[0]+1;row++)
    for(column=0;column<shape[1]+1;column++)
      for(component=0;component<5;component++)
        output[(row*16+column)*5+component]=row+column+component;
  bt_j=row;bt_i=column;bt_c=component;
}
void bt_case(int view,int u,int v){
  int data[2048],dims[2],single[1],x,*output=data,*shape=dims;
  for(x=0;x<2048;x++)data[x]=3*x+7;
  dims[0]=u;dims[1]=v;single[0]=u;
  if(view==1){shape=data;shape[0]=u;shape[1]=v;}
  if(view==2){shape=data+5;shape[0]=u;shape[1]=v;}
  if(view==3){shape=single;output=0;}
  if(view==4)output=0;
  bt_excerpt(output,shape);
  printf("%d %d %d %d %d %d %d %d",view,u,v,bt_j,bt_i,bt_c,shape[0],view==3?99:shape[1]);
  for(x=0;x<2048;x++)printf(" %d",data[x]);printf("\\n");
}
int main(void){
'''
    return text+"\n".join("bt_case("+",".join(map(str,row))+");" for row in CASES)+"return 0;}\n"


def model(row):
    view,u,v = row
    data = [3*x+7 for x in range(2048)]
    base = {1:0,2:5}.get(view)
    if base is not None:
        data[base:base+2] = [u,v]
    def bound(axis):
        value = data[base+axis] if base is not None else [u,v][axis]
        return stage.suite.word(value+1)
    j,i,c = 0,77,91
    while j<bound(0):
        assert j<16
        i = 0
        while i<bound(1):
            assert i<16 and view not in [3,4]
            c = 0
            while c<5:
                data[(j*16+i)*5+c] = j+i+c
                c += 1
            i += 1
        j += 1
    final = [data[base],data[base+1]] if base is not None else [u,99 if view==3 else v]
    return " ".join(map(str,[*row,j,i,c,*final,*data]))+"\n"


def validate():
    stage.configure()
    stage.check_build()
    path = WORK/"report.json"
    report = json.loads(path.read_text())
    assert report["status"] == "passed" and report["optimizer_coverage"] == "not-supported"
    assert report["verification_script_sha256"] == sha(Path(__file__))
    assert report["harness_sha256"] == sha(stage.SELF)
    assert report["compiler_sha256"] == sha(stage.suite.COMPILER)
    assert report["proof_report_sha256"] == sha(stage.suite.PROOF)
    for helper,digest in report["helper_sources"].items():
        assert sha(ROOT/helper) == digest,helper
    assert report["source_sha256"] == sha(SOURCE) and SOURCE.read_text() == source_text()
    expected = "".join(model(row) for row in CASES)
    assert report["calls_per_configuration"] == len(CASES)
    for name,facts in report["configurations"].items():
        for artifact,digest in facts["artifacts"].items():
            assert sha(WORK/name/artifact) == digest,(name,artifact)
        assert (WORK/name/"output.txt").read_text() == expected
    assert set(report["configurations"]) == {"disabled","interchange"}
    assert (WORK/"reference-output.txt").read_text() == expected
    assert report["reference_sha256"] == sha(WORK/"reference-output.txt")
    bodies = [stage.suite.function_body((WORK/name/(SOURCE.stem+".light.c")).read_text(),"bt_excerpt")
              for name in ["disabled","interchange"]]
    assert bodies[0] == bodies[1] and bodies[0].count("for (") == 3
    assert report["original_three_loop_body_preserved"] and not report["timing_or_profitability_measured"]
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generate-only",action="store_true")
    parser.add_argument("--validate",action="store_true")
    args = parser.parse_args()
    if args.generate_only:
        SOURCE.write_text(source_text())
        return
    if args.validate:
        validate()
        print("OLO Figure 2 adapted-source bindings passed; optimizer coverage remains unsupported")
        return
    stage.configure()
    stage.check_build()
    assert SOURCE.read_text() == source_text()
    WORK.mkdir(parents=True,exist_ok=True)
    expected = "".join(model(row) for row in CASES)
    subprocess.run(["gcc","-O0","-fwrapv",str(SOURCE),"-o",str(WORK/"reference")],check=True)
    actual = subprocess.check_output([str(WORK/"reference")],text=True)
    assert actual == expected
    (WORK/"reference-output.txt").write_text(actual)
    results = {}
    for name in ["disabled","interchange"]:
        directory = WORK/name
        directory.mkdir(exist_ok=True)
        # Reuse the compiler invocation and complete artifact collection,
        # while this fixture has its own independent word model.
        env = os.environ.copy()
        env = {k:v for k,v in env.items() if not k.startswith("GUARDCERT_")}
        env.update(GUARDCERT_AFFINE_MODE=name,GUARDCERT_AFFINE_PROFILE="inferred",GUARDCERT_AFFINE_CAP="4")
        with (directory/"compile.log").open("w") as log:
            subprocess.run([str(stage.suite.COMPILER),"-conf",str(stage.suite.COMPILER.parent/"compcert.ini"),
                "-stdlib",str(stage.suite.COMPILER.parent/"runtime"),"-dclight","-S","-o",str(directory/"program.s"),str(SOURCE)],
                cwd=directory,env=env,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=240)
        subprocess.run(["gcc","-no-pie",str(directory/"program.s"),"-o",str(directory/"program")],check=True)
        actual = subprocess.check_output([str(directory/"program")],text=True)
        assert actual == expected
        (directory/"output.txt").write_text(actual)
        results[name] = {"artifacts":{p:sha(directory/p) for p in
            ["program.s","program",SOURCE.stem+".light.c","compile.log","output.txt"]}}
    report = {"status":"passed","optimizer_coverage":"not-supported","paper":PAPER,
        "source_adaptation":"flat fixed 16x16x5 layout, Mint32 data, replacement arithmetic body; not full NPB BT",
        "gap":"frontend cannot describe root load-plus-one or loaded child bound in a recursive affine nest",
        "original_three_loop_body_preserved":True,"calls_per_configuration":len(CASES),
        "configurations":results,"verification_script_sha256":sha(Path(__file__)),"harness_sha256":sha(stage.SELF),
        "compiler_sha256":sha(stage.suite.COMPILER),"proof_report_sha256":sha(stage.suite.PROOF),
        "helper_sources":{p:sha(ROOT/p) for p in ["scripts/loaded_affine_reduced.py",
            "scripts/native_loaded_affine_multi.py","scripts/native_zero_trip.py","scripts/audit_interface_clight.py"]},
        "source_sha256":sha(SOURCE),"reference_sha256":sha(WORK/"reference-output.txt"),
        "timing_or_profitability_measured":False}
    (WORK/"report.json").write_text(json.dumps(report,indent=2)+"\n")
    validate()
    print(json.dumps({"status":"passed","assembly_calls":2*len(CASES),
        "optimizer_coverage":"not-supported","report_sha256":sha(WORK/"report.json")},indent=2))


if __name__ == "__main__":
    main()
