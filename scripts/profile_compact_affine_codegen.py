"""Compare one actual rank-three compile with checked compaction enabled/disabled.

This is a bounded diagnostic, not a statistical compile-time benchmark or a
runtime profitability experiment. Both runs use the same source and binary.
"""
import argparse
import json
import os
from pathlib import Path
import signal
import subprocess
import time

import native_compact_affine_validation as native
from audit_interface_clight import ROOT, sha

WORK=ROOT / "build/selected-affine-pipeline/compact-codegen-profile-v1"


def one_selected_source():
    source=native.fixtures.source_text(False)
    start=source.index("void triangular3(")
    finish=source.index("void descending3(",start)
    function=source[start:finish]
    begin=function.index("for(;i<n;i++){")
    end=function.index("out_i=",begin)
    loop=function[begin:end].strip()
    assert function.count(loop)==1
    selected=function.replace(loop,"\n#pragma scop\n"+loop+"\n#pragma endscop\n")
    source=source[:start]+selected+source[finish:]
    assert source.count("#pragma scop")==1
    return source


def compile_once(work,source,binary,pluto,enabled,deadline):
    directory=work / ("enabled" if enabled else "disabled")
    directory.mkdir()
    environment={key:value for key,value in os.environ.items() if not key.startswith("GUARDCERT_")}
    environment.update(GUARDCERT_TENSOR_MODE="pipeline",GUARDCERT_POLYHEDRAL_MODE="tile",
        GUARDCERT_PLUTO=str(pluto),GUARDCERT_PIPELINE_DUMP=str(directory/"phases"),
        GUARDCERT_SCOP_DIAGNOSTICS="1",GUARDCERT_PIPELINE_CHECK_DIAGNOSTICS="1",
        GUARDCERT_CANONICAL_DIAGNOSTICS=str(directory/"oracle-counters.txt"),
        GUARDCERT_AFFINE_FLOOR="-2",GUARDCERT_AFFINE_CAP="4",
        GUARDCERT_AFFINE_BOUND_LOW="-2",GUARDCERT_AFFINE_BOUND_HIGH="4")
    if not enabled:
        environment["GUARDCERT_CANONICALIZE"]="disabled"
    command=[str(binary),"-fall","-stdlib",str(binary.parent/"runtime"),"-dclight",
             "-S","-o",str(directory/"program.s"),str(source)]
    (directory/"command.json").write_text(json.dumps({"argv":command,"environment":{
        key:value for key,value in environment.items() if key.startswith("GUARDCERT_")}},indent=2)+"\n")
    started=time.monotonic()
    with (directory/"compile.log").open("x") as log:
        process=subprocess.Popen(command,cwd=directory,env=environment,stdout=log,
                                 stderr=subprocess.STDOUT,start_new_session=True)
        print(json.dumps({"mode":directory.name,"compiler_pid":process.pid,"deadline_seconds":deadline}),flush=True)
        try:
            process.wait(timeout=deadline)
            timed_out=False
        except subprocess.TimeoutExpired:
            timed_out=True
            os.killpg(process.pid,signal.SIGKILL)
            process.wait()
    elapsed=time.monotonic()-started
    phases=[]
    for phase in sorted((directory/"phases").glob("guardcert-signed-affine-phase-*")):
        phases.append({"directory":str(phase.relative_to(ROOT)),
            "rank":int((phase/"source-rank.txt").read_text()),
            "affine_validation":(phase/"affine-result.txt").exists(),
            "tiling_validation":(phase/"tiling-result.txt").exists(),
            "prepared_codegen_completed":(phase/"raw-generated.loop").exists(),
            "whole_candidate_check":(phase/"whole-candidate-check-diagnostic.txt").read_text().strip()
                if (phase/"whole-candidate-check-diagnostic.txt").exists() else None})
    result={"mode":directory.name,"elapsed_wall_seconds":elapsed,"timeout":timed_out,
            "exit_code":process.returncode,"assembly_emitted":(directory/"program.s").exists(),
            "phases":phases,"deadline_seconds":deadline}
    if enabled:
        assert not timed_out and process.returncode==0,result
        assert any(p["rank"]==3 and p["whole_candidate_check"]=="valid=true\nalarm-free=true" for p in phases),result
        subprocess.run(["gcc","-no-pie",str(directory/"program.s"),"-o",str(directory/"program")],
                       check=True,capture_output=True)
        observed=subprocess.check_output([str(directory/"program")],text=True,timeout=120)
        (directory/"output.txt").write_text(observed)
        assert observed==native.fixtures.expected_output()
        result["full_output_calls"]=len(native.fixtures.CASES)
    (directory/"result.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result),flush=True)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work",type=Path,default=WORK)
    parser.add_argument("--deadline",type=int,default=90)
    parser.add_argument("--validate",action="store_true")
    args=parser.parse_args()
    work=args.work.resolve()
    assert work.is_relative_to(ROOT/"build/selected-affine-pipeline")
    if args.validate or (work/"report.json").exists():
        report=json.loads((work/"report.json").read_text())
        assert report["status"]=="observed"
        for path,digest in report["bindings"].items(): assert sha(ROOT/path)==digest,path
        native.check_build()
        print(json.dumps({"status":"validated","report_sha256":sha(work/"report.json")}))
        return
    assert 1<=args.deadline<=600
    bindings=native.check_build()
    pluto=native.scheduler.validate()
    work.mkdir(parents=True,exist_ok=False)
    source=work/"one-marked-rank-three.c"
    source.write_text(one_selected_source())
    results=[compile_once(work,source,native.COMPILER,ROOT/pluto["binary"],enabled,args.deadline)
             for enabled in (True,False)]
    bindings|={path:sha(path) for path in [Path(__file__),ROOT/"scripts/native_compact_affine_validation.py",
        ROOT/"scripts/selected_compact_affine_fixtures.py",native.scheduler.REPORT,ROOT/pluto["binary"]]}
    bindings|={path:sha(path) for path in work.rglob("*") if path.is_file()}
    report={"status":"observed","results":results,"same_source_and_binary":True,
            "replicates_per_mode":1,"statistical_compile_time_benchmark":False,
            "runtime_profitability_measured":False,"full_goal_complete":False,
            "bindings":{str(path.relative_to(ROOT)):digest for path,digest in bindings.items()}}
    (work/"report.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"status":"observed","report_sha256":sha(work/"report.json")}))


if __name__=="__main__":
    main()
