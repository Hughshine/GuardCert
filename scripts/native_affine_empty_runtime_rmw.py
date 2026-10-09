"""Check empty, previous-candidate and original paths in one emitted program."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess

import native_affine_empty_runtime as native
import native_affine_observation as historical
import affine_observation_fixtures as fixtures
from audit_interface_clight import ROOT,sha
from native_zero_trip import function_body
from native_affine_nest_paths import closing_brace
from native_memory_layout_sequence_paths import printer_for_gcc

WORK=ROOT/"build/affine-empty-runtime/native-rmw-v1"
BASELINE=ROOT/"build/affine-empty-signed/regression-v1/report.json"


def empty_selections(body):
    for match in re.finditer(r"if\s*\(\s*\$[0-9]+\s*\)\s*\{",body):
        yes=match.end()-1
        yes_end=closing_brace(body,yes)
        alternate=re.match(r"\s*else\s*\{",body[yes_end+1:])
        if not alternate:
            continue
        no=yes_end+1+alternate.end()-1
        no_end=closing_brace(body,no)
        if "for (" not in body[yes:yes_end] and re.search(r"\$i\s*<\s*\*\$bound",body[no:no_end]):
            yield yes,no


def compile_run(name,configuration,pluto,work):
    marked,mode,kind,extra=configuration
    directory=work/name;directory.mkdir()
    source=directory/"regions.c";source.write_text(fixtures.source_text(marked))
    env={key:value for key,value in os.environ.items()if not key.startswith("GUARDCERT_")}
    env.update(GUARDCERT_TENSOR_MODE=kind,GUARDCERT_POLYHEDRAL_MODE=mode,GUARDCERT_PLUTO=str(pluto),
        GUARDCERT_PIPELINE_DUMP=str(directory/"phases"),GUARDCERT_SCOP_DIAGNOSTICS="1",
        GUARDCERT_PIPELINE_CHECK_DIAGNOSTICS="1",GUARDCERT_AFFINE_ROW_CAP="4",
        GUARDCERT_AFFINE_COLUMN_CAP="8",GUARDCERT_AFFINE_GEOMETRY_CAP="4",GUARDCERT_AFFINE_EXTENT="8192")
    env.update(extra)
    command=[str(native.COMPILER),"-fall","-stdlib",str(native.COMPILER.parent/"runtime"),"-dclight",
        "-S","-o",str(directory/"program.s"),str(source)]
    (directory/"compile-command.json").write_text(json.dumps({"argv":command,
        "environment":{key:value for key,value in env.items()if key.startswith("GUARDCERT_")}},indent=2)+"\n")
    with(directory/"compile.log").open("x")as log:
        subprocess.run(command,cwd=directory,env=env,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=600)
    expected=fixtures.expected_output()
    subprocess.run(["gcc","-no-pie",str(directory/"program.s"),"-o",str(directory/"program")],check=True,capture_output=True)
    output=subprocess.check_output([str(directory/"program")],text=True,timeout=120)
    (directory/"output.txt").write_text(output);assert output==expected,(name,"assembly complete output")
    subprocess.run(["gcc","-O0","-fwrapv",str(source),"-o",str(directory/"reference")],check=True,capture_output=True)
    output=subprocess.check_output([str(directory/"reference")],text=True,timeout=120)
    (directory/"reference-output.txt").write_text(output);assert output==expected,(name,"original source and word model")
    dump=(directory/"regions.light.c").read_text()
    instrumented=printer_for_gcc(dump)
    instrumented=instrumented[:instrumented.index("\nint guard_original_main(void)")]
    captures,empty_sites,candidate_sites,fallback_occurrences={},{},{},{}
    for slot,fn in enumerate(fixtures.NAMES):
        body=function_body(instrumented,fn)
        captures[fn]=len(historical.capture_sites(body))
        empty=list(empty_selections(body));candidate=list(historical.selections(body))
        empty_sites[fn],candidate_sites[fn]=len(empty),len(candidate)
        loops=list(re.finditer(r"for\s*\([^;]*;\s*1\s*;\s*\$i\s*=",body))
        original=[]
        for loop in loops:
            opening=body.index("{",loop.end());end=closing_brace(body,opening)
            if re.search(r"\$i\s*<\s*\*\$bound",body[opening:end]):
                original.append(loop.start())
        fallback_occurrences[fn]=len(original);assert len(original)==1,(name,fn,"single original fallback AST")
        edits=[(yes+1,f"guard_empty[{slot}]++;")for yes,_ in empty]
        edits +=[(yes+1,f"guard_candidate[{slot}]++;")for yes,_ in candidate]
        edits +=[(position,f"guard_fallback[{slot}]++;\n")for position in original]
        changed=body
        for position,code in sorted(edits,reverse=True):
            changed=changed[:position]+code+changed[position:]
        definition=re.search(r"\b"+re.escape(fn)+r"\([^;{}]*\)\s*\{",instrumented)
        assert definition
        start=definition.end();end=closing_brace(instrumented,start-1)
        assert instrumented[start:end]==body
        instrumented=instrumented[:start]+changed+instrumented[end:]
    installed=name not in("disabled","unannotated")
    candidate_installed=name in("tile","schedule")
    assert empty_sites==dict(zip(fixtures.NAMES,[1,1,0]if installed else[0,0,0])),(name,empty_sites)
    assert candidate_sites==dict(zip(fixtures.NAMES,[1,1,0]if candidate_installed else[0,0,0])),(name,candidate_sites)
    assert captures==dict(zip(fixtures.NAMES,[2,2,0]if candidate_installed else[1,1,0]if installed else[0,0,0])),(name,captures)
    phases=sorted((directory/"phases").glob("guardcert-signed-affine-phase-*"))
    accepted_phases=[]
    for phase in phases:
        if(phase/"refusal.txt").exists():
            assert not(phase/"receipt.txt").exists();continue
        if(phase/"receipt.txt").exists():
            assert(phase/"request-adapter.txt").read_text().startswith("conditional-loaded-affine-snapshot-request\nsource-model-unchanged=true\n")
            assert(phase/"affine-result.txt").read_text()=="accepted\n"
            assert(phase/"tiling-result.txt").read_text()=="accepted\n"
            assert(phase/"whole-candidate-check-diagnostic.txt").read_text()=="valid=true\nalarm-free=true\n"
            assert all((phase/file).exists()for file in("source.loop","before.scop","generated.loop","raw-generated.loop"))
            accepted_phases.append(phase.name)
    if candidate_installed:
        assert len(accepted_phases)>=2
    if not installed:
        assert not phases
    calls=[]
    for case in fixtures.CASES:
        slot=case[0]
        calls.append(f"guard_empty[{slot}]=0;guard_candidate[{slot}]=0;guard_fallback[{slot}]=0;run_case("+
            ",".join(map(str,case))+f');printf("paths %d %d %d\\n",guard_empty[{slot}],guard_candidate[{slot}],guard_fallback[{slot}]);')
    diagnostic=directory/"branch-diagnostic.c"
    diagnostic.write_text("int guard_empty[3],guard_candidate[3],guard_fallback[3];\n"+instrumented+
        "\nint main(void){\n"+"\n".join(calls)+"\nreturn 0;}\n")
    with(directory/"branch-gcc.log").open("x")as log:
        subprocess.run(["gcc","-O0","-fwrapv","-Wno-builtin-declaration-mismatch","-Wno-discarded-qualifiers",
            str(diagnostic),"-o",str(directory/"branch-diagnostic")],stdout=log,stderr=subprocess.STDOUT,check=True)
    output=subprocess.check_output([str(directory/"branch-diagnostic")],text=True,timeout=120)
    (directory/"branch-output.txt").write_text(output)
    lines=output.splitlines();assert len(lines)==2*len(fixtures.CASES)
    assert"\n".join(lines[::2])+"\n"==expected,(name,"Clight complete output")
    paths=[]
    for case,line in zip(fixtures.CASES,lines[1::2]):
        slot,kind,start,n,m,a=case
        empty,candidate,fallback=map(int,line.split()[1:])
        assert empty+candidate+fallback==1,(name,case,"actual exclusive execution path")
        effective_n=m if kind==8 else n
        predicted=installed and slot<2 and start==0 and(effective_n<=0 or
            0<effective_n<=4 and -4<=m<4 and (2 if slot==1 else 1)*(effective_n-1)+m<=0)
        assert empty==int(predicted),(name,case,"actual empty choice",empty,predicted)
        paths.append({"input":list(case),"empty":empty,"candidate":candidate,
            "fast":empty+candidate,"refused":fallback if installed and slot<2 else 0,
            "unmarked":int(not installed or slot>=2)})
    return {"assembly_calls":len(paths),"Clight_calls":len(paths),"root_capture_occurrences":captures,
        "empty_installed_sites":empty_sites,"candidate_installed_sites":candidate_sites,
        "original_fallback_occurrences":fallback_occurrences,"accepted_optimizer_phases":accepted_phases,
        "actual_empty_selections":sum(row["empty"]for row in paths),
        "actual_candidate_selections":sum(row["candidate"]for row in paths),
        "actual_fast_selections":sum(row["fast"]for row in paths),
        "actual_refused_selections":sum(row["refused"]for row in paths),"paths":paths}


def validate():
    native.check_build()
    report=json.loads((WORK/"report.json").read_text())
    assert report["status"]=="passed"and report["proved_entrypoint"]==native.builder.ENTRY
    for path,digest in report["bindings"].items():
        assert sha(ROOT/path)==digest,path
    return report


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument("--validate",action="store_true")
    args=parser.parse_args()
    if args.validate or(WORK/"report.json").exists():
        report=validate();print(json.dumps({"status":"validated","assembly_calls":report["assembly_calls"]}));return
    bindings=native.check_build();assert not WORK.exists();WORK.mkdir()
    baseline=json.loads(BASELINE.read_text());assert baseline["status"]=="passed"
    for path,digest in baseline["bindings"].items():
        assert sha(ROOT/path)==digest,path
    pluto=ROOT/native.scheduler.validate()["binary"]
    configurations={}
    try:
        for name,configuration in native.CONFIGURATIONS.items():
            row=compile_run(name,configuration,pluto,WORK);configurations[name]=row
            if name in("tile","schedule"):
                old=baseline["rmw_configurations"][name]["paths"]
                for new,prior in zip(row["paths"],old,strict=True):
                    assert new["input"]==prior["input"]
                    assert new["fast"]>=prior["fast"],(name,new,"previous acceptance lost")
                    if not new["empty"]:
                        assert new["candidate"]==prior["fast"],(name,new,"previous candidate path changed")
            print(name,json.dumps({key:value for key,value in row.items()if key!="paths"}),flush=True)
    except Exception as error:
        (WORK/"native-script.py").write_bytes(Path(__file__).read_bytes())
        (WORK/"failure.json").write_text(json.dumps({"status":"failed","reason":repr(error)},indent=2)+"\n");raise
    bindings|={BASELINE:sha(BASELINE),native.scheduler.REPORT:sha(native.scheduler.REPORT),pluto:sha(pluto),
        ROOT/"scripts/native_affine_empty_runtime_rmw.py":sha(Path(__file__)),
        ROOT/"scripts/native_affine_empty_runtime.py":sha(ROOT/"scripts/native_affine_empty_runtime.py"),
        ROOT/"scripts/native_affine_observation.py":sha(ROOT/"scripts/native_affine_observation.py"),
        ROOT/"scripts/affine_observation_fixtures.py":sha(ROOT/"scripts/affine_observation_fixtures.py"),
        ROOT/"scripts/native_zero_trip.py":sha(ROOT/"scripts/native_zero_trip.py"),
        ROOT/"scripts/native_affine_nest_paths.py":sha(ROOT/"scripts/native_affine_nest_paths.py"),
        ROOT/"scripts/native_memory_layout_sequence_paths.py":sha(ROOT/"scripts/native_memory_layout_sequence_paths.py")}
    bindings|={path:sha(path)for path in WORK.rglob("*")if path.is_file()}
    report={"status":"passed","proved_entrypoint":native.builder.ENTRY,"configurations":configurations,
        "assembly_calls":sum(row["assembly_calls"]for row in configurations.values()),
        "Clight_calls":sum(row["Clight_calls"]for row in configurations.values()),
        "array_cells_checked_per_call":2*fixtures.SIZE,"public_exits_and_continuation_checked":True,
        "actual_empty_candidate_original_paths_distinguished":True,"previous_fast_paths_retained":True,
        "previous_candidate_paths_unchanged_when_empty_refuses":True,"real_source_read_prefix_exercised":True,
        "profitability_measured":False,"preserved_failed_runs":[],
        "bindings":{str(path.relative_to(ROOT)):digest for path,digest in bindings.items()}}
    (WORK/"report.json").write_text(json.dumps(report,indent=2)+"\n")
    validate();print(json.dumps({"status":"passed","assembly_calls":report["assembly_calls"],
        "report_sha256":sha(WORK/"report.json")}),flush=True)


if __name__=="__main__":
    main()
