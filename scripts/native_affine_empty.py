"""Execute the selected empty-affine compiler and inspect actual fallback paths."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess

import audit_affine_empty as audit
import build_affine_empty_compiler as builder
import affine_empty_fixtures as fixtures
import build_pipeline_pluto as scheduler
from audit_interface_clight import ROOT,sha
from native_zero_trip import function_body
from native_affine_nest_paths import closing_brace
from native_memory_layout_sequence_paths import printer_for_gcc

WORK=ROOT/"build/affine-empty/native-v4"
COMPILER=builder.WORK/"ccomp"
CONFIGURATIONS={"tile":(True,"tile","pipeline",{}),
    "schedule":(True,"schedule","pipeline",{}),
    "unannotated":(False,"tile","pipeline",{}),
    "disabled":(True,"tile","disabled",{}),
    "scheduler-failure":(True,"tile","pipeline",{"GUARDCERT_PLUTO":"/usr/bin/false"}),
    "resource-refusal":(True,"tile","pipeline",{"GUARDCERT_FM_ROWS":"0"})}


def check_build():
    path=COMPILER.parent/".guard-build.json"
    stamp=json.loads(path.read_text())
    assert stamp["proved_entrypoint"]==builder.ENTRY
    assert stamp["empty_header_only_builder_after_existing_registry"]
    assert stamp["empty_negative_child_public_counter_zero"]
    assert stamp["empty_outer_skips_child_load"]
    assert stamp["empty_no_body_pointer_observation_requirement"]
    audit.validate()
    bindings={COMPILER:stamp["compiler_sha256"],path:sha(path),builder.PROOF:stamp["proof_report_sha256"],
        ROOT/"scripts/build_affine_empty_compiler.py":stamp["build_script_sha256"],
        COMPILER.parent/"driver/Driver.ml":stamp["driver_sha256"],
        COMPILER.parent/"cparser/Parse.ml":stamp["parser_sha256"],
        COMPILER.parent/"extract_tensor_regions.v":stamp["extraction_sha256"]}
    bindings|={ROOT/name:digest for name,digest in
        (stamp["proof_bindings"]|stamp["native_sources"]|stamp["build_helpers"]).items()}
    for source,digest in bindings.items():
        assert sha(source)==digest,source
    return bindings


def compile_run(name,configuration,pluto,work):
    marked,mode,kind,extra=configuration
    directory=work/name; directory.mkdir()
    source=directory/"regions.c"; source.write_text(fixtures.source_text(marked))
    env={key:value for key,value in os.environ.items()if not key.startswith("GUARDCERT_")}
    env.update(GUARDCERT_TENSOR_MODE=kind,GUARDCERT_POLYHEDRAL_MODE=mode,GUARDCERT_PLUTO=str(pluto),
        GUARDCERT_PIPELINE_DUMP=str(directory/"phases"),GUARDCERT_AFFINE_ROW_CAP="4",
        GUARDCERT_AFFINE_COLUMN_CAP="8",GUARDCERT_AFFINE_GEOMETRY_CAP="8",GUARDCERT_AFFINE_EXTENT="8192")
    env.update(extra)
    command=[str(COMPILER),"-fall","-stdlib",str(COMPILER.parent/"runtime"),"-dclight","-S",
        "-o",str(directory/"program.s"),str(source)]
    (directory/"compile-command.json").write_text(json.dumps({"argv":command,
        "environment":{key:value for key,value in env.items()if key.startswith("GUARDCERT_")}},indent=2)+"\n")
    with(directory/"compile.log").open("x")as log:
        subprocess.run(command,cwd=directory,env=env,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=600)
    expected=fixtures.expected_output()
    subprocess.run(["gcc","-no-pie",str(directory/"program.s"),"-o",str(directory/"program")],check=True,capture_output=True)
    output=subprocess.check_output([str(directory/"program")],text=True,timeout=120)
    (directory/"output.txt").write_text(output); assert output==expected,(name,"Asm complete outputs")
    subprocess.run(["gcc","-O0","-fwrapv",str(source),"-o",str(directory/"reference")],check=True,capture_output=True)
    output=subprocess.check_output([str(directory/"reference")],text=True,timeout=120)
    (directory/"reference-output.txt").write_text(output); assert output==expected,(name,"source word model")
    dump=(directory/"regions.light.c").read_text()
    counts={fn:len(re.findall(r"\$[0-9]+\s*=\s*\*\$bound\s*;",function_body(dump,fn)))for fn in fixtures.NAMES}
    installed=name not in("disabled","unannotated")
    assert counts==dict(zip(fixtures.NAMES,[1,1,0,1]if installed else[0,0,0,0])),(name,counts)
    instrumented=printer_for_gcc(dump)
    instrumented=instrumented[:instrumented.index("\nint guard_original_main(void)")]
    for slot,fn in enumerate(fixtures.NAMES):
        body=function_body(instrumented,fn)
        loops=list(re.finditer(r"for\s*\([^;]*;\s*1\s*;\s*\$i\s*=",body))
        assert loops,(name,fn,"actual original fallback occurrences")
        changed=body
        for loop in reversed(loops):
            start=loop.start(); opening=body.index("{",loop.end()); end=closing_brace(body,opening)
            assert re.search(r"\$i\s*<\s*\*\$bound",body[opening:end]),(name,fn,"original loaded test")
            changed=changed[:start]+f"{{guard_fallback[{slot}]++;"+changed[start:end+1]+"}"+changed[end+1:]
        definition=re.search(r"\b"+re.escape(fn)+r"\([^;{}]*\)\s*\{",instrumented)
        assert definition
        start=definition.end(); end=closing_brace(instrumented,start-1)
        assert instrumented[start:end]==body
        instrumented=instrumented[:start]+changed+instrumented[end:]
    calls=[]
    for case in fixtures.CASES:
        slot=case[0]
        calls.append(f"guard_fallback[{slot}]=0;run_case("+",".join(map(str,case))+
            f');printf("path %d\\n",guard_fallback[{slot}]);')
    diagnostic=directory/"branch-diagnostic.c"
    diagnostic.write_text("int guard_fallback[4];\n"+instrumented+"\nint main(void){\n"+"\n".join(calls)+"\nreturn 0;}\n")
    with(directory/"branch-gcc.log").open("x")as log:
        subprocess.run(["gcc","-O0","-fwrapv","-Wno-builtin-declaration-mismatch","-Wno-discarded-qualifiers",
            str(diagnostic),"-o",str(directory/"branch-diagnostic")],stdout=log,stderr=subprocess.STDOUT,check=True)
    output=subprocess.check_output([str(directory/"branch-diagnostic")],text=True,timeout=120)
    (directory/"branch-output.txt").write_text(output)
    lines=output.splitlines(); assert len(lines)==2*len(fixtures.CASES)
    assert"\n".join(lines[::2])+"\n"==expected,(name,"Clight complete outputs")
    paths=[]
    for case,line in zip(fixtures.CASES,lines[1::2]):
        slot,kind,start,n,m,a=case
        refused=int(line.split()[1]); assert refused in(0,1)
        fast=1-refused if counts[fixtures.NAMES[slot]]else 0
        if counts[fixtures.NAMES[slot]]:
            if start==0 and n<=0:
                assert fast==1,(name,"outer empty skips M",case)
            elif start==0 and 0<n<=4 and 0<=m<8 and fixtures.empty(slot,start,n,m):
                assert fast==1,(name,"all children empty",case)
            else:
                assert fast==0,(name,"actual source fallback",case)
        paths.append({"input":list(case),"fast":fast,"refused":refused if counts[fixtures.NAMES[slot]]else 0,
            "unmarked":0 if counts[fixtures.NAMES[slot]]else 1})
    return{"assembly_calls":len(paths),"Clight_calls":len(paths),"source_width":fixtures.STYLE,"installed_sites":counts,"paths":paths,
        "actual_fast_selections":sum(row["fast"]for row in paths),
        "actual_refused_selections":sum(row["refused"]for row in paths),
        "unmarked_calls":sum(row["unmarked"]for row in paths),
        "NULL_body_pointer_calls":sum(case[1]==1 for case in fixtures.CASES),
        "NULL_child_pointer_calls":sum(case[1]==2 for case in fixtures.CASES),
        "undefined_body_word_calls":sum(case[0]==3 for case in fixtures.CASES),
        "data_header_overlap_calls":sum(case[1]==3 for case in fixtures.CASES)}


def validate(work=WORK):
    report=json.loads((work/"report.json").read_text()); assert report["status"]=="passed"
    assert report["proved_entrypoint"]==builder.ENTRY
    check_build()
    for path,digest in report["bindings"].items():
        assert sha(ROOT/path)==digest,path
    return report


def main():
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument("--validate",action="store_true")
    args=parser.parse_args()
    if args.validate or(WORK/"report.json").exists():
        report=validate(); print(json.dumps({"status":"validated","assembly_calls":report["assembly_calls"]})); return
    assert not WORK.exists(); bindings=check_build()
    pluto=ROOT/scheduler.validate()["binary"]
    WORK.mkdir()
    configurations={}
    try:
        for style in("add","subtract"):
            fixtures.configure(style)
            directory=WORK/style; directory.mkdir()
            for name,configuration in CONFIGURATIONS.items():
                key=style+"-"+name
                configurations[key]=compile_run(name,configuration,pluto,directory)
                print(key,json.dumps({key:value for key,value in configurations[key].items()if key!="paths"}),flush=True)
    except Exception as error:
        (WORK/"native-script.py").write_bytes(Path(__file__).read_bytes())
        (WORK/"failure.json").write_text(json.dumps({"status":"failed","reason":repr(error)},indent=2)+"\n"); raise
    bindings|={ROOT/path:sha(ROOT/path)for path in["scripts/affine_empty_fixtures.py","scripts/native_affine_empty.py",
        "scripts/native_zero_trip.py","scripts/native_affine_nest_paths.py","scripts/native_memory_layout_sequence_paths.py",
        "scripts/build_pipeline_pluto.py"]}
    bindings|={scheduler.REPORT:sha(scheduler.REPORT),pluto:sha(pluto)}
    for failed in("native-v1","native-v2","native-v3"):
        bindings|={path:sha(path)for path in(ROOT/"build/affine-empty"/failed).rglob("*")if path.is_file()}
    bindings|={ROOT/"build/affine-empty"/name:sha(ROOT/"build/affine-empty"/name)
        for name in("compiler-build-v1.log","compiler-build-v1.json")}
    bindings|={path:sha(path)for path in WORK.rglob("*")if path.is_file()}
    report={"status":"passed","proved_entrypoint":builder.ENTRY,"configurations":configurations,
        "assembly_calls":sum(row["assembly_calls"]for row in configurations.values()),
        "Clight_calls":sum(row["Clight_calls"]for row in configurations.values()),
        "array_cells_checked_per_call":2*fixtures.SIZE,"public_exits_and_continuation_checked":True,
        "runtime_source_preexecution_used":False,"empty_rewrite_uses_C_opt_certificate":False,
        "previously_installed_polyhedral_candidates_are_not_replaced":True,"profitability_measured":False,
        "negative_header_parameter_fast_path_supported":False,
        "expanded_tree_fallback_occurrences_materialized":True,
        "preserved_failed_runs":["build/affine-empty/native-v1/failure.json","build/affine-empty/native-v2/failure.json",
            "build/affine-empty/native-v3/failure.json"],
        "bindings":{str(path.relative_to(ROOT)):digest for path,digest in bindings.items()}}
    (WORK/"report.json").write_text(json.dumps(report,indent=2)+"\n")
    validate(); print(json.dumps({"status":"passed","assembly_calls":report["assembly_calls"],
        "report_sha256":sha(WORK/"report.json")}),flush=True)


if __name__=="__main__":
    main()
