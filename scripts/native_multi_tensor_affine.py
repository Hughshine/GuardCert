"""Run marked multi-array C through the new proved compiler and inspect separate Clight paths."""
import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

import build_multi_tensor_affine_compiler as builder
import build_pipeline_pluto as scheduler
import multi_tensor_affine_fixtures as fixtures
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/multi-tensor-affine-native/native-v4"
COMPILER = builder.WORK / "ccomp"
CONFIGURATIONS = {
    "row-nonunit": (False, True, "tile", "normal", [2,3,2]),
    "row-partial-unit": (False, True, "tile", "normal", [1,3,2]),
    "row-all-unit": (False, True, "tile", "normal", [1,1,1]),
    "column-nonunit": (True, True, "tile", "normal", [2,3,2]),
    "row-schedule": (False, True, "schedule", "normal", [2,3,2]),
    "unannotated": (False, False, "tile", "normal", [2,3,2]),
    "disabled": (False, True, "tile", "disabled", [2,3,2]),
    "scheduler-failure": (False, True, "tile", "failure", [2,3,2]),
}
HELPERS = ["scripts/native_multi_tensor_affine.py", "scripts/multi_tensor_affine_fixtures.py",
           "scripts/build_multi_tensor_affine_compiler.py", "scripts/build_pipeline_pluto.py",
           "scripts/native_selected_regions.py", "scripts/native_zero_trip.py",
           "scripts/native_affine_nest_paths.py", "scripts/native_memory_layout_sequence_paths.py"]


def check_build():
    stamp_path = COMPILER.parent / ".guard-build.json"
    stamp = json.loads(stamp_path.read_text())
    assert stamp["proved_entrypoint"] == builder.ENTRY
    assert stamp["selected_only_discovery_and_installation"]
    assert stamp["external_scheduler_callback_connected"] and stamp["prepared_codegen_candidate_producer"]
    bindings = {COMPILER: stamp["compiler_sha256"], stamp_path: sha(stamp_path),
                ROOT/builder.PROOF: stamp["proof_report_sha256"],
                COMPILER.parent/"driver/Driver.ml": stamp["driver_sha256"],
                COMPILER.parent/"cparser/Parse.ml": stamp["parser_sha256"],
                COMPILER.parent/"extract_tensor_regions.v": stamp["extraction_sha256"],
                ROOT/"scripts/build_multi_tensor_affine_compiler.py": stamp["build_script_sha256"]}
    bindings |= {ROOT/path: digest for path,digest in
                 (stamp["proof_bindings"] | stamp["native_sources"] | stamp["build_helpers"]).items()}
    for path,digest in bindings.items():
        assert sha(path)==digest,path
    return bindings


def dispatch_sites(body):
    for match in re.finditer(r"if\s*\(\s*\$[0-9]+\s*\)\s*\{", body):
        yes=match.end()-1; finish=fixtures.closing_brace(body,yes)
        no=re.match(r"\s*else\s*\{",body[finish+1:])
        if no is None:
            continue
        fallback=finish+1+no.end()-1; end=fixtures.closing_brace(body,fallback)
        if re.search(r"\$i\s*<\s*\$n", body[fallback:end]) and re.search(r"\*\s*\(\s*\$a", body[yes:finish]):
            yield yes,fallback


def compile_run(name, configuration, pluto, reuse=None):
    column,marked,mode,kind,sizes=configuration
    directory=WORK/name
    reused = reuse is not None and (reuse/name/"reference-output.txt").exists()
    if reused:
        assert not (reuse/"report.json").exists(), "Reuse only the failed detector checkpoint"
        assert "installed-sites" in json.loads((reuse/"failure.json").read_text())["error"]
        assert (reuse/name/"regions.c").read_text()==fixtures.source_text(column,marked)
        shutil.copytree(reuse/name,directory)
        (directory/"reused-compilation.json").write_text(json.dumps({
            "from":str((reuse/name).relative_to(ROOT)),
            "reason":"Whitespace-sensitive installation detector failed after native and reference outputs passed",
            "compiler_sha256":sha(COMPILER),
            "source_sha256":sha(directory/"regions.c"),
            "assembly_sha256":sha(directory/"program.s")},indent=2)+"\n")
    else:
        directory.mkdir()
        (directory/"regions.c").write_text(fixtures.source_text(column,marked))
    source=directory/"regions.c"
    env={key:value for key,value in os.environ.items() if not key.startswith("GUARDCERT_")}
    env.update(GUARDCERT_TENSOR_MODE="disabled" if kind=="disabled" else "pipeline",
               GUARDCERT_POLYHEDRAL_MODE=mode,
               GUARDCERT_PLUTO="/usr/bin/false" if kind=="failure" else str(pluto),
               GUARDCERT_TILE_SIZES=",".join(map(str,sizes)),
               GUARDCERT_PIPELINE_DUMP=str(directory/"phases"),
               GUARDCERT_SCOP_DIAGNOSTICS="1",GUARDCERT_TENSOR_DIAGNOSTICS="1")
    if not reused:
        with (directory/"compile.log").open("x") as log:
            subprocess.run([str(COMPILER),"-fall","-stdlib",str(COMPILER.parent/"runtime"),
                            "-dclight","-S","-o",str(directory/"program.s"),str(source)],
                           cwd=directory,env=env,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=600)
        subprocess.run(["gcc","-no-pie",str(directory/"program.s"),"-o",str(directory/"program")],check=True,capture_output=True)
        output=subprocess.check_output([str(directory/"program")],text=True,timeout=90)
        (directory/"output.txt").write_text(output)
        subprocess.run(["gcc","-O0","-fwrapv",str(source),"-o",str(directory/"reference")],check=True,capture_output=True)
        reference=subprocess.check_output([str(directory/"reference")],text=True,timeout=90)
        (directory/"reference-output.txt").write_text(reference)
    output=(directory/"output.txt").read_text()
    assert output==fixtures.expected_output(column),(name,"assembly-output")
    reference=(directory/"reference-output.txt").read_text()
    assert reference==fixtures.expected_output(column),(name,"reference-output")
    installed=marked and kind=="normal"
    dump=(directory/"regions.light.c").read_text()
    sites={function:len(list(dispatch_sites(fixtures.function_body(dump,function)))) for function in fixtures.NAMES}
    expected=dict(zip(fixtures.NAMES,fixtures.INSTALLED if installed else [0]*len(fixtures.NAMES)))
    assert sites==expected,(name,"installed-sites",sites,expected)
    phases=sorted((directory/"phases").glob("guardcert-phase-*"))
    assert len(phases)==(5 if marked and kind!="disabled" else 0),(name,"phase-count",len(phases))
    for phase in phases:
        assert (phase/"source.loop").exists() and (phase/"before.scop").exists()
        if installed:
            assert (phase/"receipt.txt").exists()
            assert (phase/"affine-result.txt").read_text()=="accepted\n"
            assert (phase/"tiling-result.txt").read_text()=="accepted\n"
            assert (phase/"generated.loop").exists() and (phase/"raw-statement-0.loop").exists()
            assert "--identity" not in (phase/"command.txt").read_text() if mode=="schedule" else True
        else:
            assert (phase/"scheduler-refusal.txt").exists() and not (phase/"receipt.txt").exists()
    return {"calls":len(fixtures.CASES),"installed_sites":sites,"phase_calls":len(phases),
            "automatic_source_description":True,"source_or_target_handwritten_metadata":False,
            "complete_outputs_checked":True,"runtime_paths_claimed_from_assembly":False,
            "reused_successful_compilation":reused}


def branch_probe(name, configuration):
    column,marked,_mode,kind,_sizes=configuration
    directory=WORK/name
    source=fixtures.printer_for_gcc((directory/"regions.light.c").read_text())
    for function in fixtures.NAMES:
        body=fixtures.function_body(source,function)
        additions=[(position+1,text) for yes,no in dispatch_sites(body)
                   for position,text in [(yes,"guard_fast++;"),(no,"guard_alias_refusal++;")]]
        additions += [(match.start(),"guard_original++;") for match in re.finditer(
            r"for\s*\(\s*;\s*1;\s*\$i\s*=\s*\$i\s*\+\s*1U?\)",body)]
        changed=body
        for position,text in sorted(additions,reverse=True):
            changed=changed[:position]+text+changed[position:]
        source=source.replace(body,changed,1)
    source="int guard_fast,guard_alias_refusal,guard_original;\n"+source
    source += "int main(void){"+"".join("guard_fast=guard_alias_refusal=guard_original=0;multi_case("+
        ",".join(map(str,case))+');printf("PATH %d %d %d\\n",guard_fast,guard_alias_refusal,guard_original);'
        for case in fixtures.CASES)+"return 0;}\n"
    (directory/"branches.c").write_text(source)
    subprocess.run(["gcc","-O0","-fwrapv","-Wno-builtin-declaration-mismatch","-Wno-discarded-qualifiers",
                    str(directory/"branches.c"),"-o",str(directory/"branches")],capture_output=True,check=True)
    output=subprocess.check_output([str(directory/"branches")],text=True,timeout=90)
    (directory/"branch-output.txt").write_text(output)
    actual=[list(map(int,line.split()[1:])) for line in output.splitlines() if line.startswith("PATH ")]
    expected=[fixtures.expected_path(case,column,marked and kind=="normal") for case in fixtures.CASES]
    assert actual==expected,(name,"paths",[(case,a,b) for case,a,b in zip(fixtures.CASES,actual,expected) if a!=b])
    assert "\n".join(line for line in output.splitlines() if not line.startswith("PATH "))+"\n"==fixtures.expected_output(column)
    return {"calls":len(fixtures.CASES),"actual_paths":actual,"assembly_path_claim":False}


def validate():
    check_build()
    report=json.loads((WORK/"report.json").read_text())
    assert report["status"]=="passed" and report["proved_entrypoint"]==builder.ENTRY
    assert set(report["configurations"])==set(CONFIGURATIONS)
    for path,digest in report["bindings"].items():
        assert sha(ROOT/path)==digest,path
    for name,configuration in CONFIGURATIONS.items():
        assert (WORK/name/"regions.c").read_text()==fixtures.source_text(*configuration[:2])
        assert (WORK/name/"output.txt").read_text()==fixtures.expected_output(configuration[0])
        assert (WORK/name/"reference-output.txt").read_text()==fixtures.expected_output(configuration[0])
    return report


def main():
    global WORK
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work",type=Path,default=WORK)
    parser.add_argument("--validate",action="store_true")
    parser.add_argument("--reuse-compiled",type=Path)
    args=parser.parse_args();WORK=args.work.resolve()
    if args.reuse_compiled is not None:
        args.reuse_compiled=args.reuse_compiled.resolve()
    if args.validate or (WORK/"report.json").exists():
        report=validate();print(json.dumps({"status":"validated","report_sha256":sha(WORK/"report.json")}));return
    assert not WORK.exists(),"Use a fresh native checkpoint"
    bindings=check_build();pluto=scheduler.validate();bindings[scheduler.REPORT]=sha(scheduler.REPORT)
    WORK.mkdir(parents=True)
    configurations={};paths={}
    try:
        for name,configuration in CONFIGURATIONS.items():
            configurations[name]=compile_run(name,configuration,ROOT/pluto["binary"],args.reuse_compiled)
            paths[name]=branch_probe(name,configuration)
            print(json.dumps({"configuration":name,"status":"passed","calls":len(fixtures.CASES)}),flush=True)
    except Exception as error:
        (WORK/"failure.json").write_text(json.dumps({"status":"failed","error":repr(error),"completed":list(configurations)},indent=2)+"\n")
        raise
    bindings |= {ROOT/path:sha(ROOT/path) for path in HELPERS}
    bindings |= {path:sha(path) for path in WORK.rglob("*") if path.is_file()}
    report={"status":"passed","proved_entrypoint":builder.ENTRY,"compiler_sha256":sha(COMPILER),
            "configurations":configurations,"clight_paths":paths,
            "assembly_calls":sum(case["calls"] for case in configurations.values()),
            "independent_Clight_calls":sum(case["calls"] for case in paths.values()),
            "full_memory_and_public_exits_checked":True,"real_scheduler_and_prepared_codegen":True,
            "loaded_source_header_supported":False,"general_affine_domains_supported":False,
            "measured_cost_added":False,"full_goal_complete":False,
            "bindings":{str(path.relative_to(ROOT)):digest for path,digest in bindings.items()}}
    (WORK/"report.json").write_text(json.dumps(report,indent=2)+"\n")
    validate();print(json.dumps({"status":"passed","assembly_calls":report["assembly_calls"],
                              "Clight_calls":report["independent_Clight_calls"],"report_sha256":sha(WORK/"report.json")}),flush=True)


if __name__=="__main__":
    main()
