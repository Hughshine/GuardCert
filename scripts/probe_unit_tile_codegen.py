"""Inspect raw codegen coordinate elimination with the frozen tight compiler.

This probe records actual source/raw/adapted outputs, not native correctness
or accepted installation. Each input contains one selected fixture function.
"""
import json
import os
from pathlib import Path
import subprocess

from audit_interface_clight import ROOT, sha
import native_zero_loaded_word_fixtures as fixtures
import build_pipeline_pluto as scheduler

WORK = ROOT/"build/unit-tile-codegen-probe"
COMPILER = ROOT/"build/loaded-word-tight/compiler/ccomp"
SIZES = {"unit-row":[1,3,2], "unit-column":[2,1,2],
         "unit-component":[2,3,1], "all-unit":[1,1,1]}


def source_text():
    return fixtures.source_text(True).split("void selected_mixed",1)[0]+"int main(void){return 0;}\n"


def inspect(name, sizes, binary):
    directory=WORK/name
    directory.mkdir()
    source=directory/"region.c"
    source.write_text(source_text())
    env={k:v for k,v in os.environ.items() if not k.startswith("GUARDCERT_")}
    env.update(GUARDCERT_TENSOR_MODE="pipeline",GUARDCERT_POLYHEDRAL_MODE="tile",
               GUARDCERT_PLUTO=str(binary),GUARDCERT_TILE_SIZES=",".join(map(str,sizes)),
               GUARDCERT_PIPELINE_DUMP=str(directory/"phases"))
    with (directory/"compile.log").open("x") as log:
        subprocess.run([str(COMPILER),"-conf",str(COMPILER.parent/"compcert.ini"),
            "-stdlib",str(COMPILER.parent/"runtime"),"-dclight","-S","-o",
            str(directory/"program.s"),str(source)],cwd=directory,env=env,
            stdout=log,stderr=subprocess.STDOUT,check=True,timeout=600)
    [phase]=list((directory/"phases").glob("guardcert-phase-*"))
    raw=(phase/"raw-generated.loop").read_text()
    generated=(phase/"generated.loop").read_text()
    sites=len(list(fixtures.dispatch_sites(fixtures.function_body((directory/"region.light.c").read_text(),"selected_one"))))
    return {"tile_sizes":sizes,"raw_depth":raw.count("loop ["),"adapted_depth":generated.count("loop ["),
            "installed_dispatches":sites,"phase":str(phase.relative_to(ROOT)),"native_execution_checked":False}


def main():
    if (WORK/"report.json").exists():
        report=json.loads((WORK/"report.json").read_text())
        for path,digest in report["bindings"].items():assert sha(ROOT/path)==digest,path
        print(json.dumps({"status":"validated-inspection","report_sha256":sha(WORK/"report.json")}))
        return
    assert not WORK.exists(),"Refusing to overwrite a codegen probe"
    stamp=json.loads((COMPILER.parent/".guard-build.json").read_text())
    assert sha(COMPILER)==stamp["compiler_sha256"]
    binary=ROOT/scheduler.validate()["binary"]
    WORK.mkdir(parents=True)
    facts={}
    for name,sizes in SIZES.items():
        facts[name]=inspect(name,sizes,binary)
        print(name,facts[name],flush=True)
    paths=[COMPILER,COMPILER.parent/".guard-build.json",scheduler.REPORT,ROOT/"scripts/probe_unit_tile_codegen.py"]
    paths += [ROOT/path for path in fixtures.HELPERS]
    paths += [p for p in WORK.rglob("*") if p.is_file()]
    report={"status":"inspected","configurations":facts,"native_correctness_claimed":False,
            "bindings":{str(p.relative_to(ROOT)):sha(p) for p in paths}}
    (WORK/"report.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"status":"inspected","report_sha256":sha(WORK/"report.json")}))


if __name__ == "__main__":
    main()
