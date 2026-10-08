"""Audit the installed-source zero-RMW preparation and whole-program compiler proof.

Only successor modules are compiled. All historical proof objects remain inputs.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess

import audit_affine_nest_materialized as deep
import audit_tensor_loaded_word_factory as parent
import native_loaded_word_pipeline_v3 as native
import audit_zero_rmw as zero
import audit_loaded_word_padded_frontend as padded
from audit_compiler import names
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/loaded-word-zero/proof-v2"
MODULES = ['prototype/interface/ClightTensorPreparedGenerated.v', 'prototype/interface/ClightTensorZeroRmwPreparation.v', 'prototype/interface/ClightTensorZeroRmwScanBridge.v', 'prototype/interface/ClightTensorZeroRmwDriver.v', 'prototype/interface/ClightTensorZeroRmwFactory.v', 'prototype/interface/ClightZeroLoadedWordFrontendFactory.v', 'prototype/interface/ClightSelectedZeroLoadedWordFrontendCompiler.v']
KIND = "source-licensed-zero-rmw-loaded-word-compiler"
ENTRY = "ClightSelectedZeroLoadedWordFrontendCompiler.compile_selected_zero_loaded_word_frontend_regions"
ENDPOINT = ENTRY+"_correct"


def frozen_inputs():
    parent.validate()
    native.validate()
    zero.validate()
    padded.validate()
    return {str(p.relative_to(ROOT)):sha(p) for p in [parent.WORK/"report.json",native.WORK/"report.json",zero.WORK/"report.json",padded.WORK/"report.json",
            native.COMPILER,native.COMPILER.parent/".guard-build.json"]}


def closure():
    flags = deep.flags()
    result = subprocess.run(["rocq","dep",*flags,*MODULES],cwd=ROOT,capture_output=True,text=True,check=True)
    (WORK/"dependencies.txt").write_text(result.stdout)
    (WORK/"dependency-warnings.txt").write_text(result.stderr)
    graph = {}
    # The historical dependency graph describes old sources without rereading
    # unrelated untracked drafts during dependency discovery.
    for text in [(parent.WORK/"dependencies.txt").read_text(),(zero.WORK/"dependencies.txt").read_text(),
                 (padded.WORK/"dependencies.txt").read_text(),result.stdout]:
        for line in text.splitlines():
            if ": " not in line:
                continue
            outputs,dependencies = line.split(": ",1)
            node = outputs.split()[0]
            if node.endswith(".vo"):
                graph[(ROOT/node).resolve()] = [(ROOT/p).resolve() for p in dependencies.split() if p.endswith(".vo")]
    order,seen = [],set()
    def visit(node):
        if node in seen or node not in graph:
            return
        seen.add(node)
        for dependency in graph[node]:
            visit(dependency)
        order.append(node.with_suffix(".v"))
    for file in MODULES:
        visit((ROOT/file).with_suffix(".vo"))
    sources = [str(p.relative_to(ROOT)) for p in order]
    assert not set(sources) & parent.PROTECTED_DRAFTS
    frozen_objects = {p:sha((ROOT/p).with_suffix(".vo")) for p in sources if p not in MODULES}
    for file in sources:
        if file not in MODULES:
            continue
        with (WORK/(Path(file).stem+".log")).open("w") as log:
            subprocess.run(["rocq","compile",*flags,file],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
        print("Compiled",file,flush=True)
    assert frozen_objects == {p:sha((ROOT/p).with_suffix(".vo")) for p in frozen_objects}
    (WORK/"required-closure.json").write_text(json.dumps(sources,indent=2)+"\n")
    return sources


def validate():
    report = json.loads((WORK/"report.json").read_text())
    assert report["status"] == "compiled" and report["kind"] == KIND
    assert report["frozen_inputs"] == frozen_inputs()
    assert report["condition_encoding_endpoint"] == zero.ENDPOINT
    assert report["minimal_semantic_kernel_changed"] is False and report["new_compiler_proved"] is True
    assert report["new_whole_program_entrypoint"] == ENDPOINT
    assert report["new_assembly_evidence"] is False and report["new_guard_profitability_measured"] is False
    assert not report["additional_global_axioms"] and not report["kernel_assumptions"]
    assert report["toolchain"] == subprocess.check_output(["rocq","--version"],text=True).strip()
    assert report["compiler_assumptions"] == json.loads((parent.WORK/"report.json").read_text())["generated_compiler_baseline_assumptions"]
    for field,base in [("sources",ROOT),("helpers",ROOT),("artifacts",WORK)]:
        for file,digest in report[field].items():
            assert sha(base/file) == digest,(field,file)
    for file,digest in report["compiled_objects"].items():
        assert sha((ROOT/file).with_suffix(".vo")) == digest,file
    expected = [Path(file).stem+"."+name for file in MODULES for name in
                re.findall(r"^Print Assumptions (\w+)\.",(ROOT/file).read_text(),re.MULTILINE)]
    assert report["queried_endpoints"] == expected
    assert set(report["endpoint_assumptions"]) == set(expected)
    for values in report["endpoint_assumptions"].values():
        assert set(values) <= set(report["compiler_assumptions"])
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate",action="store_true")
    args = parser.parse_args()
    if args.validate or (WORK/"report.json").exists():
        validate();print(json.dumps({"status":"validated","report_sha256":sha(WORK/"report.json")}));return
    frozen = frozen_inputs()
    WORK.mkdir(parents=True)
    sources = closure()
    endpoints = []
    for file in MODULES:
        code = (ROOT/file).read_text()
        assert not re.search(r"\b(Admitted|Abort|Axiom|Parameter)\b",code),file
        assert not re.search(r"^\s*Show\.",code,re.MULTILINE),file
        endpoints += [Path(file).stem+"."+name for name in re.findall(r"^Print Assumptions (\w+)\.",code,re.MULTILINE)]
    queries = {"COMPCERT":"Compiler.transf_c_program_correct","KERNEL":"GuardInterface.guardify_preservation",
               "COMPILER":native.ENTRY+"_correct","NEW_COMPILER":ENDPOINT,**{f"ENDPOINT_{i}":e for i,e in enumerate(endpoints)}}
    lines = ["From compcert.driver Require Import Compiler.","From GuardInterface Require Import GuardInterface "
             +native.ENTRY.split(".")[0]+" "+" ".join(Path(p).stem for p in MODULES)+"."]
    for short,qualified in deep.PRINTER_ALIASES.items():
        lines += [f"Goal {short}={qualified}. reflexivity. Qed."]
    for marker,endpoint in queries.items():
        lines += [f'Goal True. idtac "{marker}". exact I. Qed.',f"Print Assumptions {endpoint}."]
    lines += ['Goal True. idtac "END". exact I. Qed.']
    (WORK/"Audit.v").write_text("\n".join(lines)+"\n")
    run = subprocess.run(["rocq","compile",*deep.flags(),str(WORK/"Audit.v")],cwd=ROOT,capture_output=True,text=True)
    (WORK/"assumptions.log").write_text(run.stdout+run.stderr)
    assert run.returncode == 0,run.stdout[-3000:]+run.stderr
    markers = [*queries,"END"]
    sections = {marker:sorted({deep.PRINTER_ALIASES.get(n,n) for n in
                names(run.stdout.split(marker+"\n",1)[1].split(markers[i+1]+"\n",1)[0])})
                for i,marker in enumerate(markers[:-1])}
    actual = {e:sections[f"ENDPOINT_{i}"] for i,e in enumerate(endpoints)}
    assert not sections["KERNEL"]
    assert sections["NEW_COMPILER"] == sections["COMPILER"]
    assert all(set(v) <= set(sections["COMPILER"]) for v in actual.values())
    source_hashes = {p:sha(ROOT/p) for p in sources}
    source_hashes |= {str(p.relative_to(ROOT)):sha(p) for p in (ROOT/"vendor/CompCert").rglob("*.v")}
    objects = {p:sha((ROOT/p).with_suffix(".vo")) for p in sources}
    objects |= {str(p.relative_to(ROOT)):sha(p.with_suffix(".vo")) for p in (ROOT/"vendor/CompCert").rglob("*.v") if p.with_suffix(".vo").exists()}
    assert frozen_inputs() == frozen
    report = {"status":"compiled","kind":KIND,"frozen_inputs":frozen,"required_closure":sources,
        "queried_endpoints":endpoints,"endpoint_assumptions":actual,"compcert_assumptions":sections["COMPCERT"],
        "compiler_assumptions":sections["COMPILER"],"new_compiler_assumptions":sections["NEW_COMPILER"],"kernel_assumptions":sections["KERNEL"],"additional_global_axioms":[],
        "condition_encoding_endpoint":zero.ENDPOINT,"new_whole_program_entrypoint":ENDPOINT,"sources":source_hashes,"compiled_objects":objects,
        "helpers":{"scripts/audit_zero_loaded_word.py":sha(ROOT/"scripts/audit_zero_loaded_word.py")},
        "toolchain":subprocess.check_output(["rocq","--version"],text=True).strip(),
        "artifacts":{p:sha(WORK/p) for p in ["Audit.v","Audit.vo","assumptions.log","dependencies.txt","dependency-warnings.txt","required-closure.json"]},
        "source_scope":"actual signed32 loaded root/child loops and literal positive component loop; zero-RMW shortcut plus historical nonzero scan; checked source, private allocation, canonical model and actual generated candidate",
        "effect_scope":"zero-RMW Mint32 observation preservation licenses exact original/cached execution; generated target returns identical final memory and live temporary observations",
        "minimal_semantic_kernel_changed":False,"new_compiler_proved":True,"new_compiler_installed":False,"new_assembly_evidence":False,
        "new_guard_profitability_measured":False,
        "remaining_obligations":["extract and execute the new compiler on the same C matrix and stable-header aliases",
                                 "measure the successor guard and complete candidate costs",
                                 "compact nonzero RMW conditions and candidate lowering improvements"]}
    (WORK/"report.json").write_text(json.dumps(report,indent=2)+"\n")
    validate()
    print(json.dumps({"status":"compiled","endpoints":len(endpoints),"closure":len(sources),
                      "closed_endpoints":sum(not v for v in actual.values()),"maximum_endpoint_globals":max(map(len,actual.values())),
                      "report_sha256":sha(WORK/"report.json")}),flush=True)


if __name__ == "__main__":
    main()
