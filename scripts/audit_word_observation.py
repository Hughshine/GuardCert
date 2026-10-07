"""Audit value-preserving typed stores and their actual Clight syntax checker."""
import argparse
import json
import re
import subprocess

from audit_compiler import names
from audit_interface_clight import ROOT, compcert_flags, sha

WORK = ROOT / "build/word-observation"
MODULE = ROOT / "prototype/interface/CompCertWordObservation.v"
HELPERS = ["scripts/audit_word_observation.py", "scripts/audit_interface_clight.py", "scripts/audit_compiler.py"]


def validate():
    report = json.loads((WORK / "report.json").read_text())
    assert report["status"] == "compiled" and report["additional_global_axioms"] == []
    for p,digest in report["sources"].items(): assert sha(ROOT/p)==digest,p
    for p,digest in report["compiled_objects"].items(): assert sha((ROOT/p).with_suffix(".vo"))==digest,p
    for p,digest in report["helpers"].items(): assert sha(ROOT/p)==digest,p
    for p,digest in report["artifacts"].items(): assert sha(WORK/p)==digest,p
    assert report["toolchain"]==subprocess.check_output(["rocq","--version"],text=True).strip()
    baseline=set().union(*(set(a) for a in report["baseline_assumptions"].values()))
    assert len(report["endpoint_assumptions"])==7
    for name,actual in report["endpoint_assumptions"].items(): assert set(actual)<=baseline,name
    assert not report["runtime_shortcut_installed"] and not report["guard_cost_measured"]
    return report


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate",action="store_true")
    args=parser.parse_args()
    if args.validate:
        validate();print(json.dumps({"status":"validated","report_sha256":sha(WORK/"report.json")},indent=2));return
    WORK.mkdir(parents=True,exist_ok=True)
    code=MODULE.read_text()
    assert not re.search(r"\b(Admitted|Abort|Axiom|Parameter)\b",code)
    endpoints=["CompCertWordObservation."+name for name in re.findall(r"^Print Assumptions (\w+)\.",code,re.MULTILINE)]
    baseline={"STORE_SAME":"Mem.load_store_same","STORE_OTHER":"Mem.load_store_other",
              "CLIGHT":"ClightCondition.fragment_language"}
    queries={**baseline,**{f"CHECK_{i}":name for i,name in enumerate(endpoints)}}
    flags=compcert_flags()
    run=subprocess.run(["rocq","compile",*flags,str(MODULE)],cwd=ROOT,capture_output=True,text=True)
    (WORK/"module.log").write_text(run.stdout+run.stderr)
    assert run.returncode==0,run.stderr[-1800:]
    lines=["From compcert.common Require Import Memory.","From Guard Require Import ClightCondition.",
           "From GuardInterface Require Import CompCertWordObservation."]
    for marker,name in queries.items():lines += [f'Goal True. idtac "{marker}". exact I. Qed.',f"Print Assumptions {name}."]
    lines.append('Goal True. idtac "END". exact I. Qed.')
    audit=WORK/"Audit.v";audit.write_text("\n".join(lines)+"\n")
    run=subprocess.run(["rocq","compile",*flags,str(audit)],cwd=ROOT,capture_output=True,text=True)
    (WORK/"assumptions.log").write_text(run.stdout+run.stderr)
    assert run.returncode==0,run.stderr[-1800:]
    markers=[*queries,"END"]
    sections={m:sorted(names(run.stdout.split(m+"\n",1)[1].split(markers[i+1]+"\n",1)[0]))
              for i,m in enumerate(markers[:-1])}
    allowed=set().union(*(set(sections[m]) for m in baseline))
    actual={name:sections[f"CHECK_{i}"] for i,name in enumerate(endpoints)}
    for name,values in actual.items():assert set(values)<=allowed,(name,set(values)-allowed)
    upstream=ROOT/"vendor/CompCert"
    sources={str(p.relative_to(ROOT)):sha(p) for p in upstream.rglob("*.v")}
    sources |= {str(MODULE.relative_to(ROOT)):sha(MODULE),"theories/ClightCondition.v":sha(ROOT/"theories/ClightCondition.v")}
    objects={str(MODULE.relative_to(ROOT)):sha(MODULE.with_suffix(".vo")),
             "theories/ClightCondition.v":sha(ROOT/"theories/ClightCondition.vo")}
    objects |= {str(p.relative_to(ROOT)):sha(p.with_suffix(".vo")) for p in upstream.rglob("*.v") if p.with_suffix(".vo").exists()}
    report={"status":"compiled","sources":sources,"compiled_objects":objects,
            "baseline_assumptions":{m:sections[m] for m in baseline},"endpoint_assumptions":actual,
            "additional_global_axioms":[],"runtime_shortcut_installed":False,"guard_cost_measured":False,
            "completed_clight_body_memory_guarantee":True,"static_checker_produces_store_classification":True,
            "fixed_observation_address_only":True,"temp_frame_and_source_progress_are_separate":True,
            "toolchain":subprocess.check_output(["rocq","--version"],text=True).strip(),
            "helpers":{p:sha(ROOT/p) for p in HELPERS},
            "artifacts":{p:sha(WORK/p) for p in ["Audit.v","Audit.vo","module.log","assumptions.log"]}}
    (WORK/"report.json").write_text(json.dumps(report,indent=2)+"\n")
    validate();print(json.dumps({"status":"compiled","endpoints":len(endpoints),"baseline_globals":len(allowed),
                               "report_sha256":sha(WORK/"report.json")},indent=2))


if __name__=="__main__":main()
