"""Audit positive-offset condition services without rebuilding frozen proof inputs."""
import argparse
import json
from pathlib import Path
import re
import subprocess

import audit_affine_nest_materialized as language
import audit_zero_loaded_word as baseline
from audit_compiler import names
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/positive-offset-headers/proof"
MODULES = ["prototype/interface/CompCertPositiveOffsetFacts.v",
           "prototype/interface/ClightPositiveOffsetHeaders.v"]


def inputs():
    report = baseline.validate()
    return {"baseline_report": sha(baseline.WORK/"report.json"),
            "baseline_objects": report["compiled_objects"]}


def endpoints():
    return [Path(path).stem+"."+name for path in MODULES for name in
            re.findall(r"^Print Assumptions (\w+)\.", (ROOT/path).read_text(), re.MULTILINE)]


def validate():
    report = json.loads((WORK/"report.json").read_text())
    assert report["status"] == "compiled" and report["frozen_inputs"] == inputs()
    assert report["queried_endpoints"] == endpoints()
    assert set(report["endpoint_assumptions"]) == set(endpoints())
    allowed=set(baseline.validate()["compiler_assumptions"])
    assert all(set(values)<=allowed for values in report["endpoint_assumptions"].values())
    assert sum(not values for values in report["endpoint_assumptions"].values()) == 5
    assert max(map(len,report["endpoint_assumptions"].values())) == 4
    assert not report["additional_global_axioms"] and not report["kernel_changed"]
    assert not report["new_compiler_theorem"] and not report["new_guard_installed"]
    assert report["toolchain"] == subprocess.check_output(["rocq","--version"],text=True).strip()
    for path,digest in report["bindings"].items():
        assert sha(ROOT/path) == digest,path
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    if args.validate or (WORK/"report.json").exists():
        report=validate()
        print(json.dumps({"status":"validated","report_sha256":sha(WORK/"report.json")}))
        return
    frozen=inputs()
    WORK.mkdir(parents=True)
    compile_flags=language.flags()
    dep=subprocess.run(["rocq","dep",*compile_flags,*MODULES],cwd=ROOT,capture_output=True,text=True,check=True)
    (WORK/"dependencies.txt").write_text(dep.stdout)
    (WORK/"dependency-warnings.txt").write_text(dep.stderr)
    for path in MODULES:
        source=ROOT/path; obj=source.with_suffix(".vo")
        assert not re.search(r"\b(Admitted|Abort|Axiom|Parameter)\b",source.read_text()),path
        if obj.exists():
            # A module already built during this stage is frozen too.
            assert obj.stat().st_mtime >= source.stat().st_mtime,path
        else:
            with (WORK/(source.stem+".log")).open("w") as log:
                subprocess.run(["rocq","compile",*compile_flags,path],cwd=ROOT,
                               stdout=log,stderr=subprocess.STDOUT,check=True)
    queried=endpoints()
    lines=["From GuardInterface Require Import CompCertPositiveOffsetFacts ClightPositiveOffsetHeaders."]
    for i,endpoint in enumerate(queried):
        lines += [f'Goal True. idtac "OFFSET_ENDPOINT_{i}". exact I. Qed.', f"Print Assumptions {endpoint}."]
    lines += ['Goal True. idtac "OFFSET_END". exact I. Qed.']
    (WORK/"Audit.v").write_text("\n".join(lines)+"\n")
    audit=subprocess.run(["rocq","compile",*compile_flags,str(WORK/"Audit.v")],cwd=ROOT,capture_output=True,text=True)
    (WORK/"assumptions.log").write_text(audit.stdout+audit.stderr)
    assert audit.returncode == 0,audit.stderr
    markers=[f"OFFSET_ENDPOINT_{i}" for i in range(len(queried))]+["OFFSET_END"]
    actual={endpoint:sorted(names(audit.stdout.split(markers[i]+"\n",1)[1].split(markers[i+1]+"\n",1)[0]))
            for i,endpoint in enumerate(queried)}
    allowed=set(baseline.validate()["compiler_assumptions"])
    assert all(set(values)<=allowed for values in actual.values()),actual
    assert sum(not values for values in actual.values()) == 5
    assert max(map(len,actual.values())) == 4
    assert frozen == inputs(),"A historical proof input changed"
    bindings={ROOT/path:sha(ROOT/path) for path in MODULES}
    bindings |= {(ROOT/path).with_suffix(".vo"):sha((ROOT/path).with_suffix(".vo")) for path in MODULES}
    bindings |= {ROOT/"scripts/audit_positive_offset_headers.py":sha(ROOT/"scripts/audit_positive_offset_headers.py")}
    bindings |= {path:sha(path) for path in WORK.rglob("*") if path.is_file()}
    report={"status":"compiled","frozen_inputs":frozen,"queried_endpoints":queried,
            "endpoint_assumptions":actual,"additional_global_axioms":[],"kernel_changed":False,
            "new_compiler_theorem":False,"new_guard_installed":False,
            "scope":"nonnegative literal offsets; actual cached word profile and existing loaded/indexed receipts imply signed mathematical bounds and absence of signed-add overflow",
            "condition_expression_evaluation_proved":False,
            "existing_capture_receipt_consumed":True,"source_read_licensing_changed":False,
            "toolchain":subprocess.check_output(["rocq","--version"],text=True).strip(),
            "bindings":{str(path.relative_to(ROOT)):digest for path,digest in bindings.items()}}
    (WORK/"report.json").write_text(json.dumps(report,indent=2)+"\n")
    validate()
    print(json.dumps({"status":"compiled","closed_endpoints":sum(not values for values in actual.values()),
                      "endpoints":len(queried),"maximum_endpoint_globals":max(map(len,actual.values())),"new_modules":len(MODULES),
                      "report_sha256":sha(WORK/"report.json")}),flush=True)


if __name__ == "__main__":
    main()
