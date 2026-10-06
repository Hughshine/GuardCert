"""Recheck the cursor compiler after shared proof objects have been rebuilt."""
import json
import subprocess
from pathlib import Path
import audit_affine_nest_materialized as deep
from audit_compiler import names
from audit_interface_clight import ROOT,sha

WORK=ROOT/"build/affine-nest-materialized/cursor-regression"
OLD=ROOT/"build/affine-cursor-dependent-compiler/proof/report.json"
CURRENT=ROOT/"build/affine-nest-materialized/proof/report.json"
ENDPOINT="ClightGuardedAffineCursorDependentCompiler.compile_guarded_affine_cursor_dependent_correct"


def main():
    WORK.mkdir(parents=True,exist_ok=True)
    deep.WORK=WORK
    closure=deep.compile_closure(deep.flags(),entries=[ROOT/"prototype/interface/ClightGuardedAffineCursorDependentCompiler.v"])
    old=json.loads(OLD.read_text());current=json.loads(CURRENT.read_text())
    for source,digest in old["sources"].items():
        assert sha(ROOT/source)==digest,source
    # Compilation of sibling consumers must not invalidate the new proof.
    for source,digest in current["compiled_objects"].items():
        assert sha((ROOT/source).with_suffix(".vo"))==digest,source
    path=WORK/"Audit.v"
    path.write_text("From compcert.driver Require Import Compiler.\nFrom GuardInterface Require Import ClightGuardedAffineCursorDependentCompiler.\nPrint Assumptions "+ENDPOINT+".\n")
    result=subprocess.run(["rocq","compile",*deep.flags(),str(path)],capture_output=True,text=True,cwd=ROOT)
    (WORK/"assumptions.log").write_text(result.stdout+result.stderr)
    assert result.returncode==0,result.stdout+result.stderr
    actual=names(result.stdout)
    assert actual==set(old["endpoint_assumptions"][ENDPOINT])
    changed=[source for source,digest in old["compiled_objects"].items()
        if sha((ROOT/source).with_suffix(".vo"))!=digest]
    report={"status":"compiled","endpoint":ENDPOINT,"endpoint_assumptions":sorted(actual),
        "inherited_frozen_report_sha256":sha(OLD),"materialized_proof_report_sha256":sha(CURRENT),
        "required_closure":closure,"sources":{s:sha(ROOT/s) for s in closure},
        "compiled_objects":{s:sha((ROOT/s).with_suffix(".vo")) for s in closure},
        "changed_frozen_object_digests":changed,"frozen_report_rewritten":False,
        "new_materialized_objects_unchanged":True,"native_rerun":False,
        "verification_script_sha256":sha(ROOT/"scripts/audit_cursor_after_shared_rebuild.py")}
    path=WORK/"report.json";path.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"status":"passed","assumptions":len(actual),"dependencies":len(closure),
        "changed_frozen_object_digests":len(changed),"report_sha256":sha(path),"native_rerun":False},indent=2))


if __name__=="__main__":
    main()
