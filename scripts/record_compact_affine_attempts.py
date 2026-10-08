"""Retain two harness failures separately from the passing rank-three tier."""
import json
from pathlib import Path

import selected_compact_affine_fixtures as fixtures
from audit_interface_clight import ROOT, sha

WORK=ROOT / "build/selected-affine-pipeline/compact-harness-attempts-v1"


def main():
    if (WORK/"report.json").exists():
        report=json.loads((WORK/"report.json").read_text())
        for path,digest in report["bindings"].items(): assert sha(ROOT/path)==digest,path
        print(json.dumps({"status":"validated","report_sha256":sha(WORK/"report.json")}))
        return
    WORK.mkdir(parents=True,exist_ok=False)
    rows=[]
    bindings={Path(__file__):sha(Path(__file__)),ROOT/"scripts/selected_compact_affine_fixtures.py":sha(ROOT/"scripts/selected_compact_affine_fixtures.py")}
    for name,log_name,reason in [
        ("compact-tile-smoke-v1","/tmp/guard-compact-smoke-v1.log","harness expected exactly six proposals; two additional nested fragments were tried"),
        ("compact-tile-smoke-v2","/tmp/guard-compact-smoke-v2.log","harness expected ascending acceptance at -2,m=2, where the first child is empty; preserve this refusal and add the separate useful accepting input")]:
        attempt=ROOT/"build/selected-affine-pipeline"/name
        log=WORK/(name+".log")
        log.write_bytes(Path(log_name).read_bytes())
        assert "AssertionError" in log.read_text()
        directory=attempt/"tile"
        output=(directory/"output.txt").read_text()
        assert output==(directory/"reference-output.txt").read_text()
        cases=[tuple(map(int,line.split()[:7])) for line in output.splitlines()]
        assert output=="".join(fixtures.output_model(case) for case in cases)
        branch=directory/"branch-output.txt"
        if branch.exists(): assert "\n".join(branch.read_text().splitlines()[::2])+"\n"==output
        rows.append({"directory":str(attempt.relative_to(ROOT)),"failure":"harness assertion",
            "reason":reason,"assembly_full_output_calls":len(cases),
            "assembly_reference_and_independent_model_matched":True,
            "Clight_full_outputs_matched":branch.exists()})
        bindings|={p:sha(p) for p in attempt.rglob("*") if p.is_file()}
        bindings[log]=sha(log)
    (WORK/"report.json").write_text(json.dumps({"status":"recorded","attempts":rows,
        "passing_tier":"build/selected-affine-pipeline/compact-affine-native-v1/report.json",
        "timing_or_profitability_measured":False,"full_goal_complete":False,
        "bindings":{str(p.relative_to(ROOT)):digest for p,digest in bindings.items()}},indent=2)+"\n")
    print(json.dumps({"status":"recorded","report_sha256":sha(WORK/"report.json")}))


if __name__=="__main__":
    main()
