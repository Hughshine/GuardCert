"""Exercise static signed-encoding refusal and the retained nonnegative builder."""
import json
from pathlib import Path

import native_affine_empty_signed as native
from audit_interface_clight import ROOT,sha
from native_zero_trip import function_body

WORK=ROOT/"build/affine-empty-signed/profile-refusal-v1"


def main():
    bindings=native.check_build()
    if(WORK/"report.json").exists():
        report=json.loads((WORK/"report.json").read_text())
        assert report["status"]=="passed" and report["proved_entrypoint"]==native.builder.ENTRY
        for path,digest in report["bindings"].items():
            assert sha(ROOT/path)==digest,path
        print(json.dumps({"status":"validated","report_sha256":sha(WORK/"report.json")}));return
    assert not WORK.exists();WORK.mkdir()
    native.fixtures.configure("subtract")
    pluto=ROOT/native.scheduler.validate()["binary"]
    configuration=(True,"tile","pipeline",{"GUARDCERT_PLUTO":"/usr/bin/false",
        "GUARDCERT_AFFINE_GEOMETRY_CAP":"2147483647"})
    try:
        result=native.compile_run("scheduler-failure",configuration,pluto,WORK)
        dump=(WORK/"scheduler-failure/regions.light.c").read_text()
        for name in("empty_triangle","empty_double","undefined_body_word"):
            body=function_body(dump,name)
            assert "2147483646"in body,(name,"retained old exclusive header cap")
            assert "-2147483647"not in body,(name,"signed lower gate was not installed")
        baseline=native.validate()["configurations"]["subtract-scheduler-failure"]
        assert result["paths"]==baseline["paths"],"static refusal lost old acceptance"
    except Exception as error:
        (WORK/"native-script.py").write_bytes(Path(__file__).read_bytes())
        (WORK/"failure.json").write_text(json.dumps({"status":"failed","reason":repr(error)},indent=2)+"\n");raise
    bindings|={ROOT/"scripts/native_affine_empty_signed_profile.py":sha(Path(__file__)),
        ROOT/"scripts/native_affine_empty_signed.py":sha(ROOT/"scripts/native_affine_empty_signed.py"),
        native.WORK/"report.json":sha(native.WORK/"report.json"),
        native.scheduler.REPORT:sha(native.scheduler.REPORT),pluto:sha(pluto)}
    bindings|={path:sha(path)for path in WORK.rglob("*")if path.is_file()}
    report={"status":"passed","proved_entrypoint":native.builder.ENTRY,"result":result,
        "signed_profile_compilation_refusal_exercised":True,"old_profile_target_installed":True,
        "original_fallback_occurrences_per_tested_function":1,
        "paths_equal_normal_subtract_matrix":True,"geometry_cap":2147483647,
        "scheduler_unavailable":True,"profitability_measured":False,
        "bindings":{str(path.relative_to(ROOT)):digest for path,digest in bindings.items()}}
    (WORK/"report.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"status":"passed","assembly_calls":result["assembly_calls"],
        "Clight_calls":result["Clight_calls"],"report_sha256":sha(WORK/"report.json")}),flush=True)


if __name__=="__main__":
    main()
