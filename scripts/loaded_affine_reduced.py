"""Reuse the complete-C matrix and path probes for certified guard reduction."""
import argparse
import json
from pathlib import Path
import sys

import native_loaded_affine_multi as suite
import validate_loaded_affine_multi as validator
import probe_loaded_affine_multi as probes
from audit_interface_clight import sha

SELF = Path(__file__).resolve()
BASELINE = suite.ROOT/"build/loaded-affine-multi/native/report.json"
STAGE = "numeric-first-path-facts-reused-before-alias"


def check_build():
    stamp = json.loads((suite.COMPILER.parent/".guard-build.json").read_text())
    proof = json.loads(suite.PROOF.read_text())
    assert stamp["proved_entrypoint"] == suite.ENTRY == proof["whole_program_entrypoint"]
    assert stamp["guard_stage"] == STAGE
    assert proof["status"] == "compiled" and proof["additional_global_axioms"] == []
    assert proof["already_accepted_numeric_and_first_path_checks_are_not_reexecuted"]
    checks = {suite.COMPILER:stamp["compiler_sha256"],suite.COMPILER.parent/"driver/Driver.ml":stamp["driver_sha256"],
        suite.COMPILER.parent/"extract_loaded_affine_multi.v":stamp["extraction_sha256"],
        suite.PROOF:stamp["proof_report_sha256"],suite.ROOT/"scripts/build_loaded_affine_multi.py":stamp["build_script_sha256"],
        suite.ROOT/"scripts/audit_loaded_affine_reduced.py":proof["verification_script_sha256"]}
    checks |= {suite.ROOT/p:digest for p,digest in (stamp["proof_sources"]|stamp["native_sources"]|stamp["build_helpers"]).items()}
    checks |= {(suite.ROOT/p).with_suffix(".vo"):digest for p,digest in proof["compiled_objects"].items()}
    for path,digest in checks.items():
        assert sha(path) == digest,path
    return stamp


def configure():
    suite.COMPILER = suite.ROOT/"build/loaded-affine-multi-reduced/compiler/ccomp"
    suite.PROOF = suite.ROOT/"build/loaded-affine-multi-reduced/proof/report.json"
    suite.WORK = suite.ROOT/"build/loaded-affine-multi-reduced/native"
    suite.check_build = check_build


def comparison(report):
    baseline = json.loads(BASELINE.read_text())
    assert baseline["status"] == "passed"
    assert report["cases"] == baseline["cases"] and report["source_sha256"] == baseline["source_sha256"]
    assert set(report["configurations"]) == set(baseline["configurations"])
    result = {}
    for name,facts in baseline["configurations"].items():
        # The old proof/object binding is historical. Compare only its saved
        # native artifacts, whose exact contents must still be available.
        old = BASELINE.parent/name
        for artifact,digest in facts["artifacts"].items():
            assert sha(old/artifact) == digest,(name,artifact)
        assert (old/"output.txt").read_bytes() == (suite.WORK/name/"output.txt").read_bytes()
        functions = {}
        for function,before in facts["functions"].items():
            after = report["configurations"][name]["functions"][function]
            assert before["guarded"] == after["guarded"],(name,function)
            functions[function] = {"guarded":after["guarded"],
                "before":{k:before[k] for k in ["loops","clight_ifs","clight_bytes","machine_bytes"]},
                "after":{k:after[k] for k in ["loops","clight_ifs","clight_bytes","machine_bytes"]}}
            if after["guarded"]:
                assert after["clight_ifs"] < before["clight_ifs"],(name,function)
                assert after["clight_bytes"] < before["clight_bytes"],(name,function)
        result[name] = functions
    return result


def annotate(path,**fields):
    report = json.loads(path.read_text())
    report.update(guard_stage=STAGE,harness_sha256=sha(SELF),**fields)
    path.write_text(json.dumps(report,indent=2)+"\n")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action",choices=["run","paths","validate"])
    args = parser.parse_args()
    configure()
    if args.action == "run":
        sys.argv = [str(SELF)]
        suite.main()
        path = suite.WORK/"report.json"
        report = json.loads(path.read_text())
        annotate(path,previous_native_report_sha256=sha(BASELINE),comparison=comparison(report))
    elif args.action == "paths":
        probes.main()
        path = suite.WORK/"path-report.json"
        report = json.loads(path.read_text())
        report["helper_sources"][str(SELF.relative_to(suite.ROOT))] = sha(SELF)
        path.write_text(json.dumps(report,indent=2)+"\n")
        annotate(path)
    else:
        report = validator.validate()
        assert report["guard_stage"] == STAGE and report["harness_sha256"] == sha(SELF)
        assert report["previous_native_report_sha256"] == sha(BASELINE)
        assert report["comparison"] == comparison(report)
        paths = validator.validate_paths(report)
        assert paths["guard_stage"] == STAGE and paths["harness_sha256"] == sha(SELF)
        print(json.dumps({"status":"passed","calls":report["total_new_calls"],
            "clight_calls":paths["instrumented_clight_calls"],"machine_probes":paths["machine_probe_count"],
            "report_sha256":sha(suite.WORK/"report.json"),"path_report_sha256":sha(suite.WORK/"path-report.json")},indent=2))


if __name__ == "__main__":
    main()
