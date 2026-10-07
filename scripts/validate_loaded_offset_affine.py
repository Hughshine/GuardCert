"""Validate proof/build, native matrix, and optional execution-path bindings."""
import argparse
import json
from pathlib import Path
import re

import native_loaded_offset_affine as suite
from audit_interface_clight import sha


def validate():
    suite.check_build()
    path = suite.WORK/"report.json"
    report = json.loads(path.read_text())
    assert report["status"] == "passed" and report["proved_entrypoint"] == suite.ENTRY
    assert report["compiler_sha256"] == sha(suite.COMPILER)
    assert report["stamp_sha256"] == sha(suite.COMPILER.parent/".guard-build.json")
    assert report["proof_report_sha256"] == sha(suite.PROOF)
    assert report["source_sha256"] == sha(suite.SOURCE)
    assert suite.SOURCE.read_text() == suite.source_text()
    assert report["verification_script_sha256"] == sha(Path(suite.__file__))
    assert report["cases"] == [list(row) for row in suite.cases()]
    for helper,digest in report["helper_sources"].items():
        assert sha(suite.ROOT/helper) == digest,helper
    expected = suite.expected_output()
    assert (suite.WORK/"reference-output.txt").read_text() == expected
    assert sha(suite.WORK/"reference-output.txt") == report["reference_sha256"]
    assert set(report["configurations"]) == {"disabled","interchange","tile-2-3","wrong-reindex","invalid-domain","resource-limit"}
    for name,facts in report["configurations"].items():
        directory = suite.WORK/name
        assert facts["calls"] == len(suite.cases())+1 == report["calls_per_configuration"]
        for artifact,digest in facts["artifacts"].items():
            assert sha(directory/artifact) == digest,(name,artifact)
        assert (directory/"output.txt").read_text() == expected,name
        dump = (directory/(suite.SOURCE.stem+".light.c")).read_text()
        for function,depth in zip(suite.NAMES+["loaded_small2"],suite.DEPTHS+[2]):
            body = suite.function_body(dump,function)
            observation = facts["functions"][function]
            assert observation["guarded"] == (body.count("for (")>depth)
            assert observation["loops"] == body.count("for (")
            assert observation["clight_bytes"] == len(body.encode())
            assert observation["machine_bytes"] == suite.machine_bytes(directory/"program",function)
        installed = {function for function,f in facts["functions"].items() if f["guarded"]}
        if name in ["interchange","tile-2-3"]:
            assert {"loaded_accum3","loaded_multi3","loaded_twice2","loaded_small2"} <= installed
        else:
            assert not installed,(name,installed)
    assert not report["configurations"]["interchange"]["functions"]["loaded_chain2"]["guarded"]
    assert report["total_new_calls"] == sum(f["calls"] for f in report["configurations"].values()) == 708
    witness = tuple(report["true_dependence_counterexample"])
    assert suite.run_model(witness)[0] != suite.run_model(witness,interchange=True)[0]
    return report


def validate_paths(native):
    path = suite.WORK/"path-report.json"
    report = json.loads(path.read_text())
    assert report["status"] == "passed"
    assert report["native_report_sha256"] == sha(suite.WORK/"report.json")
    assert report["compiler_sha256"] == sha(suite.COMPILER)
    assert report["verification_script_sha256"] == sha(suite.ROOT/"scripts/probe_loaded_offset_affine.py")
    for helper,digest in report["helper_sources"].items():
        assert sha(suite.ROOT/helper) == digest,helper
    branches = report["clight_branch_probes"]
    assert set(branches) == {"interchange","tile-2-3"}
    for name,facts in branches.items():
        directory = suite.WORK/name
        for artifact,digest in facts["artifacts"].items():
            assert sha(directory/artifact) == digest,(name,artifact)
        output = (directory/"branch-output.txt").read_text().splitlines()
        observed = [list(map(int,line.split()[1:])) for line in output if line.startswith("PATH ")]
        assert observed == facts["expected_and_actual_branches"]
        assert len(observed) == facts["calls"] == len(suite.cases())+1
        assert facts["fast"] == sum(a[0] for a in observed)
        assert facts["fallback"] == sum(a[1] for a in observed)
        assert "\n".join(line for line in output if not line.startswith("PATH "))+"\n" == suite.expected_output()
        for function,sites in facts["dispatch_sites"].items():
            assert sites == ((2 if function == "loaded_twice2" else 1)
                if native["configurations"][name]["functions"][function]["guarded"] else 0)
    assert report["instrumented_clight_calls"] == sum(f["calls"] for f in branches.values()) == 236
    expected = {(name,probe) for name in ["disabled","interchange","tile-2-3"]
        for probe in ["three-axis","multi-array","repeated-regions"]}
    expected |= {(name,probe) for name in ["interchange","tile-2-3"]
        for probe in ["same-block-slices","body-alias-fallback","partial-body-alias-fallback",
                      "bound-first-write","bound-second-row","short-source"]}
    probes = report["unmodified_machine_probes"]
    assert {(p["configuration"],p["name"]) for p in probes} == expected
    assert len(probes) == report["machine_probe_count"] == 21
    for probe in probes:
        directory = suite.WORK/probe["configuration"]
        assert probe["binary_sha256"] == sha(directory/"program")
        assert probe["binary_sha256"] == native["configurations"][probe["configuration"]]["artifacts"]["program"]
        commands,log = directory/(probe["name"]+".gdb"),directory/(probe["name"]+".gdb.log")
        assert probe["commands_sha256"] == sha(commands)
        assert probe["log_sha256"] == sha(log)
        parsed = re.findall(r"^GUARDCERT_LOADED_AFFINE_PATH (.*)$",log.read_text(),re.MULTILINE)
        assert len(parsed) == 1 and json.loads(parsed[0]) == probe["observed"]
        if probe["name"] == "short-source":
            assert probe["observed"]["comparison_indices"] == [0,1]
            assert probe["observed"]["comparison_sites"] > 0
    assert report["store_order_observes_actual_reordering_and_tiling"]
    assert report["short_source_pointer_comparisons_stop_before_future_unlicensed_address"]
    assert not report["timing_or_profitability_measured"]
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--paths",action="store_true",help="also require the complete execution-path report")
    args = parser.parse_args()
    report = validate()
    result = {"status":"passed","configurations":len(report["configurations"]),
        "calls":report["total_new_calls"],"report_sha256":sha(suite.WORK/"report.json")}
    if args.paths:
        paths = validate_paths(report)
        result.update(machine_probes=paths["machine_probe_count"],clight_calls=paths["instrumented_clight_calls"],
                      path_report_sha256=sha(suite.WORK/"path-report.json"))
    print(json.dumps(result,indent=2))
