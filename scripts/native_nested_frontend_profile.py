"""Validate a proposed tighter premise that makes the dependent chain admissible."""
import argparse
import json
import re

from audit_interface_clight import sha
import native_nested_frontend_coverage as coverage
import probe_nested_frontend_coverage as paths

WORK = coverage.WORK/"one-column-profile"
MODES = ["interchange","tile-2-3"]
HELPERS = ["scripts/native_nested_frontend_profile.py", *paths.HELPERS]
PROFILE = {"root_cap":4,"bound_lower":1,"bound_upper_exclusive":2}


def validate():
    coverage.validate()
    report = json.loads((WORK/"report.json").read_text())
    assert report["status"]=="passed" and report["proved_entrypoint"]==coverage.frontend.ENTRY
    assert report["base_coverage_sha256"]==sha(coverage.WORK/"report.json")
    assert report["compiler_sha256"]==sha(coverage.frontend.COMPILER)
    assert report["proposed_profile"]==PROFILE
    assert set(report["helper_sources"])==set(HELPERS)
    for p,digest in report["helper_sources"].items(): assert sha(coverage.ROOT/p)==digest,p
    assert set(report["configurations"])==set(MODES)
    assert set(report["clight_branch_probes"])==set(MODES)
    for mode,facts in report["configurations"].items():
        directory = WORK/mode
        assert facts["calls"]==119 and facts["range_policy"]==PROFILE
        for p,digest in facts["artifacts"].items(): assert sha(directory/p)==digest,(mode,p)
        assert (directory/"output.txt").read_text()==coverage.expected_output()
        dump = (directory/(coverage.SOURCE.stem+".light.c")).read_text()
        assert set(facts["functions"])==set(coverage.NAMES)
        assert (directory/"compile.log").read_text().count("indexed=true exact=true checked=true depth=3")==8
        for name,value in facts["functions"].items():
            body = coverage.function_body(dump,name)
            assert value["loops"]==body.count("for (") and value["installed"]
            assert value["loops"]>(6 if name=="nested_twice" else 3)
            assert value["machine_bytes"]==coverage.frontend.machine_bytes(directory/"program",name)
            assert "$row < *($shape + 0) + 1" in body and "$column < *($shape + 1) + 1" in body
        branch = report["clight_branch_probes"][mode]
        for p,digest in branch["artifacts"].items(): assert sha(directory/p)==digest,(mode,p)
        lines = (directory/"branch-output.txt").read_text().splitlines()
        actual = [list(map(int,line.split()[1:])) for line in lines if line.startswith("PATH ")]
        expected = [paths.expected_dispatch(mode,row,bound_high=2) for row in coverage.cases()]
        assert actual==expected and branch["calls"]==len(actual)==119
        assert branch["cases_and_expected_dispatch"]==[[list(row),value] for row,value in zip(coverage.cases(),expected)]
        assert "\n".join(line for line in lines if not line.startswith("PATH "))+"\n"==coverage.expected_output()
        assert branch["fast"]==sum(a[0] for a in actual) and branch["runtime_refusal"]==sum(a[1] for a in actual)
        chain_rows = [(row,a) for row,a in zip(coverage.cases(),actual) if row[0]==2]
        assert any(row==(2,0,0,2,0,1,1) and a==[1,0] for row,a in chain_rows)
        assert any(row==(2,0,0,2,3,1,1) and a==[0,1] for row,a in chain_rows)
    assert report["new_assembly_calls"]==238 and report["instrumented_clight_calls"]==238
    assert not report["generic_assumption_inference"] and not report["timing_or_profitability_measured"]
    return report


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate",action="store_true")
    args=parser.parse_args()
    if args.validate:
        validate()
        print(json.dumps({"status":"validated","report_sha256":sha(WORK/"report.json")},indent=2))
        return
    coverage.validate()
    WORK.mkdir(parents=True,exist_ok=True)
    configurations={mode:coverage.compile_run(mode,directory=WORK/mode,bound_high=2) for mode in MODES}
    clight={mode:paths.clight_probe(mode,directory=WORK/mode,bound_high=2) for mode in MODES}
    report={"status":"passed","proved_entrypoint":coverage.frontend.ENTRY,
            "base_coverage_sha256":sha(coverage.WORK/"report.json"),
            "compiler_sha256":sha(coverage.frontend.COMPILER),"proposed_profile":PROFILE,
            "helper_sources":{p:sha(coverage.ROOT/p) for p in HELPERS},
            "configurations":configurations,"clight_branch_probes":clight,
            "new_assembly_calls":238,"instrumented_clight_calls":238,
            "dependent_chain_installed_with_runtime_premise":True,
            "generic_assumption_inference":False,"timing_or_profitability_measured":False}
    (WORK/"report.json").write_text(json.dumps(report,indent=2)+"\n")
    validate()
    print(json.dumps({"status":"passed","new_assembly_calls":238,"report_sha256":sha(WORK/"report.json")},indent=2))


if __name__ == "__main__":
    main()
