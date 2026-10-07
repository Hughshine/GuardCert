"""Check the same-word compiler on array/context inputs and actual dispatch.

Reuse source generation and the independent signed-word source model from the
frontend coverage suite, with separate inputs, binaries, and reports.  Additional
inputs exercise constant stores through loaded-header aliases.  This does not
modify or refresh historical coverage reports.
"""
import argparse
import json
from pathlib import Path
import subprocess

from audit_interface_clight import ROOT, sha
import native_nested_frontend as frontend
import native_nested_frontend_coverage as coverage
import probe_nested_frontend_coverage as probe

WORK = ROOT / "build/nested-stability/native"
COMPILER = ROOT / "build/nested-stability/compiler/ccomp"
PROOF = ROOT / "build/nested-stability/proof/report.json"
ENTRY = "ClightGuardedNestedStabilityCompiler.compile_ncs_stability_regions"
EXTRA = [(3, view, 0, u, v, 1, 1) for view, u, v in
         [(0, 1, 1), (1, 1, 1), (2, 1, 1), (1, 1, 2), (2, 2, 1),
          (1, 2, 1), (2, 1, 2), (0, 2, 1)]]
CASES = coverage.cases() + EXTRA
SOURCE = WORK / "nested_stability.c"
LEGACY = ROOT / "build/nested-frontend/compiler/ccomp"
HELPERS = list(dict.fromkeys(["scripts/native_nested_stability.py", *probe.HELPERS]))
OLD_DISPATCH = probe.expected_dispatch


def expected_dispatch(mode, row, *, bound_high=5):
    if row[0] == 3 and row[1] in [1, 2] and row[2:5] == (0, 1, 1):
        return [1, 0] if coverage.installation_expected(mode, "nested_write") else [0, 0]
    return OLD_DISPATCH(mode, row, bound_high=bound_high)


def configure():
    frontend.COMPILER, frontend.PROOF, frontend.ENTRY = COMPILER, PROOF, ENTRY
    coverage.WORK, coverage.SOURCE = WORK, SOURCE
    coverage.cases = lambda: CASES
    probe.WORK, probe.expected_dispatch = WORK, expected_dispatch


def bindings():
    return {"status": "passed", "proved_entrypoint": ENTRY,
            "compiler_sha256": sha(COMPILER), "proof_report_sha256": sha(PROOF),
            "stamp_sha256": sha(COMPILER.parent / ".guard-build.json"),
            "source_sha256": sha(SOURCE), "cases": [list(row) for row in CASES],
            "helpers": {p: sha(ROOT / p) for p in HELPERS}}


def validate_native(report):
    frontend.check_build()
    assert {k: report[k] for k in bindings()} == bindings()
    assert SOURCE.read_text() == coverage.source_text()
    expected = coverage.expected_output()
    assert (WORK / "reference-output.txt").read_text() == expected
    assert sha(WORK / "reference-output.txt") == report["reference_sha256"]
    assert set(report["configurations"]) == set(coverage.MODES)
    for mode, facts in report["configurations"].items():
        directory = WORK / mode
        for name, digest in facts["artifacts"].items():
            assert sha(directory / name) == digest, (mode, name)
        assert (directory / "output.txt").read_text() == expected
        assert facts["calls"] == len(CASES)
        dump = (directory / (SOURCE.stem + ".light.c")).read_text()
        for name, values in facts["functions"].items():
            body = coverage.function_body(dump, name)
            baseline = 6 if name == "nested_twice" else 3
            assert values["loops"] == body.count("for (")
            assert values["installed"] == (values["loops"] > baseline)
            assert values["installed"] == coverage.installation_expected(mode, name)
            assert values["machine_bytes"] == frontend.machine_bytes(directory / "program", name)
    assert set(report["clight_dispatch"]) == set(probe.MODES)
    for mode, facts in report["clight_dispatch"].items():
        directory = WORK / mode
        for name, digest in facts["artifacts"].items():
            assert sha(directory / name) == digest, (mode, name)
        output = (directory / "branch-output.txt").read_text().splitlines()
        actual = [list(map(int, line.split()[1:])) for line in output if line.startswith("PATH ")]
        assert actual == [expected_dispatch(mode, row) for row in CASES]
        assert facts["cases_and_expected_dispatch"] == [[list(row), branch] for row, branch in zip(CASES, actual)]
        assert facts["calls"] == len(CASES) and not facts["assembly_path_claim"]
        assert "\n".join(line for line in output if not line.startswith("PATH ")) + "\n" == expected
    assert report["new_assembly_calls"] == len(CASES) * len(coverage.MODES)
    assert report["clight_dispatch_calls"] == len(CASES) * len(probe.MODES)
    assert not report["timing_or_profitability_measured"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    configure()
    if args.validate:
        validate_native(json.loads((WORK / "report.json").read_text()))
        print(json.dumps({"status": "validated", "report_sha256": sha(WORK / "report.json")}))
        return
    frontend.check_build()
    WORK.mkdir(parents=True, exist_ok=True)
    SOURCE.write_text(coverage.source_text())
    subprocess.run(["gcc", "-O0", "-fwrapv", str(SOURCE), "-o", str(WORK / "reference")], check=True)
    output = subprocess.check_output([str(WORK / "reference")], text=True, timeout=90)
    assert output == coverage.expected_output()
    (WORK / "reference-output.txt").write_text(output)
    configurations = {mode: coverage.compile_run(mode) for mode in coverage.MODES}
    dispatch = {mode: probe.clight_probe(mode) for mode in probe.MODES}
    report = bindings() | {"reference_sha256": sha(WORK / "reference-output.txt"),
                          "configurations": configurations, "clight_dispatch": dispatch,
                          "new_assembly_calls": len(CASES) * len(coverage.MODES),
                          "clight_dispatch_calls": len(CASES) * len(probe.MODES),
                          "additional_cases": [list(row) for row in EXTRA],
                          "arrays_checked": {"A": 6144, "B": 2048, "C": 2048},
                          "timing_or_profitability_measured": False}
    validate_native(report)
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "passed", "assembly_calls": report["new_assembly_calls"],
                      "clight_calls": report["clight_dispatch_calls"],
                      "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
