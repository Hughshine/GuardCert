"""Audit an automatic nonidentity affine layout phase through the frozen pipeline compiler."""
import argparse
import json
import os
import re
import subprocess

import native_prepared_pipeline as base
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/polyhedral-layout/native"
SCHEDULER = ROOT / "scripts/polyhedral_layout_scheduler.py"
NAMES = ["row-affine", "column-affine"]


def compile_run(name):
    column = name == "column-affine"
    directory = WORK/name
    directory.mkdir(parents=True)
    source = directory/"regions.c"
    source.write_text(base.source_text(column, True))
    env = {k: v for k, v in os.environ.items() if not k.startswith("GUARDCERT_")}
    env.update(GUARDCERT_TENSOR_MODE="pipeline", GUARDCERT_POLYHEDRAL_MODE="affine",
               GUARDCERT_PLUTO=str(SCHEDULER), GUARDCERT_LAYOUT_PLUTO=str(ROOT/base.scheduler.validate()["binary"]),
               GUARDCERT_PIPELINE_DUMP=str(directory/"phases"),
               GUARDCERT_TENSOR_DIAGNOSTICS="1", GUARDCERT_SCOP_DIAGNOSTICS="1")
    compiler = base.COMPILER
    with (directory/"compile.log").open("w") as log:
        subprocess.run([str(compiler), "-conf", str(compiler.parent/"compcert.ini"),
                        "-stdlib", str(compiler.parent/"runtime"), "-dclight", "-S", "-o",
                        str(directory/"program.s"), str(source)], cwd=directory, env=env,
                       stdout=log, stderr=subprocess.STDOUT, check=True, timeout=600)
    subprocess.run(["gcc", "-no-pie", str(directory/"program.s"), "-o", str(directory/"program")], check=True)
    output = subprocess.check_output([str(directory/"program")], text=True, timeout=90)
    (directory/"output.txt").write_text(output)
    assert output == base.expected_output(column), name
    dump = (directory/"regions.light.c").read_text()
    functions = {}
    for index, function in enumerate(base.fixtures.NAMES):
        actual = len(list(base.fixtures.prior.dispatch_sites(base.fixtures.function_body(dump, function))))
        expected = base.fixtures.MARKED[index] if index != 5 else 0
        assert actual == expected, (name, function, actual, expected)
        functions[function] = {"installed_sites": actual}
    manifest = re.findall(r"GUARDCERT_SCOP label=(\S+) file=(\S+) begin=(\d+) end=(\d+) statements=(\d+)",
                          (directory/"compile.log").read_text())
    assert len(manifest) == sum(base.fixtures.MARKED)
    phases = sorted((directory/"phases").glob("guardcert-phase-*"))
    assert len(phases) == 5
    for phase in phases:
        layout = json.loads((phase/"before.scop.layout-phase.json").read_text())
        assert layout["status"] == "proposed" and not layout["target_loop_constructed"]
        assert layout["layout_iterator_order"] == ([1, 0, 2] if column else [0, 1, 2])
        assert (phase/"before.scop.pluto-affine.scop").is_file()
        assert (phase/"receipt.txt").read_text() == "phase-validation=accepted\nprepared-codegen=successful\n"
        assert not (phase/"refusal.txt").exists()
        generated = (phase/"generated.loop").read_text()
        assert ("args=(v1,v2,v0,v6,v7)" if column else "args=(v2,v1,v0,v6,v7)") in generated
    return {"assembly_calls": len(base.fixtures.CASES), "functions": functions, "phase_invocations": len(phases),
            "nonidentity_schedule": column, "layout_iterator_order": [1, 0, 2] if column else [0, 1, 2]}


def validate():
    base.validate()
    report = json.loads((WORK/"report.json").read_text())
    assert report["status"] == "passed" and report["proved_entrypoint"] == base.ENTRY
    for path, digest in report["bindings"].items():
        assert sha(ROOT/path) == digest, path
    assert set(report["configurations"]) == set(NAMES) and set(report["clight_dispatch"]) == set(NAMES)
    for name in NAMES:
        assert (WORK/name/"regions.c").read_text() == base.source_text(name == "column-affine", True)
        assert (WORK/name/"output.txt").read_text() == base.expected_output(name == "column-affine")
        assert report["clight_dispatch"][name]["cases_and_dispatch"] == [
            [list(case), base.expected_dispatch(name,case)] for case in base.fixtures.CASES]
    assert report["configurations"]["column-affine"]["nonidentity_schedule"]
    assert report["assembly_calls"] == report["clight_dispatch_calls"] == 2*len(base.fixtures.CASES)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    if args.validate or (WORK/"report.json").exists():
        validate()
        print(json.dumps({"status": "validated", "report_sha256": sha(WORK/"report.json")}, indent=2))
        return
    base.validate()
    configurations = {name: compile_run(name) for name in NAMES}
    # Reuse the exact independent generated-Clight probe implementation; only
    # its artifact directory changes for these additional source compilations.
    old_work = base.WORK
    try:
        base.WORK = WORK
        dispatch = {name: base.branch_probe(name) for name in NAMES}
    finally:
        base.WORK = old_work
    base.validate()
    bindings = {SCHEDULER: sha(SCHEDULER), ROOT/"scripts/native_polyhedral_layout.py": sha(ROOT/"scripts/native_polyhedral_layout.py"),
                base.WORK/"report.json": sha(base.WORK/"report.json")}
    bindings |= {p: sha(p) for p in WORK.rglob("*") if p.is_file()}
    report = {"status": "passed", "proved_entrypoint": base.ENTRY,
              "configurations": configurations, "clight_dispatch": dispatch,
              "assembly_calls": 2*len(base.fixtures.CASES), "clight_dispatch_calls": 2*len(base.fixtures.CASES),
              "bindings": {str(p.relative_to(ROOT)): digest for p, digest in bindings.items()},
              "compiler_and_proof_reused_unchanged": True, "new_global_axioms": [],
              "nonidentity_schedule_generated_automatically": True, "target_loop_handwritten": False,
              "pluto_selected_the_layout_permutation": False,
              "candidate_producer": "Pluto affine phase plus GuardCert access-matrix layout phase, then checked prepared codegen",
              "tiling_integrated": False, "profitability_measured": False}
    (WORK/"report.json").write_text(json.dumps(report, indent=2)+"\n")
    validate()
    print(json.dumps({"status": "passed", "assembly_calls": report["assembly_calls"],
                      "clight_dispatch_calls": report["clight_dispatch_calls"],
                      "report_sha256": sha(WORK/"report.json")}, indent=2))


if __name__ == "__main__":
    main()
