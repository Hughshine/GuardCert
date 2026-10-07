"""Run the unchanged OLO adapted source through the extracted nested compiler."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess

from audit_interface_clight import ROOT, sha
from native_zero_trip import function_body
import native_olo_figure2 as original

COMPILER = ROOT / "build/nested-frontend/compiler/ccomp"
PROOF = ROOT / "build/nested-frontend/proof/report.json"
WORK = ROOT / "build/nested-frontend/native"
SOURCE = ROOT / "examples/olo_figure2_adapted.c"
ENTRY = "ClightGuardedNestedFrontendCompiler.compile_ncs_frontend_regions"
CONFIGURATIONS = ["disabled", "identity", "interchange", "tile-2-3", "wrong-reindex", "invalid-domain"]
INSTALLED = {"identity", "interchange", "tile-2-3"}
HELPERS = ["scripts/native_nested_frontend.py", "scripts/native_olo_figure2.py", "scripts/loaded_affine_reduced.py",
           "scripts/native_loaded_affine_multi.py", "scripts/native_zero_trip.py", "scripts/audit_interface_clight.py"]


def expected_output():
    return "".join(original.model(row) for row in original.CASES)


def check_build():
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    proof = json.loads(PROOF.read_text())
    assert stamp["proved_entrypoint"] == proof["whole_program_entrypoint"] == ENTRY
    assert proof["status"] == "compiled" and not proof["additional_global_axioms"]
    checks = {COMPILER: stamp["compiler_sha256"], PROOF: stamp["proof_report_sha256"],
              COMPILER.parent / "driver/Driver.ml": stamp["driver_sha256"],
              COMPILER.parent / "extract_nested_frontend.v": stamp["extraction_sha256"],
              ROOT / "scripts/build_nested_frontend.py": stamp["build_script_sha256"]}
    checks |= {ROOT / p: digest for p, digest in (stamp["proof_sources"] | stamp["native_sources"] | stamp["build_helpers"]).items()}
    checks |= {(ROOT / p).with_suffix(".vo"): digest for p, digest in proof["compiled_objects"].items()}
    checks |= {ROOT / p: digest for p, digest in proof["verification_helpers"].items()}
    for path, digest in checks.items():
        assert sha(path) == digest, path
    return stamp


def machine_bytes(binary, name):
    symbols = subprocess.check_output(["nm", "-S", "--defined-only", str(binary)], text=True)
    match = re.search(r"^\w+\s+(\w+)\s+[tT]\s+" + name + r"$", symbols, re.MULTILINE)
    assert match, name
    return int(match.group(1), 16)


def compile_run(mode):
    directory = WORK / mode
    directory.mkdir(parents=True, exist_ok=True)
    env = {key: value for key, value in os.environ.items() if not key.startswith("GUARDCERT_")}
    env.update(GUARDCERT_AFFINE_MODE=mode, GUARDCERT_AFFINE_CAP="4", GUARDCERT_AFFINE_BOUND_LOW="1",
               GUARDCERT_AFFINE_BOUND_HIGH="5", GUARDCERT_AFFINE_DIAGNOSTICS="1")
    with (directory / "compile.log").open("w") as log:
        run = subprocess.run([str(COMPILER), "-conf", str(COMPILER.parent / "compcert.ini"),
                              "-stdlib", str(COMPILER.parent / "runtime"), "-dclight", "-S", "-o",
                              str(directory / "program.s"), str(SOURCE)], cwd=directory, env=env,
                             stdout=log, stderr=subprocess.STDOUT, timeout=240)
    assert run.returncode == 0, (mode, (directory / "compile.log").read_text()[-3000:])
    assert "indexed=true exact=true checked=true depth=3" in (directory / "compile.log").read_text()
    subprocess.run(["gcc", "-no-pie", str(directory / "program.s"), "-o", str(directory / "program")], check=True)
    result = subprocess.run([str(directory / "program")], capture_output=True, text=True, timeout=90)
    assert result.returncode == 0, (mode, result.returncode, result.stderr)
    (directory / "output.txt").write_text(result.stdout)
    assert result.stdout == expected_output(), mode
    dump = directory / (SOURCE.stem + ".light.c")
    body = function_body(dump.read_text(), "bt_excerpt")
    loops = body.count("for (")
    assert (loops > 3) == (mode in INSTALLED), (mode, loops)
    assert "$row < *($shape + 0) + 1" in body and "$column < *($shape + 1) + 1" in body
    return {"installed": mode in INSTALLED, "loops": loops, "clight_bytes": len(body.encode()),
            "machine_bytes": machine_bytes(directory / "program", "bt_excerpt"), "calls": len(original.CASES),
            "artifacts": {p: sha(directory / p) for p in ["compile.log", "program.s", "program", dump.name, "output.txt"]}}


def validate():
    check_build()
    path = WORK / "report.json"
    report = json.loads(path.read_text())
    assert report["status"] == "passed" and report["proved_entrypoint"] == ENTRY
    assert report["source_sha256"] == sha(SOURCE) and SOURCE.read_text() == original.source_text()
    assert report["compiler_sha256"] == sha(COMPILER)
    assert report["stamp_sha256"] == sha(COMPILER.parent / ".guard-build.json")
    assert report["proof_report_sha256"] == sha(PROOF)
    assert report["cases"] == [list(row) for row in original.CASES]
    for helper, digest in report["helper_sources"].items():
        assert sha(ROOT / helper) == digest, helper
    assert sha(WORK / "reference-output.txt") == report["reference_sha256"]
    assert (WORK / "reference-output.txt").read_text() == expected_output()
    assert set(report["configurations"]) == set(CONFIGURATIONS)
    for mode, facts in report["configurations"].items():
        directory = WORK / mode
        for artifact, digest in facts["artifacts"].items():
            assert sha(directory / artifact) == digest, (mode, artifact)
        assert (directory / "output.txt").read_text() == expected_output()
        body = function_body((directory / (SOURCE.stem + ".light.c")).read_text(), "bt_excerpt")
        assert facts["loops"] == body.count("for (") and facts["installed"] == (mode in INSTALLED)
        assert facts["clight_bytes"] == len(body.encode())
        assert facts["machine_bytes"] == machine_bytes(directory / "program", "bt_excerpt")
        assert facts["calls"] == len(original.CASES)
    assert report["new_assembly_calls"] == sum(f["calls"] for f in report["configurations"].values()) == 48
    assert report["prior_coverage_report_unchanged"] and not report["timing_or_profitability_measured"]
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    if args.validate:
        validate()
        print(json.dumps({"status": "validated", "report_sha256": sha(WORK / "report.json")}, indent=2))
        return
    check_build()
    assert SOURCE.read_text() == original.source_text()
    WORK.mkdir(parents=True, exist_ok=True)
    subprocess.run(["gcc", "-O0", "-fwrapv", str(SOURCE), "-o", str(WORK / "reference")], check=True)
    reference = subprocess.check_output([str(WORK / "reference")], text=True)
    assert reference == expected_output()
    (WORK / "reference-output.txt").write_text(reference)
    facts = {}
    for mode in CONFIGURATIONS:
        print("Checking", mode, flush=True)
        facts[mode] = compile_run(mode)
    report = {"status": "passed", "proved_entrypoint": ENTRY, "compiler_sha256": sha(COMPILER),
              "proof_report_sha256": sha(PROOF), "stamp_sha256": sha(COMPILER.parent / ".guard-build.json"),
              "source_sha256": sha(SOURCE), "cases": original.CASES, "configurations": facts,
              "new_assembly_calls": sum(f["calls"] for f in facts.values()),
              "helper_sources": {p: sha(ROOT / p) for p in HELPERS}, "reference_sha256": sha(WORK / "reference-output.txt"),
              "source_class": "unchanged adapted OLO Figure 2 flat 16x16x5 source with two repeated loaded-plus-one headers",
              "original_array_root_and_child_retained_in_fallback": True, "prior_coverage_report_unchanged": True,
              "timing_or_profitability_measured": False, "machine_candidate_path_evidence_is_separate_report": True}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "passed", "assembly_calls": report["new_assembly_calls"],
                      "report_sha256": sha(WORK / "report.json")}, indent=2))


if __name__ == "__main__":
    main()
