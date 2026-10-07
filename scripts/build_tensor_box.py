"""Extract profiled tensor coordinate-condition synthesis and Clight lowering."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess

import audit_tensor_box as audit
import build_memory_validator as original

ROOT = audit.ROOT
WORK = ROOT / "build/tensor-coordinate-guard/extracted"
PROOF = audit.WORK / "report.json"
NATIVE = ["adapters/compcert-memory/native/GuardMemoryNumbers.ml",
          "prototype/interface/native/TensorBoxMain.ml"]
sha = audit.sha
EXPECTED = {"coordinate-guard-compiled": True, "negative-coefficient-compiled": True,
            "intermediate-overflow": False, "unknown-dimension": False, "profile-arity": False,
            "coordinate-box": True, "wide-columns": False, "wide-components": False,
            "outside-runtime-profile": False, "negative-coefficient": True,
            "negative-coordinate": False, "maximum-signed-scalar": True,
            "minimum-signed-scalar": True}
KIND = "extracted-profiled-tensor-coordinate-guard"


def validate():
    proof = audit.validate()
    report = json.loads((WORK / "report.json").read_text())
    assert report["status"] == "executed" and report["kind"] == KIND
    assert report["proof_report_sha256"] == sha(PROOF)
    assert report["proof_endpoints"] == len(proof["queried_endpoints"])
    assert report["executable_sha256"] == sha(WORK / "tensor-box-prototype")
    assert report["extraction_sha256"] == sha(WORK / "Extract.v")
    assert report["build_helper_sha256"] == sha(Path(__file__))
    assert report["extraction_helper_sha256"] == sha(ROOT / "scripts/build_memory_validator.py")
    for field, base in [("native_sources", ROOT), ("extracted_sources", WORK)]:
        for file, digest in report[field].items():
            assert sha(base / file) == digest, file
    assert report["run_log_sha256"] == sha(WORK / "run.log")
    assert {case["case"]: case["accepted"] for case in report["cases"]} == EXPECTED
    assert len(report["cases"]) == len(EXPECTED)
    for case in report["cases"]:
        if "generated_tests" in case:
            assert (case["generated_tests"] > 0) == case["accepted"]
    assert report["condition_synthesis_and_lowering_executed"]
    assert report["semantic_coordinate_flag_executed"]
    assert report["actual_guard_fixture_proofs_compiled"]
    assert not report["generated_machine_guard_executed"]
    assert not report["whole_program_compiler_installed"]
    assert not report["C_or_assembly_evidence_added"]
    return report


def run(*arguments):
    subprocess.run(arguments, cwd=WORK, check=True, stdout=subprocess.DEVNULL)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    if parser.parse_args().validate:
        report = validate()
        print(json.dumps({"status": "validated", "cases": len(report["cases"]),
                          "report_sha256": sha(WORK / "report.json")}, indent=2))
        return
    proof = audit.validate()
    WORK.mkdir(parents=True, exist_ok=True)
    for pattern in ("*.ml", "*.mli", "*.cmi", "*.cmx", "*.o"):
        for path in WORK.glob(pattern):
            path.unlink()
    source = original.EXTRACTION
    imports = "From GuardInterface Require Import ClightTensorBoxExample ClightTensorBoxGuard.\n"
    source = source.replace("From GuardMemory Require Import", imports + "From GuardMemory Require Import", 1)
    source = source.split("Separate Extraction ", 1)[0] + """Separate Extraction
  ClightTensorBoxExample.tensor_box_demo_compile
  ClightTensorBoxExample.tensor_box_demo_layout ClightTensorBoxExample.tensor_box_demo_scalars
  ClightTensorBoxExample.tensor_box_demo_profile ClightTensorBoxExample.tensor_box_demo_accesses
  ClightTensorBoxExample.tensor_box_demo_semantic_flag ClightTensorBoxExample.tensor_box_demo_full_guard
  ClightTensorSourceExample.tensor_source_demo_dimensions
  ClightTensorBoxGuard.compile_tensor_box_guard.
"""
    extraction = WORK / "Extract.v"
    extraction.write_text(source)
    run("rocq", "compile", *audit.deep.flags(), str(extraction))
    for name in ["ImpureConfig", "TilingValidator", "GuardMemoryPolyhedral", "GuardMemoryTilingProgress"]:
        (WORK / (name + ".mli")).unlink(missing_ok=True)
    for path in WORK.glob("*.ml"):
        assert "AXIOM TO BE REALIZED" not in path.read_text(), path.name
    for file in NATIVE:
        shutil.copy2(ROOT / file, WORK / Path(file).name)
    files = sorted(path.name for path in WORK.glob("*.ml"))
    ordered = subprocess.check_output(["ocamlfind", "ocamldep", "-sort", *files], cwd=WORK, text=True).split()
    for name in ordered:
        interface = Path(name).with_suffix(".mli")
        if (WORK / interface).is_file():
            run("ocamlfind", "ocamlopt", "-package", "zarith", "-c", str(interface))
        run("ocamlfind", "ocamlopt", "-package", "zarith", "-c", name)
    executable = WORK / "tensor-box-prototype"
    run("ocamlfind", "ocamlopt", "-package", "zarith", "-linkpkg", "-o", str(executable),
        *[str(Path(name).with_suffix(".cmx")) for name in ordered])
    output = subprocess.run([str(executable)], cwd=WORK, capture_output=True, text=True)
    (WORK / "run.log").write_text(output.stdout + output.stderr)
    assert output.returncode == 0, output.stdout + output.stderr
    cases = [json.loads(line) for line in output.stdout.splitlines()]
    assert {case["case"]: case["accepted"] for case in cases} == EXPECTED
    report = {"status": "executed", "kind": KIND,
              "proof_report_sha256": sha(PROOF), "executable_sha256": sha(executable),
              "extraction_sha256": sha(extraction), "build_helper_sha256": sha(Path(__file__)),
              "extraction_helper_sha256": sha(ROOT / "scripts/build_memory_validator.py"),
              "native_sources": {file: sha(ROOT / file) for file in NATIVE},
              "extracted_sources": {path.name: sha(path) for pattern in ["*.ml", "*.mli"]
                                    for path in WORK.glob(pattern)},
              "run_log_sha256": sha(WORK / "run.log"), "cases": cases,
              "condition_synthesis_and_lowering_executed": True,
              "semantic_coordinate_flag_executed": True,
              "actual_guard_fixture_proofs_compiled": True,
              "generated_machine_guard_executed": False,
              "whole_program_compiler_installed": False, "C_or_assembly_evidence_added": False,
              "proof_endpoints": len(proof["queried_endpoints"])}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "executed", "cases": len(cases),
                      "report_sha256": sha(WORK / "report.json")}, indent=2))


if __name__ == "__main__":
    main()
