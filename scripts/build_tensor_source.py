"""Extract tensor source recognition, semantic coordinate checks, and candidate lowering."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess

import audit_tensor_source as audit
import build_memory_validator as original

ROOT = audit.ROOT
WORK = ROOT / "build/tensor-original-source/extracted"
PROOF = audit.WORK / "report.json"
NATIVE = ["adapters/compcert-memory/native/GuardMemoryNumbers.ml",
          "adapters/compcert-memory/native/GuardMemoryOracle.ml",
          "adapters/compcert-memory/native/GuardMemoryTopo.ml",
          "prototype/interface/native/TensorSourceMain.ml"]
sha = audit.sha
EXPECTED = {"horner-source-recognized": True, "changed-rhs": False,
            "wrong-rank": False, "unknown-coordinate": False, "unused-read": False,
            "coordinate-box": True, "wide-columns": False,
            "negative-coefficient": True, "negative-coordinate": False,
            "source-instruction-mapped": True, "source-instruction-tiled": True,
            "zero-tile": False}


def validate():
    proof = audit.validate()
    report = json.loads((WORK / "report.json").read_text())
    assert report["status"] == "executed"
    assert report["kind"] == "extracted-original-tensor-source-prototype"
    assert report["proof_report_sha256"] == sha(PROOF)
    assert report["proof_endpoints"] == len(proof["queried_endpoints"])
    assert report["executable_sha256"] == sha(WORK / "tensor-source-prototype")
    assert report["extraction_sha256"] == sha(WORK / "Extract.v")
    assert report["build_helper_sha256"] == sha(Path(__file__))
    assert report["extraction_helper_sha256"] == sha(ROOT / "scripts/build_memory_validator.py")
    for field, base in [("native_sources", ROOT), ("extracted_sources", WORK)]:
        for file, digest in report[field].items():
            assert sha(base / file) == digest, file
    assert report["run_log_sha256"] == sha(WORK / "run.log")
    cases = report["cases"]
    assert len(cases) == len(EXPECTED)
    assert {case["case"]: case["accepted"] for case in cases} == EXPECTED
    assert all(case.get("alarm_free", True) for case in cases)
    assert all(case["statement_nodes"] > 0 for case in cases if case["case"] in
               {"source-instruction-mapped", "source-instruction-tiled"})
    assert report["source_descriptors_executed"] and report["semantic_coordinate_checker_executed"]
    assert not report["machine_coordinate_guard_executed"]
    assert not report["generated_statements_executed"]
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
        for p in WORK.glob(pattern):
            p.unlink()
    source = original.EXTRACTION
    imports = "From GuardInterface Require Import ClightTensorCandidates ClightTensorSourceExample.\nFrom GuardMemory Require Import GuardMemoryTensorSource GuardMemoryTensorSourceRegion.\n"
    source = source.replace("From GuardMemory Require Import", imports + "From GuardMemory Require Import", 1)
    prefix = source.split("Separate Extraction ", 1)[0]
    source = prefix + """Separate Extraction ClightTensorCandidates.check_tensor_mapped
  ClightTensorCandidates.check_tensor_tiled ClightTensorSourceExample.tensor_source_demo_code
  ClightTensorSourceExample.tensor_source_demo_cell ClightTensorSourceExample.tensor_source_demo_recognized
  ClightTensorSourceExample.tensor_source_demo_described ClightTensorSourceExample.tensor_source_demo_operation
  ClightTensorSourceExample.tensor_source_demo_access ClightTensorSourceExample.tensor_source_demo_dimensions
  ClightTensorSourceExample.tensor_source_demo_layout ClightTensorSourceExample.tensor_source_demo_loop
  GuardMemoryTensorSource.tensor_source_instruction GuardMemoryTensorSource.check_tensor_source_operation
  GuardMemoryTensorSourceRegion.tensor_source_operation_box GuardMemoryTensorSourceRegion.tensor_coordinate_box_check
  LinTerm.LinQ.export CstrC.Cstr.isContrad.
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
    files = sorted(p.name for p in WORK.glob("*.ml"))
    ordered = subprocess.check_output(["ocamlfind", "ocamldep", "-sort", *files], cwd=WORK, text=True).split()
    for name in ordered:
        interface = Path(name).with_suffix(".mli")
        if (WORK / interface).is_file():
            run("ocamlfind", "ocamlopt", "-package", "zarith", "-c", str(interface))
        run("ocamlfind", "ocamlopt", "-package", "zarith", "-c", name)
    executable = WORK / "tensor-source-prototype"
    run("ocamlfind", "ocamlopt", "-package", "zarith", "-linkpkg", "-o", str(executable),
        *[str(Path(name).with_suffix(".cmx")) for name in ordered])
    output = subprocess.run([str(executable)], cwd=WORK, capture_output=True, text=True)
    (WORK / "run.log").write_text(output.stdout + output.stderr)
    assert output.returncode == 0, output.stdout + output.stderr
    cases = [json.loads(line) for line in output.stdout.splitlines()]
    assert len(cases) == len(EXPECTED)
    assert {case["case"]: case["accepted"] for case in cases} == EXPECTED
    report = {"status": "executed", "kind": "extracted-original-tensor-source-prototype",
              "proof_report_sha256": sha(PROOF), "executable_sha256": sha(executable),
              "extraction_sha256": sha(extraction), "build_helper_sha256": sha(Path(__file__)),
              "extraction_helper_sha256": sha(ROOT / "scripts/build_memory_validator.py"),
              "native_sources": {file: sha(ROOT / file) for file in NATIVE},
              "extracted_sources": {p.name: sha(p) for pattern in ["*.ml", "*.mli"]
                                    for p in WORK.glob(pattern)},
              "run_log_sha256": sha(WORK / "run.log"), "cases": cases,
              "source_descriptors_executed": True, "semantic_coordinate_checker_executed": True,
              "machine_coordinate_guard_executed": False,
              "generated_statements_executed": False, "whole_program_compiler_installed": False,
              "C_or_assembly_evidence_added": False,
              "proof_endpoints": len(proof["queried_endpoints"])}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "executed", "cases": len(cases), "report_sha256": sha(WORK / "report.json")}, indent=2))


if __name__ == "__main__":
    main()
