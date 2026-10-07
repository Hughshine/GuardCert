"""Extract source-point syntax checks and guards; do not execute generated Clight."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess

import audit_tensor_header_point as audit

ROOT = audit.ROOT
WORK = ROOT / "build/tensor-header-point/extracted"
PROOF = audit.WORK / "report.json"
NATIVE = "prototype/interface/native/TensorHeaderPointMain.ml"
CASES = {"dynamic-product", "load-refused", "division-refused", "wrong-type-refused",
         "substitution-keeps-stride", "two-observer-tests", "actual-check-lowering", "conditional-child-capture"}
KIND = "extracted-tensor-header-point-syntax"


def validate():
    audit.validate()
    report = json.loads((WORK / "report.json").read_text())
    assert report["status"] == "executed" and report["kind"] == KIND
    assert report["proof_report_sha256"] == audit.sha(PROOF)
    for field, path in [("executable_sha256", WORK / "tensor-header-point"),
                        ("extraction_sha256", WORK / "Extract.v"),
                        ("build_helper_sha256", Path(__file__)),
                        ("native_source_sha256", ROOT / NATIVE), ("run_log_sha256", WORK / "run.log")]:
        assert report[field] == audit.sha(path), str(path)
    for file, digest in report["extracted_sources"].items():
        assert audit.sha(WORK / file) == digest, file
    assert {c["case"] for c in report["cases"]} == CASES
    assert len(report["cases"]) == len(CASES) and all(c["passed"] for c in report["cases"])
    assert report["condition_syntax_generation_executed"]
    assert not report["generated_Clight_executed"] and not report["C_or_assembly_evidence_added"]
    return report


def run(*args):
    subprocess.run(args, cwd=WORK, check=True, stdout=subprocess.DEVNULL)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    if parser.parse_args().validate or (WORK / "report.json").exists():
        report = validate()
        print(json.dumps({"status": "validated", "cases": len(report["cases"]),
                          "report_sha256": audit.sha(WORK / "report.json")}, indent=2))
        return
    audit.validate()
    WORK.mkdir(parents=True, exist_ok=True)
    extraction = WORK / "Extract.v"
    extraction.write_text("""From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNativeString ExtrOcamlZBigInt.
From GuardInterface Require Import ClightWordArithmeticTransport ClightDirectWordObservation
  ClightTensorHeaderFirstPoint ClightTensorHeaderCapture ClightTensorHeaderPointExample.
Set Extraction AccessOpaque.
Extraction Blacklist List String Int Misc.
Separate Extraction ClightWordArithmeticTransport.word_arithmetic_check
  ClightWordArithmeticTransport.word_replace ClightDirectWordObservation.direct_word_check_code
  ClightNestedConstantHeaders.ncs_observer_templates
  ClightTensorHeaderFirstPoint.tensor_zero_binding ClightTensorHeaderCapture.tensor_header_capture
  ClightTensorHeaderPointExample.thp_index ClightTensorHeaderPointExample.thp_cell
  ClightTensorHeaderPointExample.thp_shape ClightTensorHeaderPointExample.thp_observers.
""")
    run("rocq", "compile", *audit.deep.flags(), str(extraction))
    for path in WORK.glob("*.ml"):
        assert "AXIOM TO BE REALIZED" not in path.read_text(), path.name
    shutil.copy2(ROOT / NATIVE, WORK / Path(NATIVE).name)
    files = sorted(p.name for p in WORK.glob("*.ml"))
    ordered = subprocess.check_output(["ocamlfind", "ocamldep", "-sort", *files], cwd=WORK, text=True).split()
    for file in ordered:
        interface = Path(file).with_suffix(".mli")
        if (WORK / interface).exists():
            run("ocamlfind", "ocamlopt", "-package", "zarith", "-c", str(interface))
        run("ocamlfind", "ocamlopt", "-package", "zarith", "-c", file)
    executable = WORK / "tensor-header-point"
    run("ocamlfind", "ocamlopt", "-package", "zarith", "-linkpkg", "-o", str(executable),
        *[str(Path(file).with_suffix(".cmx")) for file in ordered])
    result = subprocess.run([str(executable)], cwd=WORK, capture_output=True, text=True)
    (WORK / "run.log").write_text(result.stdout + result.stderr)
    assert result.returncode == 0, result.stdout + result.stderr
    cases = [json.loads(line) for line in result.stdout.splitlines()]
    assert {c["case"] for c in cases} == CASES and all(c["passed"] for c in cases)
    report = {"status": "executed", "kind": KIND, "proof_report_sha256": audit.sha(PROOF),
              "executable_sha256": audit.sha(executable), "extraction_sha256": audit.sha(extraction),
              "build_helper_sha256": audit.sha(Path(__file__)), "native_source_sha256": audit.sha(ROOT / NATIVE),
              "extracted_sources": {p.name: audit.sha(p) for pattern in ["*.ml", "*.mli"] for p in WORK.glob(pattern)},
              "run_log_sha256": audit.sha(WORK / "run.log"), "cases": cases,
              "condition_syntax_generation_executed": True,
              "generated_Clight_executed": False, "C_or_assembly_evidence_added": False}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "executed", "cases": len(cases),
                      "report_sha256": audit.sha(WORK / "report.json")}, indent=2))


if __name__ == "__main__":
    main()
