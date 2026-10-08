"""Extract checked multi-array source data and run real scheduling/codegen.

This is a source/candidate prototype, not a newly installed C-to-Asm compiler.
Build and execution outputs occupy a fresh checkpoint directory.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess

import audit_multi_tensor as audit
import build_memory_validator as original
import build_pipeline_pluto as scheduler

ROOT = audit.ROOT
WORK = ROOT / "build/multi-tensor/extracted-partitioned"
PROOF = audit.WORK / "report.json"
sha = audit.sha
NATIVE = ["adapters/compcert-memory/native/GuardMemoryNumbers.ml",
          "adapters/compcert-memory/native/GuardMemoryOracle.ml",
          "adapters/compcert-memory/native/GuardMemoryTopo.ml",
          "prototype/interface/native/GuardTensorAffineRegionCandidate.ml",
          "prototype/interface/native/GuardTensorLiteralRegionCandidate.ml",
          "prototype/annotated-polyhedral/native/GuardOpenScopIO.ml",
          "prototype/annotated-polyhedral/native/GuardTiledPreparedTensorCandidate.ml",
          "prototype/annotated-polyhedral/native/GuardTightPreparedTensorCandidate.ml",
          "prototype/annotated-polyhedral/native/GuardCompletedPreparedTensorCandidate.ml",
          "prototype/interface/native/GuardPartitionedMultiTensorCandidate.ml",
          "prototype/interface/native/MultiTensorPartitionedMain.ml"]
EXPECTED = {"checked-two-statement-source": True, "source-pointer-mismatch": False,
            "source-missing-second-store": False, "checked-sequential-identity": True,
            "dependence-reversed-two-stores": False, "missing-candidate-store": False,
            "unknown-second-pointer": False, "pointer-scratch-collision": False,
            "real-codegen-nonunit": True, "real-codegen-partial-unit": True,
            "real-codegen-all-unit": True}


def validate():
    audit.validate()
    report = json.loads((WORK / "report.json").read_text())
    assert report["status"] == "executed" and report["proof_report_sha256"] == sha(PROOF)
    assert {case["case"]: case["accepted"] for case in report["cases"]} == EXPECTED
    assert report["scheduler_report_sha256"] == sha(scheduler.REPORT)
    scheduler.validate()
    for path, digest in report["bindings"].items():
        assert sha(ROOT / path) == digest, path
    assert report["real_scheduler_executed"] and report["prepared_codegen_executed"]
    assert not report["target_loop_handwritten_for_pipeline_cases"]
    assert not report["generated_statements_executed"] and not report["whole_program_compiler_installed"]
    return report


def main():
    global WORK
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    parser.add_argument("--work", type=Path, default=WORK, help="fresh checkpoint directory")
    args = parser.parse_args()
    WORK = args.work.resolve()
    if args.validate or (WORK / "report.json").exists():
        report = validate()
        print(json.dumps({"status": "validated", "cases": len(report["cases"]),
                          "report_sha256": sha(WORK / "report.json")}))
        return
    assert not WORK.exists(), "Refusing to overwrite a prototype checkpoint"
    proof = audit.validate()
    pluto = scheduler.validate()
    WORK.mkdir(parents=True)
    prefix = original.EXTRACTION.split("Separate Extraction ", 1)[0]
    # These transparent Rocq definitions return their final argument. Inline
    # their bodies before extraction instead of eagerly evaluating unused
    # diagnostic strings through an OCaml identity function.
    prefix = prefix.replace('Extract Inlined Constant Debugging.failwith => "(fun _ _ default -> default)".\n', '')
    prefix += "Extraction Inline Debugging.trace Debugging.failwith.\n"
    prefix = "From Guard Require Import ClightStructuredProgress.\nFrom GuardInterface Require Import ClightLoopAdministrative ClightMultiTensorExample ClightMultiTensorCandidates GuardMemoryTiledPreparedPipeline ClightTensorRegionPreservation.\n" + prefix
    source = prefix + """Separate Extraction ClightMultiTensorExample.multi_tensor_demo_body
  ClightMultiTensorExample.multi_tensor_demo_store ClightMultiTensorExample.multi_tensor_demo_recognized
  ClightMultiTensorExample.multi_tensor_demo_instructions ClightMultiTensorExample.multi_tensor_demo_source
  ClightMultiTensorExample.multi_tensor_demo_dimensions ClightMultiTensorExample.multi_tensor_demo_pointers
  ClightMultiTensorExample.multi_tensor_demo_layout ClightMultiTensorExample.multi_tensor_demo_live
  ClightMultiTensorExample.multi_tensor_demo_pool ClightMultiTensorCandidates.check_multi_tensor_generated
  GuardMemoryTiledPreparedPipeline.checked_memory_tiled_prepared_loop
  ClightLoopAdministrative.trim_loop_skips ClightStructuredProgress.progress_syntax_size
  ClightTensorRegionPackage.tensor_propose_nest
  ClightTensorRegionPreservation.check_tensor_region_candidate LinTerm.LinQ.export CstrC.Cstr.isContrad.
"""
    extraction = WORK / "Extract.v"
    extraction.write_text(source)
    with (WORK / "build.log").open("w") as log:
        def run(*arguments):
            subprocess.run(arguments, cwd=WORK, stdout=log, stderr=subprocess.STDOUT, check=True)
        run("rocq", "compile", *audit.language.flags(), str(extraction))
        for module in ["ImpureConfig", "TilingValidator", "GuardMemoryPolyhedral", "GuardMemoryTilingProgress"]:
            (WORK / (module + ".mli")).unlink(missing_ok=True)
        for path in WORK.glob("*.ml"):
            assert "AXIOM TO BE REALIZED" not in path.read_text(), path.name
        for path in NATIVE:
            shutil.copy2(ROOT / path, WORK / Path(path).name)
        files = sorted(path.name for path in WORK.glob("*.ml"))
        ordered = subprocess.check_output(["ocamlfind", "ocamldep", "-sort", *files], cwd=WORK, text=True).split()
        for name in ordered:
            interface = Path(name).with_suffix(".mli")
            if (WORK / interface).is_file():
                run("ocamlfind", "ocamlopt", "-package", "zarith,unix", "-c", str(interface))
            run("ocamlfind", "ocamlopt", "-package", "zarith,unix", "-c", name)
        executable = WORK / "multi-tensor-prototype"
        run("ocamlfind", "ocamlopt", "-package", "zarith,unix", "-linkpkg", "-o", str(executable),
            *[str(Path(name).with_suffix(".cmx")) for name in ordered])
    env = dict(os.environ, GUARDCERT_PLUTO=str(ROOT / pluto["binary"]),
               GUARDCERT_PIPELINE_DUMP=str(WORK / "phases"), GUARDCERT_TENSOR_DIAGNOSTICS="1")
    output = subprocess.run([str(executable)], cwd=WORK, env=env, capture_output=True, text=True)
    (WORK / "run.log").write_text(output.stdout)
    (WORK / "diagnostics.log").write_text(output.stderr)
    assert output.returncode == 0, output.stdout + output.stderr
    cases = [json.loads(line) for line in output.stdout.splitlines()]
    assert {case["case"]: case["accepted"] for case in cases} == EXPECTED
    for mask in ["nonunit", "partial-unit", "all-unit"]:
        directories = list((WORK / "phases" / mask).glob("guardcert-phase-*"))
        assert len(directories) == 1, mask
        phase = directories[0]
        for name in ["command.txt", "source.loop", "before.scop", "raw-generated.loop", "generated.loop", "receipt.txt"]:
            assert (phase / name).is_file(), (mask, name)
        assert (phase / "source.loop").read_text().count("instruction array=") == 2
        assert "prepared-codegen=successful" in (phase / "receipt.txt").read_text()
    bindings = {ROOT / path: sha(ROOT / path) for path in NATIVE}
    bindings[Path(__file__)] = sha(Path(__file__))
    bindings[ROOT / "scripts/build_memory_validator.py"] = sha(ROOT / "scripts/build_memory_validator.py")
    bindings |= {path: sha(path) for path in WORK.rglob("*") if path.is_file()}
    report = {"status": "executed", "kind": "checked-multi-array-source-and-real-generated-candidate-prototype",
              "proof_report_sha256": sha(PROOF), "proof_endpoints": len(proof["queried_endpoints"]),
              "scheduler_report_sha256": sha(scheduler.REPORT), "cases": cases,
              "real_scheduler_executed": True, "prepared_codegen_executed": True,
              "target_loop_handwritten_for_pipeline_cases": False, "generated_statements_executed": False,
              "whole_program_compiler_installed": False, "new_dynamic_guard_installed": False,
              "debug_identity_definitions_inlined": ["Debugging.trace", "Debugging.failwith"],
              "prepared_codegen_scope": "each statement of the checked whole transformed model",
              "statement_distribution_proposed": True, "whole_source_candidate_checked": True,
              "raw_to_composed_equivalence_proved": False,
              "C_or_assembly_evidence_added": False, "runtime_cross_array_alias_checked": False,
              "scope": "two dependent checked actual Horner assignments; old certificate checker with new multi-pointer lowering; real pipeline proposals for nonunit, partial-unit and all-unit tiles",
              "bindings": {str(path.relative_to(ROOT)): digest for path, digest in bindings.items()}}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "executed", "cases": len(cases),
                      "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
