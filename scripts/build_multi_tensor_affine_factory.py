"""Extract the generic full affine factory and check real scheduler/codegen proposals.

Execute the emitted-statement host; generated Clight and assembly are not executed.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess

import audit_multi_tensor_affine_versioned as audit
import build_memory_validator as original
import build_pipeline_pluto as scheduler

ROOT = audit.ROOT
WORK = ROOT / "build/multi-tensor-affine-versioned/extracted-factory-v2"
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
          "prototype/interface/native/MultiTensorAffineFactoryMain.ml"]
EXPECTED = {"full-producer-identity": True, "dependence-reversed": False,
            "missing-candidate-store": False, "exhausted-scan-pool": False,
            "wrong-source-description": False, "selected-two-sites-and-unmarked": True,
            "real-codegen-full-producer-nonunit": True,
            "real-codegen-full-producer-partial-unit": True,
            "real-codegen-full-producer-all-unit": True}


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
    assert not report["generated_statements_executed"] and not report["native_C_driver_connected"]
    assert report["full_factory_executed"] and report["selected_statement_host_executed"]
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
    prefix = "From GuardInterface Require Import ClightMultiTensorDataExample ClightMultiTensorAffineFactory ClightSelectedRegion.\nFrom Guard Require Import ClightStructuredProgress.\nFrom GuardInterface Require Import ClightLoopAdministrative ClightMultiTensorExample ClightMultiTensorCandidates GuardMemoryTiledPreparedPipeline ClightTensorRegionPreservation.\n" + prefix
    source = prefix + """Separate Extraction ClightMultiTensorDataExample.multi_tensor_data_source
  ClightMultiTensorDataExample.multi_tensor_data_description ClightMultiTensorDataExample.multi_tensor_data_assignments
  ClightMultiTensorDataExample.multi_tensor_data_assignment ClightMultiTensorAffineFactory.check_multi_tensor_affine_region
  ClightSelectedRegion.selected_transform_statement ClightStructuredProgress.structured_progress_supported
  GuardMemoryTiledCompiler.select_memory_tiled_table ClightTempFootprint.statement_temps Ctypes.type_int32s
  ClightMultiTensorExample.multi_tensor_demo_body
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
        ordered = subprocess.check_output(["ocamlfind", "ocamldep", "-sort", *files], cwd=WORK, text=True, stderr=log).split()
        for name in ordered:
            interface = Path(name).with_suffix(".mli")
            if (WORK / interface).is_file():
                run("ocamlfind", "ocamlopt", "-package", "zarith,unix", "-c", str(interface))
            run("ocamlfind", "ocamlopt", "-package", "zarith,unix", "-c", name)
        executable = WORK / "multi-tensor-affine-factory"
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
    report = {"status": "executed", "kind": "generic-full-affine-factory-real-codegen-and-selected-statement-host",
              "proof_report_sha256": sha(PROOF), "proof_endpoints": len(proof["queried_endpoints"]),
              "scheduler_report_sha256": sha(scheduler.REPORT), "cases": cases,
              "real_scheduler_executed": True, "prepared_codegen_executed": True,
              "target_loop_handwritten_for_pipeline_cases": False, "generated_statements_executed": False,
              "whole_program_compiler_theorem": True, "native_C_driver_connected": False,
              "full_factory_executed": True, "selected_statement_host_executed": True,
              "guarded_statement_emitted": True, "static_refusal_cases": 4,
              "marked_sites_checked": 2, "identical_unmarked_sites_preserved": 1,
              "new_dynamic_guard_installed_in_C_driver": False,
              "debug_identity_definitions_inlined": ["Debugging.trace", "Debugging.failwith"],
              "prepared_codegen_scope": "each statement of the checked whole transformed model",
              "statement_distribution_proposed": True, "whole_source_candidate_checked": True,
              "raw_to_composed_equivalence_proved": False,
              "C_or_assembly_evidence_added": False, "runtime_cross_array_alias_checked": False,
              "scope": "renamed two-store actual source; typed scan/candidate allocation; complete emitted guard/candidate/restore/fallback; real pipeline proposals for three tile masks; selected statement installation only",
              "bindings": {str(path.relative_to(ROOT)): digest for path, digest in bindings.items()}}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "executed", "cases": len(cases),
                      "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
