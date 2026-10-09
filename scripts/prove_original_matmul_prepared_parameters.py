"""Connect actual matmul capture and generated execution at the same parameters."""

import argparse
import json
from pathlib import Path
import subprocess

import audit_original_matmul_capture as parent
import audit_original_matmul_prepared as prepared
import audit_original_matmul_typed as typed
import polcert_core
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

WORK = ROOT / "build/original-matmul/source-prepared-parameters-v1"
NEST = ROOT / "build/original-matmul/source-nest-v1"
PIPELINE = ROOT / "build/original-matmul/source-pipeline-loop-v1"
CODE = r'''From Stdlib Require Import Bool List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.polygen Require Import Result.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivatePool ClightTempFrame ClightTempFootprint.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDoubleLocations GuardMemoryDoubleMatmul
  GuardMemoryDoubleMatmulLoops GuardMemoryDoubleNestControl GuardMemoryDoubleMatmulNest
  GuardMemoryDoubleMatmulInstr GuardMemoryDoubleMatmulPipelineLoop GuardMemoryDoublePolyhedral
  GuardMemoryDoublePrepared GuardMemoryDoublePreparedAt GuardMemoryDoubleMatmulCapture.
From GuardOriginalMatmul Require Import OriginalMatmul OriginalMatmulBody.
From GuardOriginalMatmulNest Require Import OriginalMatmulNest.
From GuardOriginalMatmulPipeline Require Import OriginalMatmulPipeline.
From GuardOriginalMatmulPrepared Require Import OriginalMatmulPrepared.
From GuardOriginalMatmulCapture Require Import OriginalMatmulCapture.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem original_matmul_generated_model_at schedule generated parameters ge layouts memory final :
  length parameters=3%nat ->
  mayReturn (checked_double_prepared_loop schedule original_matmul_pipeline_request) (Some generated) ->
  DoubleAssignmentIRs.Loop.loop_semantics (fst (fst generated)) parameters
    (RuntimeState (global_double_locations ge layouts) memory)
    (RuntimeState (global_double_locations ge layouts) final) ->
  DoubleAssignmentIRs.Loop.loop_semantics (double_matmul_pipeline_nest original_matmul_site) parameters
    (RuntimeState (global_double_locations ge layouts) memory)
    (RuntimeState (global_double_locations ge layouts) final).
Proof.
  intros LENGTH PIPELINE EXEC.
  eapply (@checked_double_prepared_loop_correct_at schedule original_matmul_pipeline_request
    generated parameters _ _ PIPELINE).
  - cbn; symmetry; exact LENGTH.
  - apply global_double_locations_nonalias.
  - exact EXEC.
Qed.

Theorem original_matmul_capture_to_generated_source fe ge locals temps memory blocks layouts
  m_block n_block k_block body source_after source_final :
  original_selected_body=Some body ->
  double_matmul_static ge locals original_matmul_site blocks ->
  double_matmul_layout_certificate original_matmul_site layouts ->
  double_global_binding ge locals _M m_block -> double_global_binding ge locals _N n_block ->
  double_global_binding ge locals _K k_block ->
  exec_stmt fe ge locals temps memory body E0 source_after source_final Out_normal ->
  exists (accepted : bool) prepared prepared_after,
    exec_stmt fe ge locals temps memory original_matmul_capture_code E0 prepared memory Out_normal /\
    prepared ! (matmul_capture_flag original_matmul_captures)=Some (Vint (if accepted then Int.one else Int.zero)) /\
    temp_agree (program_temps prog) temps prepared /\
    exec_stmt fe ge locals prepared memory body E0 prepared_after source_final Out_normal /\
    temp_agree (program_temps prog) source_after prepared_after /\
    (accepted=true -> exists rows columns depth,
      Z.of_nat rows<=98 /\ Z.of_nat columns<=98 /\ Z.of_nat depth<=98 /\
      prepared ! (matmul_capture_M original_matmul_captures)=Some (Vint (Int.repr (Z.of_nat rows))) /\
      prepared ! (matmul_capture_N original_matmul_captures)=Some (Vint (Int.repr (Z.of_nat columns))) /\
      prepared ! (matmul_capture_K original_matmul_captures)=Some (Vint (Int.repr (Z.of_nat depth))) /\
      forall schedule generated final,
        mayReturn (checked_double_prepared_loop schedule original_matmul_pipeline_request) (Some generated) ->
        DoubleAssignmentIRs.Loop.loop_semantics (fst (fst generated))
          [Z.of_nat rows;Z.of_nat columns;Z.of_nat depth]
          (RuntimeState (global_double_locations ge layouts) memory)
          (RuntimeState (global_double_locations ge layouts) final) ->
        exec_stmt fe ge locals prepared memory body E0
          (double_matmul_nest_exit original_matmul_site rows columns depth prepared) final Out_normal).
Proof.
  intros BODY STATIC LAYOUT MB NB KB SOURCE.
  pose proof BODY as SELECTED; rewrite original_selected_nest_exact in SELECTED; inversion SELECTED; subst body.
  destruct original_matmul_capture_resources as [DISTINCT PRIVATE].
  destruct (@double_matmul_source_capture fe ge locals temps memory original_matmul_site original_matmul_captures
    _M _N _K m_block n_block k_block 98 source_after source_final MB NB KB
    ltac:(change (0<=98<=2147483647); lia) DISTINCT PRIVATE SOURCE)
    as [accepted [prepared [CAPTURE [FLAG FACTS]]]].
  destruct (@double_matmul_capture_source_transport fe ge locals temps memory original_matmul_site
    original_matmul_captures _M _N _K 98 (program_temps prog) prepared source_after source_final
    original_matmul_capture_source_fresh CAPTURE SOURCE) as [prepared_after [PREPARED PUBLIC]].
  exists accepted,prepared,prepared_after; split; [exact CAPTURE|split; [exact FLAG|split]].
  - eapply double_matmul_capture_public_frame; [exact original_matmul_capture_public_fresh|exact CAPTURE].
  - split; [exact PREPARED|split; [exact PUBLIC|intro TRUE]].
    destruct (FACTS TRUE) as [rows [columns [depth [MR [NR [KR [MC [NC [KC INV]]]]]]]]].
    exists rows,columns,depth; split; [exact MR|split; [exact NR|split; [exact KR|]]].
    split; [exact MC|split; [exact NC|split; [exact KC|]]].
    intros schedule generated final PIPELINE EXEC.
    pose proof (@original_matmul_generated_model_at schedule generated
      [Z.of_nat rows;Z.of_nat columns;Z.of_nat depth] ge layouts memory final eq_refl PIPELINE EXEC) as MODEL.
    apply (proj2 (@original_full_nest_pipeline_model fe ge locals prepared memory blocks layouts
      m_block n_block k_block rows columns depth _ final _ BODY STATIC LAYOUT MB NB KB MR NR KR INV)).
    split; [exact MODEL|reflexivity].
Qed.
Print Assumptions original_matmul_generated_model_at.
Print Assumptions original_matmul_capture_to_generated_source.
'''


def flags():
    polcert_core.select_profile("optimizer")
    return [*polcert_core.load_flags(), "-Q", str(ROOT / "adapters/compcert-memory"), "GuardMemory",
            "-Q", str(ROOT / "prototype/interface"), "GuardInterface",
            "-R", str(ROOT / "vendor/CompCert/export"), "compcert.export",
            "-Q", str(typed.AST), "GuardOriginalMatmul",
            "-Q", str(NEST), "GuardOriginalMatmulNest",
            "-Q", str(PIPELINE), "GuardOriginalMatmulPipeline",
            "-Q", str(WORK), "GuardOriginalMatmulPreparedParameters",
            "-Q", str(parent.AST), "GuardOriginalMatmulCapture",
            "-Q", str(prepared.AST), "GuardOriginalMatmulPrepared"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not args.attempt or any(c not in "abcdefghijklmnopqrstuvwxyz0123456789-" for c in args.attempt):
        raise ValueError("Use a simple attempt name")
    baseline = parent.validate()
    prepared_baseline = prepared.validate()
    for name, digest in prepared_baseline["bindings"].items():
        if sha(permitted(ROOT / name)) != digest:
            raise ValueError(f"Changed prepared input: {name}")
    if (WORK / "report.json").exists():
        raise ValueError("Successful source checkpoint is frozen")
    WORK.mkdir(exist_ok=True)
    source = WORK / "OriginalMatmulPreparedParameters.v"
    if source.with_suffix(".vo").exists():
        raise ValueError("Successful proof object is frozen")
    source.write_text(CODE)
    archive = WORK / "attempts"
    archive.mkdir(exist_ok=True)
    with (archive / f"{args.attempt}.v").open("x") as snapshot:
        snapshot.write(CODE)
    argv = ["rocq", "compile", *flags(), str(source)]
    with (archive / f"{args.attempt}.log").open("x") as log:
        run = subprocess.run(argv, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    if run.returncode:
        print((archive / f"{args.attempt}.log").read_text()[-6000:])
        raise SystemExit(run.returncode)
    bindings = dict(baseline["bindings"])
    bindings.update(prepared_baseline["bindings"])
    for path in [Path(__file__), parent.WORK / "report.json", ROOT / "scripts/compile_prepared_parameters.py", prepared.WORK / "report.json", *WORK.rglob("*")]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(path)
    for module in ["PolCertPreparedParameters", "GuardMemoryDoublePreparedAt"]:
        for suffix in [".v", ".vo"]:
            directory = "theories" if module == "PolCertPreparedParameters" else "adapters/compcert-memory"
            path = ROOT / f"{directory}/{module}{suffix}"
            bindings[str(path.relative_to(ROOT))] = sha(path)
    report = {"status": "compiled", "kind": "actual-matmul-capture-to-same-parameter-generated-backward-source",
              "actual_selected_region_exact": True, "actual_checked_pipeline_consumed": True,
              "capture_and_fixed_parameter_generated_source_bridge": True,
              "original_source_fallback_runs_from_actual_checked_state": True,
              "header_load_and_range_premises_discharged": True,
              "static_bindings_layout_and_finite_normal_source_execution_still_required": True,
              "scope": "finite generated-model execution at the actual captured parameters implies concrete source execution",
              "candidate_Clight_lowering_or_progress_complete": False,
              "selected_compiler_connected": False, "new_native_optimized_case": False,
              "command": argv, "bindings": bindings}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "compiled", "bound_files": len(bindings), "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
