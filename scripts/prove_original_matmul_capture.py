"""Connect actual matmul capture, public-state transport and the fixed source model."""

import argparse
import json
from pathlib import Path
import subprocess

import audit_original_matmul_header_license as parent
import audit_original_matmul_typed as typed
import polcert_core
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/original-matmul/source-capture-v1"
NEST = ROOT / "build/original-matmul/source-nest-v1"
PIPELINE = ROOT / "build/original-matmul/source-pipeline-loop-v1"
CODE = r'''From Stdlib Require Import Bool List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightPrivatePool ClightTempFrame ClightTempFootprint.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDoubleLocations GuardMemoryDoubleMatmul
  GuardMemoryDoubleMatmulLoops GuardMemoryDoubleNestControl GuardMemoryDoubleMatmulNest
  GuardMemoryDoubleMatmulInstr GuardMemoryDoubleMatmulPipelineLoop GuardMemoryDoublePolyhedral
  GuardMemoryDoubleMatmulCapture.
From GuardOriginalMatmul Require Import OriginalMatmul OriginalMatmulBody.
From GuardOriginalMatmulNest Require Import OriginalMatmulNest.
From GuardOriginalMatmulPipeline Require Import OriginalMatmulPipeline.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition original_matmul_capture_pool := propose_private_names (program_temps prog) 4.
Definition original_matmul_captures :=
  match original_matmul_capture_pool with
  | [(m,_);(n,_);(k,_);(flag,_)] => DoubleMatmulCaptures m n k flag
  | _ => DoubleMatmulCaptures 1%positive 2%positive 3%positive 4%positive
  end.
Definition original_matmul_capture_code := double_matmul_capture_code original_matmul_captures _M _N _K 98.

Theorem original_matmul_capture_resources :
  NoDup [matmul_capture_M original_matmul_captures;matmul_capture_N original_matmul_captures;
    matmul_capture_K original_matmul_captures] /\
  ~ In (matmul_capture_flag original_matmul_captures)
    [matmul_capture_M original_matmul_captures;matmul_capture_N original_matmul_captures;
     matmul_capture_K original_matmul_captures].
Proof.
  vm_compute; split; [repeat first [apply NoDup_cons|apply NoDup_nil]|]; cbn; intuition congruence.
Qed.
Theorem original_matmul_capture_pool_check :
  private_pool_check (program_temps prog) original_matmul_capture_pool=true.
Proof. vm_compute; reflexivity. Qed.
Lemma original_matmul_capture_pool_members id :
  In id (double_matmul_capture_ids original_matmul_captures) -> In id (var_names original_matmul_capture_pool).
Proof. vm_compute; tauto. Qed.
Theorem original_matmul_capture_public_fresh id : In id (program_temps prog) ->
  ~ In id (double_matmul_capture_ids original_matmul_captures).
Proof.
  intros PUBLIC PRIVATE; eapply (@private_pool_check_sound (program_temps prog) original_matmul_capture_pool
    original_matmul_capture_pool_check id PUBLIC); apply original_matmul_capture_pool_members; exact PRIVATE.
Qed.
Theorem original_matmul_capture_source_fresh id :
  In id (statement_temps (double_matmul_source_nest original_matmul_site _M _N _K)++program_temps prog) ->
  ~ In id (double_matmul_capture_ids original_matmul_captures).
Proof.
  rewrite in_app_iff; intros [SOURCE|PUBLIC].
  - vm_compute in SOURCE |- *; intuition congruence.
  - apply original_matmul_capture_public_fresh; exact PUBLIC.
Qed.

Theorem original_matmul_capture_and_source_model fe ge locals temps memory blocks layouts
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
      DoubleAssignmentIRs.Loop.loop_semantics (double_matmul_pipeline_nest original_matmul_site)
        [Z.of_nat rows;Z.of_nat columns;Z.of_nat depth]
        (RuntimeState (global_double_locations ge layouts) memory)
        (RuntimeState (global_double_locations ge layouts) source_final) /\
      prepared_after=double_matmul_nest_exit original_matmul_site rows columns depth prepared).
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
    destruct (proj1 (@original_full_nest_pipeline_model fe ge locals prepared memory blocks layouts
      m_block n_block k_block rows columns depth prepared_after source_final _ BODY STATIC LAYOUT
      MB NB KB MR NR KR INV) PREPARED) as [MODEL EXIT].
    exists rows,columns,depth; repeat split; assumption.
Qed.

Print Assumptions original_matmul_capture_resources.
Print Assumptions original_matmul_capture_pool_check.
Print Assumptions original_matmul_capture_public_fresh.
Print Assumptions original_matmul_capture_source_fresh.
Print Assumptions original_matmul_capture_and_source_model.
'''


def flags():
    polcert_core.select_profile("optimizer")
    return [*polcert_core.load_flags(), "-Q", str(ROOT / "adapters/compcert-memory"), "GuardMemory",
            "-Q", str(ROOT / "prototype/interface"), "GuardInterface",
            "-R", str(ROOT / "vendor/CompCert/export"), "compcert.export",
            "-Q", str(typed.AST), "GuardOriginalMatmul",
            "-Q", str(NEST), "GuardOriginalMatmulNest",
            "-Q", str(PIPELINE), "GuardOriginalMatmulPipeline",
            "-Q", str(WORK), "GuardOriginalMatmulCapture"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not args.attempt or any(c not in "abcdefghijklmnopqrstuvwxyz0123456789-" for c in args.attempt):
        raise ValueError("Use a simple attempt name")
    baseline = parent.validate()
    if (WORK / "report.json").exists():
        raise ValueError("Successful source checkpoint is frozen")
    WORK.mkdir(exist_ok=True)
    source = WORK / "OriginalMatmulCapture.v"
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
    for path in [Path(__file__), parent.WORK / "report.json", ROOT / "scripts/compile_matmul_capture.py", *WORK.rglob("*")]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(path)
    for module in ["GuardMemoryLongRangeCapture", "GuardMemoryLongCapturePath", "GuardMemoryDoubleMatmulCapture"]:
        for suffix in [".v", ".vo"]:
            path = ROOT / f"adapters/compcert-memory/{module}{suffix}"
            bindings[str(path.relative_to(ROOT))] = sha(path)
    report = {"status": "compiled", "kind": "actual-matmul-safe-conditional-capture-to-fixed-source-model",
              "actual_selected_region_exact": True, "read_licenses_from_original_source_execution": True,
              "entry_header_load_and_range_premises_discharged_by_capture": True,
              "fresh_I32_capture_names_from_actual_program_temps": True,
              "public_entry_and_source_exit_transport_proved": True,
              "original_source_fallback_runs_from_actual_checked_state": True,
              "source_model_at_actual_captured_parameters": True,
              "N_and_K_not_read_on_unreached_empty_paths": True,
              "static_bindings_layout_and_finite_normal_execution_still_required": True,
              "generated_candidate_fixed_parameter_bridge_complete": False,
              "selected_compiler_connected": False, "new_native_optimized_case": False,
              "command": argv, "bindings": bindings}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "compiled", "bound_files": len(bindings), "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
