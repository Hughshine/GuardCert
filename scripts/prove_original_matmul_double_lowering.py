"""Connect actual matmul capture and generated execution at the same parameters."""

import argparse
import json
from pathlib import Path
import subprocess

import audit_original_matmul_candidate_progress as parent
import audit_original_matmul_prepared as prepared
import audit_original_matmul_typed as typed
import polcert_core
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

WORK = ROOT / "build/original-matmul/source-double-lowering-v1"
NEST = ROOT / "build/original-matmul/source-nest-v1"
PIPELINE = ROOT / "build/original-matmul/source-pipeline-loop-v1"
CODE = r'''
From Stdlib Require Import Bool List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From polcert.polygen Require Import Result.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivatePool ClightTempFrame ClightTempFootprint ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDoubleLocations GuardMemoryDoubleMatmul
  GuardMemoryDoubleMatmulLoops GuardMemoryDoubleNestControl GuardMemoryDoubleMatmulNest
  GuardMemoryDoubleMatmulInstr GuardMemoryDoubleMatmulPipelineLoop GuardMemoryDoublePolyhedral
  GuardMemoryDoublePrepared GuardMemoryDoublePreparedAt GuardMemoryDoubleMatmulCapture GuardMemoryDoubleCandidateProgress
  GuardMemoryDoubleTensorBackend GuardMemoryDoubleNestedBackend GuardMemoryDoubleMatmulExit.
From GuardOriginalMatmul Require Import OriginalMatmul OriginalMatmulBody.
From GuardOriginalMatmulNest Require Import OriginalMatmulNest.
From GuardOriginalMatmulPipeline Require Import OriginalMatmulPipeline.
From GuardOriginalMatmulPrepared Require Import OriginalMatmulPrepared.
From GuardOriginalMatmulCapture Require Import OriginalMatmulCapture.
From GuardOriginalMatmulCandidateProgress Require Import OriginalMatmulCandidateProgress.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition original_matmul_double_layouts :=
  PTree.set _A [100;100] (PTree.set _B [100;100] (PTree.set _C [100;100]
    (PTree.set _alpha [] (PTree.set _beta [] (PTree.empty (list Z)))))).
Definition original_matmul_cache_layout :=
  [matmul_capture_M original_matmul_captures;matmul_capture_N original_matmul_captures;
   matmul_capture_K original_matmul_captures].
Definition original_matmul_candidate_bounds := repeat (DoubleNested.A.Interval 0 98) 3.
Definition original_matmul_scratch_decls := propose_private_names
  (program_temps prog++double_matmul_capture_ids original_matmul_captures) 6.
Definition original_matmul_scratch_pool := match original_matmul_scratch_decls with
  [(i,_);(ib,_);(j,_);(jb,_);(k,_);(kb,_)] => [(i,ib);(j,jb);(k,kb)] | _ => [] end.
Definition original_matmul_compile_candidate (generated : DoubleAssignmentIRs.Loop.t) := compile_double_tensor_loop original_matmul_double_layouts
  original_matmul_cache_layout original_matmul_candidate_bounds (program_temps prog) original_matmul_scratch_pool
  (fst (fst generated)).
Definition original_matmul_guarded_code body candidate := Ssequence original_matmul_capture_code
  (Sifthenelse (Etempvar (matmul_capture_flag original_matmul_captures) type_int32s)
    (Ssequence candidate (double_matmul_exit_code original_matmul_site original_matmul_captures)) body).

Lemma original_matmul_layout_certificate : double_matmul_layout_certificate original_matmul_site original_matmul_double_layouts.
Proof. vm_compute; repeat split; reflexivity. Qed.
Lemma original_matmul_tensor_static ge locals blocks :
  double_matmul_static ge locals original_matmul_site blocks ->
  double_tensor_static ge locals original_matmul_double_layouts.
Proof.
  intros STATIC array dimensions LAYOUT; unfold original_matmul_double_layouts in LAYOUT.
  rewrite !PTree.gsspec,PTree.gempty in LAYOUT.
  repeat match goal with H:context[peq ?first ?second] |- _ => destruct (peq first second); subst end;
    try discriminate; inversion LAYOUT; subst; split;
    try exact (proj1 (matmul_static_A STATIC)); try exact (proj1 (matmul_static_B STATIC));
    try exact (proj1 (matmul_static_C STATIC)); try exact (proj1 (matmul_static_alpha STATIC));
    try exact (proj1 (matmul_static_beta STATIC)).
  all: first [change (80000<=18446744073709551616)|change (8<=18446744073709551616)]; lia.
Qed.
Lemma original_matmul_scratch_checked : DoubleNested.N.scratch_check original_matmul_scratch_pool
  (original_matmul_cache_layout++program_temps prog)=true.
Proof. vm_compute; reflexivity. Qed.
Lemma original_matmul_exit_fresh : double_matmul_exit_fresh original_matmul_site original_matmul_captures.
Proof. vm_compute; intros; intuition congruence. Qed.
Lemma double_three_cache_view temps rows columns depth m_cache n_cache k_cache :
  0<=rows<=98 -> 0<=columns<=98 -> 0<=depth<=98 ->
  temps ! m_cache=Some (Vint (Int.repr rows)) ->
  temps ! n_cache=Some (Vint (Int.repr columns)) ->
  temps ! k_cache=Some (Vint (Int.repr depth)) ->
  DoubleNested.A.typed_view [m_cache;n_cache;k_cache] [rows;columns;depth] temps.
Proof.
  intros MR NR KR M N K [|[|[|n]]] parameter INDEX; cbn [nth_error] in INDEX.
  - inversion INDEX; subst parameter; exists (Int.repr rows); split; [exact M|cbn; apply Int.signed_repr; change (-2147483648<=rows<=2147483647); lia].
  - inversion INDEX; subst parameter; exists (Int.repr columns); split; [exact N|cbn; apply Int.signed_repr; change (-2147483648<=columns<=2147483647); lia].
  - inversion INDEX; subst parameter; exists (Int.repr depth); split; [exact K|cbn; apply Int.signed_repr; change (-2147483648<=depth<=2147483647); lia].
  - destruct n; discriminate.
Qed.
Lemma original_matmul_cache_view temps rows columns depth :
  0<=rows<=98 -> 0<=columns<=98 -> 0<=depth<=98 ->
  temps ! (matmul_capture_M original_matmul_captures)=Some (Vint (Int.repr rows)) ->
  temps ! (matmul_capture_N original_matmul_captures)=Some (Vint (Int.repr columns)) ->
  temps ! (matmul_capture_K original_matmul_captures)=Some (Vint (Int.repr depth)) ->
  DoubleNested.A.typed_view original_matmul_cache_layout [rows;columns;depth] temps.
Proof. unfold original_matmul_cache_layout; apply double_three_cache_view. Qed.
Lemma original_matmul_bounds_view rows columns depth : 0<=rows<=98 -> 0<=columns<=98 -> 0<=depth<=98 ->
  DoubleNested.A.env_within original_matmul_candidate_bounds [rows;columns;depth].
Proof.
  intros MR NR KR [|[|[|n]]] bound INDEX; cbn [original_matmul_candidate_bounds repeat nth_error] in INDEX.
  - inversion INDEX; subst bound; exact MR.
  - inversion INDEX; subst bound; exact NR.
  - inversion INDEX; subst bound; exact KR.
  - destruct n; discriminate.
Qed.

Theorem original_matmul_lowered_candidate_execution fe ge locals temps memory blocks generated code rows columns depth final :
  double_matmul_static ge locals original_matmul_site blocks ->
  original_matmul_compile_candidate generated=Some code ->
  0<=rows<=98 -> 0<=columns<=98 -> 0<=depth<=98 ->
  temps ! (matmul_capture_M original_matmul_captures)=Some (Vint (Int.repr rows)) ->
  temps ! (matmul_capture_N original_matmul_captures)=Some (Vint (Int.repr columns)) ->
  temps ! (matmul_capture_K original_matmul_captures)=Some (Vint (Int.repr depth)) ->
  DoubleAssignmentIRs.Loop.loop_semantics (fst (fst generated)) [rows;columns;depth]
    (RuntimeState (global_double_locations ge original_matmul_double_layouts) memory)
    (RuntimeState (global_double_locations ge original_matmul_double_layouts) final) ->
  exists target_temps, temp_agree (original_matmul_cache_layout++program_temps prog) temps target_temps /\
    exec_stmt fe ge locals temps memory code E0 target_temps final Out_normal.
Proof.
  intros STATIC CODE MR NR KR M N K MODEL.
  destruct (@compile_double_tensor_loop_correct fe ge locals original_matmul_double_layouts
    (original_matmul_tensor_static STATIC) original_matmul_cache_layout original_matmul_candidate_bounds
    (program_temps prog) original_matmul_scratch_pool (fst (fst generated)) code [rows;columns;depth] temps _ _ memory
    CODE (@original_matmul_cache_view temps rows columns depth MR NR KR M N K)
    (@original_matmul_bounds_view rows columns depth MR NR KR) MODEL
    ltac:(split; reflexivity)) as [target_temps [target_memory [[REG SAME] [FRAME RUN]]]].
  cbn [runtime_memory] in SAME; subst target_memory; exists target_temps; auto.
Qed.

Theorem original_matmul_guarded_candidate_execution fe ge locals temps memory blocks
  m_block n_block k_block body source_after source_final schedule swaps generated code :
  original_selected_body=Some body ->
  double_matmul_static ge locals original_matmul_site blocks ->
  double_global_binding ge locals _M m_block -> double_global_binding ge locals _N n_block ->
  double_global_binding ge locals _K k_block ->
  mayReturn (checked_double_prepared_loop_progress schedule swaps original_matmul_pipeline_request) (Some generated) ->
  original_matmul_compile_candidate generated=Some code ->
  exec_stmt fe ge locals temps memory body E0 source_after source_final Out_normal ->
  exists target_after, exec_stmt fe ge locals temps memory (original_matmul_guarded_code body code)
    E0 target_after source_final Out_normal /\ temp_agree (program_temps prog) source_after target_after.
Proof.
  intros BODY STATIC MB NB KB PIPELINE CODE SOURCE.
  destruct (@original_matmul_capture_to_candidate_progress fe ge locals temps memory blocks original_matmul_double_layouts
    m_block n_block k_block body source_after source_final BODY STATIC original_matmul_layout_certificate MB NB KB SOURCE)
    as [accepted [prepared [prepared_after [CAPTURE [FLAG [PUBLIC [FALLBACK [EXIT FACTS]]]]]]]].
  destruct accepted.
  - destruct (FACTS eq_refl) as [rows [columns [depth [MR [NR [KR [M [N [K [SET MODEL]]]]]]]]]].
    destruct (@original_matmul_lowered_candidate_execution fe ge locals prepared memory blocks generated code
      (Z.of_nat rows) (Z.of_nat columns) (Z.of_nat depth) source_final STATIC CODE
      ltac:(lia) ltac:(lia) ltac:(lia) M N K (MODEL schedule swaps generated PIPELINE))
      as [candidate_after [FRAME CANDIDATE]].
    assert (CACHE_FRAME : temp_agree original_matmul_cache_layout prepared candidate_after).
    { eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER; apply in_or_app; left; exact MEMBER. }
    assert (PUBLIC_FRAME : temp_agree (program_temps prog) prepared candidate_after).
    { eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER; apply in_or_app; right; exact MEMBER. }
    assert (RESTORE : exec_stmt fe ge locals candidate_after source_final
      (double_matmul_exit_code original_matmul_site original_matmul_captures) E0
      (double_matmul_nest_exit original_matmul_site rows columns depth candidate_after) source_final Out_normal).
    { apply double_matmul_exit_execution; [exact original_matmul_exit_fresh| | | | | |].
      - change (-2147483648<=Z.of_nat rows<=2147483647); lia.
      - change (-2147483648<=Z.of_nat columns<=2147483647); lia.
      - change (-2147483648<=Z.of_nat depth<=2147483647); lia.
      - rewrite (CACHE_FRAME _ (or_introl eq_refl)); exact M.
      - rewrite (CACHE_FRAME _ (or_intror (or_introl eq_refl))); exact N.
      - rewrite (CACHE_FRAME _ (or_intror (or_intror (or_introl eq_refl)))); exact K. }
    exists (double_matmul_nest_exit original_matmul_site rows columns depth candidate_after); split.
    + unfold original_matmul_guarded_code; eapply exec_Sseq_1 with (le1:=prepared) (m1:=memory) (t1:=E0) (t2:=E0);
        [exact CAPTURE|].
      eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true); [constructor; exact FLAG|reflexivity|].
      eapply exec_Sseq_1 with (le1:=candidate_after) (m1:=source_final) (t1:=E0) (t2:=E0); eassumption.
    + eapply temp_agree_trans; [exact EXIT|rewrite SET; apply double_matmul_exit_frame; exact PUBLIC_FRAME].
  - exists prepared_after; split; [|exact EXIT].
    unfold original_matmul_guarded_code; eapply exec_Sseq_1 with (le1:=prepared) (m1:=memory) (t1:=E0) (t2:=E0);
      [exact CAPTURE|].
    eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false); [constructor; exact FLAG|reflexivity|exact FALLBACK].
Qed.

Print Assumptions original_matmul_layout_certificate.
Print Assumptions original_matmul_tensor_static.
Print Assumptions original_matmul_scratch_checked.
Print Assumptions original_matmul_exit_fresh.
Print Assumptions original_matmul_lowered_candidate_execution.
Print Assumptions original_matmul_guarded_candidate_execution.
'''


def flags():
    polcert_core.select_profile("optimizer")
    return [*polcert_core.load_flags(), "-Q", str(ROOT / "adapters/compcert-memory"), "GuardMemory",
            "-Q", str(ROOT / "prototype/interface"), "GuardInterface",
            "-R", str(ROOT / "vendor/CompCert/export"), "compcert.export",
            "-Q", str(typed.AST), "GuardOriginalMatmul",
            "-Q", str(NEST), "GuardOriginalMatmulNest",
            "-Q", str(PIPELINE), "GuardOriginalMatmulPipeline",
            "-Q", str(WORK), "GuardOriginalMatmulDoubleLowering",
            "-Q", str(parent.parent.parent.AST), "GuardOriginalMatmulCapture",
            "-Q", str(prepared.AST), "GuardOriginalMatmulPrepared",
            "-Q", str(parent.AST), "GuardOriginalMatmulCandidateProgress"]


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
    source = WORK / "OriginalMatmulDoubleLowering.v"
    if source.with_suffix(".vo").exists():
        raise ValueError("Successful proof object is frozen")
    source.write_text(CODE)
    archive = WORK / "attempts"
    archive.mkdir(exist_ok=True)
    with (archive / f"{args.attempt}.v").open("x") as snapshot:
        snapshot.write(CODE)
    argv = ["rocq", "compile", "-time", *flags(), str(source)]
    with (archive / f"{args.attempt}.log").open("x") as log:
        run = subprocess.run(argv, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    if run.returncode:
        print((archive / f"{args.attempt}.log").read_text()[-6000:])
        raise SystemExit(run.returncode)
    bindings = dict(baseline["bindings"])
    bindings.update(prepared_baseline["bindings"])
    for path in [Path(__file__), parent.WORK / "report.json", ROOT / "scripts/compile_double_lowering.py", prepared.WORK / "report.json", *WORK.rglob("*")]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(path)
    for module in ["GuardMemoryRangedNested", "GuardMemoryDoubleAffineLong", "GuardMemoryDoubleTensorBackend", "GuardMemoryDoubleNestedBackend", "GuardMemoryDoubleMatmulExit"]:
        for suffix in [".v", ".vo"]:
            directory = "theories" if module.startswith("PolCert") else "adapters/compcert-memory"
            path = ROOT / f"{directory}/{module}{suffix}"
            bindings[str(path.relative_to(ROOT))] = sha(path)
    report = {"status": "compiled", "kind": "actual-matmul-capture-final-candidate-Clight-lowering-and-public-exit",
              "actual_selected_region_exact": True, "actual_checked_pipeline_consumed": True,
              "capture_and_actual_candidate_Clight_execution": True,
              "original_source_fallback_runs_from_actual_checked_state": True,
              "header_load_and_range_premises_discharged": True,
              "static_bindings_layout_and_finite_normal_source_execution_still_required": True,
              "scope": "finite actual source execution implies actual guarded Clight execution with identical final memory and public exits, given final pipeline/lowering receipts and static bindings",
              "candidate_model_progress_proved": True, "candidate_Clight_lowering_complete": True, "public_exit_restoration_proved": True,
              "selected_compiler_connected": False, "new_native_optimized_case": False,
              "command": argv, "bindings": bindings}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "compiled", "bound_files": len(bindings), "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
