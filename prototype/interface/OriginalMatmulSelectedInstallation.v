From Stdlib Require Import List Bool.
From compcert.common Require Import AST Smallstep.
From compcert.cfrontend Require Import Ctypes Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightSyntaxEquality ClightTempFootprint ClightTempScope ClightPrivatePool
  ClightGlobalScope ClightRegionProgress ClightScopedPrivateRegion.
From GuardMemory Require Import GuardMemoryDoubleCandidateProgress.
From GuardInterface Require Import ClightScopedSelectedRegion ClightScopedSelectedRegionProof
  OriginalMatmulSourceProgress OriginalMatmulProgramBindings.
From GuardOriginalMatmul Require Import OriginalMatmul OriginalMatmulBody.
From GuardOriginalMatmulCapture Require Import OriginalMatmulCapture.
From GuardOriginalMatmulDoubleLowering Require Import OriginalMatmulDoubleLowering.
From GuardOriginalMatmulPrepared Require Import OriginalMatmulPrepared.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

(** Concrete installation checkpoint for the original exported benchmark.
    The source is unchanged; only bodies under chosen labels are offered. *)
Definition original_matmul_private_pool := original_matmul_capture_pool++original_matmul_scratch_decls.
Lemma original_matmul_private_pool_checked : private_pool_check (program_temps prog) original_matmul_private_pool=true.
Proof. vm_compute; reflexivity. Qed.
Definition original_matmul_progress_supported source :=
  if statement_eq source original_matmul_region then true else false.
Theorem original_matmul_progress_supported_sound source : original_matmul_progress_supported source=true ->
  exists MODEL : region_progress source, True.
Proof.
  unfold original_matmul_progress_supported; destruct (statement_eq source original_matmul_region) as [SAME|DIFFERENT];
    [subst source; intros; exists original_matmul_source_progress; exact I|discriminate].
Qed.
Definition original_matmul_selected_candidate code source :=
  if statement_eq source original_matmul_region then Some (original_matmul_guarded_code original_matmul_region code) else None.
Theorem original_matmul_selected_candidate_sound schedule swaps generated code source target :
  mayReturn (checked_double_prepared_loop_progress schedule swaps original_matmul_pipeline_request) (Some generated) ->
  original_matmul_compile_candidate generated=Some code ->
  original_matmul_selected_candidate code source=Some target ->
  ScopedPrivateRegion.projected_region_contract (program_temps prog) (globalenv prog) original_matmul_globals source target.
Proof.
  intros PIPELINE CODE; unfold original_matmul_selected_candidate.
  destruct (statement_eq source original_matmul_region) as [SAME|DIFFERENT]; [subst source|discriminate].
  intro TARGET; inversion TARGET; subst target; eapply original_matmul_scoped_contract; eauto.
Qed.
Definition apply_original_matmul_selected chosen code :=
  if program_avoids_check original_matmul_globals prog && private_pool_check (program_temps prog) original_matmul_private_pool then
    ScopedSelectedRegion.transform_program chosen original_matmul_private_pool original_matmul_progress_supported
      (original_matmul_selected_candidate code) prog else prog.
Theorem apply_original_matmul_selected_correct chosen schedule swaps generated code :
  mayReturn (checked_double_prepared_loop_progress schedule swaps original_matmul_pipeline_request) (Some generated) ->
  original_matmul_compile_candidate generated=Some code ->
  forward_simulation (Clight.semantics2 prog) (Clight.semantics2 (apply_original_matmul_selected chosen code)).
Proof.
  intros PIPELINE CODE; unfold apply_original_matmul_selected.
  rewrite original_matmul_globals_checked,original_matmul_private_pool_checked; cbn [andb].
  eapply ScopedSelectedRegionProof.transform_program_correct2 with (live:=program_temps prog) (globals:=original_matmul_globals).
  - exact original_matmul_progress_supported_sound.
  - exact original_matmul_program_avoids.
  - intros; eapply original_matmul_selected_candidate_sound; eauto.
  - apply program_scope_computed.
  - apply private_pool_check_sound; exact original_matmul_private_pool_checked.
Qed.
Definition checked_original_matmul_install chosen schedule swaps :=
  BIND generated <- checked_double_prepared_loop_progress schedule swaps original_matmul_pipeline_request -;
  match generated with
  | None => pure prog
  | Some candidate => match original_matmul_compile_candidate candidate with
    | None => pure prog
    | Some code => pure (apply_original_matmul_selected chosen code) end end.
Theorem checked_original_matmul_install_correct chosen schedule swaps target :
  mayReturn (checked_original_matmul_install chosen schedule swaps) target ->
  forward_simulation (Clight.semantics2 prog) (Clight.semantics2 target).
Proof.
  unfold checked_original_matmul_install; intro RUN; bind_imp_destruct RUN generated PIPELINE.
  destruct generated as [candidate|]; [|apply mayReturn_pure in RUN; subst target].
  - destruct (original_matmul_compile_candidate candidate) as [code|] eqn:CODE;
      apply mayReturn_pure in RUN; subst target.
    + eapply apply_original_matmul_selected_correct; eauto.
    + apply forward_simulation_step with (match_states:=@eq Clight.state).
      * reflexivity.
      * intros source INIT; exists source; auto.
      * intros; subst; assumption.
      * intros source events next STEP current SAME; subst current; exists next; auto.
  - apply forward_simulation_step with (match_states:=@eq Clight.state).
    + reflexivity.
    + intros source INIT; exists source; auto.
    + intros; subst; assumption.
    + intros source events next STEP current SAME; subst current; exists next; auto.
Qed.
Print Assumptions original_matmul_private_pool_checked.
Print Assumptions original_matmul_progress_supported_sound.
Print Assumptions original_matmul_selected_candidate_sound.
Print Assumptions apply_original_matmul_selected_correct.
Print Assumptions checked_original_matmul_install_correct.
