From Stdlib Require Import List Bool.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Clight Csyntax Csem Cstrategy SimplExpr SimplExprproof
  SimplLocals SimplLocalsproof.
From compcert.driver Require Import Compiler.
From compcert.x86 Require Import Asm.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import GuardCompiler ClightRegionProgress ClightProgramEnvironment ClightGlobalScope ClightPrivatePool
  ClightTempFootprint ClightTempScope ClightScopedPrivateRegion.
From GuardMemory Require Import GuardMemoryDoubleCandidateProgress.
From GuardInterface Require Import ClightScopedSelectedRegion ClightScopedSelectedRegionProof
  OriginalMatmulProgramBindings OriginalMatmulSelectedInstallation
  OriginalMatmulProgramCompiler OriginalMatmulRawSelectedInstallation.
From GuardOriginalMatmul Require Import OriginalMatmul.
From GuardOriginalMatmulPrepared Require Import OriginalMatmulPrepared.
From GuardOriginalMatmulDoubleLowering Require Import OriginalMatmulDoubleLowering.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

(** This successor installs the literal frontend source, retaining its raw
    fallback. The checked environment/public-scope profile is reused. *)
Definition apply_profiled_raw_original_matmul chosen code p :=
  ScopedSelectedRegion.transform_program chosen original_matmul_private_pool original_matmul_raw_progress_supported
    (original_matmul_raw_selected_candidate code) p.
Theorem apply_profiled_raw_original_matmul_correct chosen schedule swaps generated code p :
  original_matmul_program_profile p=true ->
  mayReturn (checked_double_prepared_loop_progress schedule swaps original_matmul_pipeline_request) (Some generated) ->
  original_matmul_compile_candidate generated=Some code ->
  forward_simulation (Clight.semantics2 p) (Clight.semantics2 (apply_profiled_raw_original_matmul chosen code p)).
Proof.
  intros PROFILE PIPELINE CODE; destruct (original_matmul_program_profile_sound p PROFILE) as [ENV [SCOPE GLOBAL]].
  eapply ScopedSelectedRegionProof.transform_program_correct2 with (live:=program_temps prog) (globals:=original_matmul_globals).
  - exact original_matmul_raw_progress_supported_sound.
  - exact GLOBAL.
  - intros source target SELECT; eapply scoped_contract_reference_transport; [exact ENV|].
    eapply original_matmul_raw_selected_candidate_sound; eauto.
  - exact SCOPE.
  - apply private_pool_check_sound; exact original_matmul_private_pool_checked.
Qed.
Definition checked_raw_original_matmul_program chosen schedule swaps p :=
  match chosen with [] => pure p | _ =>
    if original_matmul_program_profile p then
      BIND generated <- checked_double_prepared_loop_progress schedule swaps original_matmul_pipeline_request -;
      match generated with None => pure p | Some candidate =>
        match original_matmul_compile_candidate candidate with None => pure p | Some code =>
          pure (apply_profiled_raw_original_matmul chosen code p) end end
    else pure p end.
Theorem checked_raw_original_matmul_program_correct chosen schedule swaps p target :
  mayReturn (checked_raw_original_matmul_program chosen schedule swaps p) target ->
  forward_simulation (Clight.semantics2 p) (Clight.semantics2 target).
Proof.
  unfold checked_raw_original_matmul_program; destruct chosen as [|label rest].
  - intro RUN; apply mayReturn_pure in RUN; subst target; apply unchanged_clight_simulation.
  - destruct (original_matmul_program_profile p) eqn:PROFILE.
    + intro RUN; bind_imp_destruct RUN generated PIPELINE; destruct generated as [candidate|].
      * destruct (original_matmul_compile_candidate candidate) as [code|] eqn:CODE;
          apply mayReturn_pure in RUN; subst target.
        -- eapply apply_profiled_raw_original_matmul_correct; eauto.
        -- apply unchanged_clight_simulation.
      * apply mayReturn_pure in RUN; subst target; apply unchanged_clight_simulation.
    + intro RUN; apply mayReturn_pure in RUN; subst target; apply unchanged_clight_simulation.
Qed.
Definition compile_raw_original_matmul_program chosen schedule swaps (program : Csyntax.program) : Base.imp (res Asm.program) :=
  match SimplExpr.transl_program program with Error errors => pure (Error errors) | OK clight =>
    match SimplLocals.transf_program clight with Error errors => pure (Error errors) | OK normalized =>
      BIND target <- checked_raw_original_matmul_program chosen schedule swaps normalized -;
      pure (compile_clight_tail (Compiler.print Compiler.print_Clight target)) end end.
Theorem raw_original_matmul_cstrategy_forward chosen schedule swaps program target :
  mayReturn (compile_raw_original_matmul_program chosen schedule swaps program) (OK target) ->
  forward_simulation (Cstrategy.semantics program) (Asm.semantics target).
Proof.
  unfold compile_raw_original_matmul_program; destruct (SimplExpr.transl_program program) as [clight|errors] eqn:P1;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (SimplLocals.transf_program clight) as [normalized|errors] eqn:P2;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN installed INSTALL; apply mayReturn_pure in RUN.
  rewrite Compiler.print_identity in RUN.
  eapply compose_forward_simulations.
  { eapply SimplExprproof.transl_program_correct; eauto using SimplExprproof.transf_program_match. }
  eapply compose_forward_simulations.
  { eapply SimplLocalsproof.transf_program_correct; eauto using SimplLocalsproof.match_transf_program. }
  eapply compose_forward_simulations.
  { eapply checked_raw_original_matmul_program_correct; exact INSTALL. }
  eapply clight_tail_correct; exact RUN.
Qed.
Theorem compile_raw_original_matmul_program_correct chosen schedule swaps program target :
  mayReturn (compile_raw_original_matmul_program chosen schedule swaps program) (OK target) ->
  backward_simulation (Csem.semantics program) (Asm.semantics target).
Proof.
  intro RUN; apply compose_backward_simulation with (atomic (Cstrategy.semantics program)).
  - eapply sd_traces; eapply Asm.semantics_determinate.
  - apply factor_backward_simulation.
    + apply Cstrategy.strategy_simulation.
    + apply Csem.semantics_single_events.
    + eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.
  - apply forward_to_backward_simulation.
    + apply factor_forward_simulation.
      * eapply raw_original_matmul_cstrategy_forward; exact RUN.
      * eapply sd_traces; eapply Asm.semantics_determinate.
    + apply atomic_receptive; apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
Qed.
Print Assumptions apply_profiled_raw_original_matmul_correct.
Print Assumptions checked_raw_original_matmul_program_correct.
Print Assumptions raw_original_matmul_cstrategy_forward.
Print Assumptions compile_raw_original_matmul_program_correct.
