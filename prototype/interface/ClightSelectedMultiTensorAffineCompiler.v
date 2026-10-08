From Stdlib Require Import List Bool.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Clight Csyntax Csem Cstrategy
  SimplExpr SimplExprproof SimplLocals SimplLocalsproof.
From compcert.driver Require Import Compiler.
From compcert.x86 Require Import Asm.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion ClightPrivatePool ClightTempScope
  ClightTempFootprint ClightStructuredProgress GuardCompiler.
From GuardMemory Require Import GuardMemoryTiledCompiler.
From GuardInterface Require Import ClightSelectedRegion ClightSelectedRegionProof
  ClightMultiTensorAffineFactory.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

(** This host uses the same source progress classifier checked by the source
    factory. Selection remains occurrence-sensitive and pool/label checks
    remain language obligations. The generic guarded-choice kernel is unchanged. *)
Definition apply_selected_multi_tensor_affine_table chosen pool table (p : Clight.program) :=
  if private_pool_check (program_temps p) pool then
    selected_transform_program chosen pool structured_progress_supported
      (select_memory_tiled_table table) p else p.
Theorem apply_selected_multi_tensor_affine_table_correct chosen pool table p :
  Forall (fun pair => PrivateRegion.projected_region_contract
    (program_temps p) (fst pair) (snd pair)) table ->
  forward_simulation (Clight.semantics2 p)
    (Clight.semantics2 (apply_selected_multi_tensor_affine_table chosen pool table p)).
Proof.
  intro TABLE; unfold apply_selected_multi_tensor_affine_table.
  destruct (private_pool_check (program_temps p) pool) eqn:FRESH.
  - eapply SelectedRegionProof.transform_program_correct2 with (live:=program_temps p).
    + exact structured_progress_supported_sound.
    + apply select_memory_tiled_table_sound; exact TABLE.
    + apply program_scope_computed.
    + eapply private_pool_check_sound; exact FRESH.
  - apply forward_simulation_step with (match_states:=@eq Clight.state).
    + reflexivity.
    + intros source INIT; exists source; auto.
    + intros; subst; assumption.
    + intros source events next STEP target SAME; subst target; exists next; auto.
Qed.

Definition compile_selected_multi_tensor_affine_regions chosen describe propose private_count
    (program : Csyntax.program) : Base.imp (res Asm.program) :=
  match SimplExpr.transl_program program with
  | Error errors => pure (Error errors)
  | OK clight => match SimplLocals.transf_program clight with
    | Error errors => pure (Error errors)
    | OK normalized =>
      let live := program_temps normalized in
      let pool := propose_private_names live private_count in
      BIND table <- checked_multi_tensor_affine_regions live pool describe propose
        (selected_program_candidates chosen normalized) -;
      pure (compile_clight_tail (Compiler.print Compiler.print_Clight
        (apply_selected_multi_tensor_affine_table chosen pool table normalized)))
    end
  end.

Theorem selected_multi_tensor_affine_cstrategy_forward chosen describe propose private_count program target :
  mayReturn (compile_selected_multi_tensor_affine_regions chosen describe propose private_count program) (OK target) ->
  forward_simulation (Cstrategy.semantics program) (Asm.semantics target).
Proof.
  unfold compile_selected_multi_tensor_affine_regions.
  destruct (SimplExpr.transl_program program) as [clight|errors] eqn:P1;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (SimplLocals.transf_program clight) as [normalized|errors] eqn:P2;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN table TABLE; apply mayReturn_pure in RUN.
  rewrite Compiler.print_identity in RUN.
  eapply compose_forward_simulations.
  { eapply SimplExprproof.transl_program_correct; eauto using SimplExprproof.transf_program_match. }
  eapply compose_forward_simulations.
  { eapply SimplLocalsproof.transf_program_correct; eauto using SimplLocalsproof.match_transf_program. }
  eapply compose_forward_simulations.
  { apply apply_selected_multi_tensor_affine_table_correct;
      eapply checked_multi_tensor_affine_regions_sound; exact TABLE. }
  eapply clight_tail_correct; exact RUN.
Qed.
Theorem compile_selected_multi_tensor_affine_regions_correct chosen describe propose private_count program target :
  mayReturn (compile_selected_multi_tensor_affine_regions chosen describe propose private_count program) (OK target) ->
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
      * eapply selected_multi_tensor_affine_cstrategy_forward; exact RUN.
      * eapply sd_traces; eapply Asm.semantics_determinate.
    + apply atomic_receptive; apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
Qed.

Print Assumptions apply_selected_multi_tensor_affine_table_correct.
Print Assumptions selected_multi_tensor_affine_cstrategy_forward.
Print Assumptions compile_selected_multi_tensor_affine_regions_correct.
