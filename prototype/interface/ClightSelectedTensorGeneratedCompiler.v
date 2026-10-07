From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Clight Csyntax Csem Cstrategy
  SimplExpr SimplExprproof SimplLocals SimplLocalsproof.
From compcert.driver Require Import Compiler.
From compcert.x86 Require Import Asm.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion ClightPrivatePool ClightTempFootprint
  ClightRegionProgress GuardCompiler.
From GuardMemory Require Import GuardMemoryTensorSource GuardMemoryNamedCompiler GuardMemoryTiledCompiler GuardMemoryCompiler.
From GuardInterface Require Import ClightCheckPlanFrame ClightLiteralBoundPreparation ClightTensorLiteralPreservation
  ClightTensorRegionPackage ClightTensorRegionPreservation ClightTensorRegionCompiler
  ClightMaterializedCheck ClightSharedGuard ClightExpressionRegionHost ClightSelectedRegion ClightSelectedExpressionHost ClightTensorLiteralCompiler ClightTensorGeneratedFactory.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

Definition compile_selected_tensor_generated_regions chosen choose describe propose private_count(program:Csyntax.program) : Base.imp(res Asm.program) :=
  match SimplExpr.transl_program program with
  | Error errors=>pure(Error errors)
  | OK clight=>match SimplLocals.transf_program clight with
    | Error errors=>pure(Error errors)
    | OK normalized=>let live:=program_temps normalized in let pool:=propose_private_names live private_count in
      BIND table <- checked_tensor_generated_literal_regions live pool choose describe propose(selected_program_candidates chosen normalized) -;
      pure(compile_clight_tail(Compiler.print Compiler.print_Clight(apply_selected_expression_region_table chosen pool table normalized)))end end.

Theorem selected_tensor_generated_cstrategy_forward chosen choose describe propose private_count program target :
  mayReturn(compile_selected_tensor_generated_regions chosen choose describe propose private_count program)(OK target) ->
  forward_simulation(Cstrategy.semantics program)(Asm.semantics target).
Proof.
  unfold compile_selected_tensor_generated_regions; destruct(SimplExpr.transl_program program)as [clight|errors]eqn:P1;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(SimplLocals.transf_program clight)as [normalized|errors]eqn:P2;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN table TABLE; apply mayReturn_pure in RUN; rewrite Compiler.print_identity in RUN.
  eapply compose_forward_simulations.
  { eapply SimplExprproof.transl_program_correct; eauto using SimplExprproof.transf_program_match. }
  eapply compose_forward_simulations.
  { eapply SimplLocalsproof.transf_program_correct; eauto using SimplLocalsproof.match_transf_program. }
  eapply compose_forward_simulations.
  { apply apply_selected_expression_region_table_correct; eapply checked_tensor_generated_literal_regions_sound; exact TABLE. }
  eapply clight_tail_correct; exact RUN.
Qed.
Theorem compile_selected_tensor_generated_regions_correct chosen choose describe propose private_count program target :
  mayReturn(compile_selected_tensor_generated_regions chosen choose describe propose private_count program)(OK target) ->
  backward_simulation(Csem.semantics program)(Asm.semantics target).
Proof.
  intro RUN; apply compose_backward_simulation with(atomic(Cstrategy.semantics program)).
  - eapply sd_traces; eapply Asm.semantics_determinate.
  - apply factor_backward_simulation.
    + apply Cstrategy.strategy_simulation.
    + apply Csem.semantics_single_events.
    + eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.
  - apply forward_to_backward_simulation.
    + apply factor_forward_simulation.
      * eapply selected_tensor_generated_cstrategy_forward; exact RUN.
      * eapply sd_traces; eapply Asm.semantics_determinate.
    + apply atomic_receptive; apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
Qed.
Print Assumptions selected_tensor_generated_cstrategy_forward.
Print Assumptions compile_selected_tensor_generated_regions_correct.
