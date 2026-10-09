From Stdlib Require Import List Bool.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Clight Csyntax Csem Cstrategy
  SimplExpr SimplExprproof SimplLocals SimplLocalsproof.
From compcert.driver Require Import Compiler.
From compcert.x86 Require Import Asm.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import GuardCompiler ClightRegionProgress ClightGlobalScope ClightPrivatePool
  ClightTempFootprint ClightTempScope ClightScopedPrivateRegion ClightSyntaxEquality.
From GuardMemory Require Import GuardMemoryDoubleCandidateProgress GuardMemoryTiledCompiler.
From GuardInterface Require Import ClightSelectedRegion ClightScopedSelectedRegion ClightScopedSelectedRegionProof
  ReductionDoubleRegionFactory ReductionDoubleSelectedCompiler InitializedDoubleSelectedCompiler OriginalMatmulProgramCompiler.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

Definition checked_selected_reduction_witnesses_program chosen private_count schedule inherited_swaps reduction_swaps p :=
  BIND original <- InitializedDoubleSelectedCompiler.checked_selected_double_program chosen private_count schedule inherited_swaps p -;
  checked_selected_reduction_double_program chosen private_count schedule reduction_swaps original.
Theorem checked_selected_reduction_witnesses_program_correct chosen private_count schedule inherited_swaps reduction_swaps p target :
  mayReturn (checked_selected_reduction_witnesses_program chosen private_count schedule inherited_swaps reduction_swaps p) target ->
  forward_simulation (Clight.semantics2 p) (Clight.semantics2 target).
Proof.
  unfold checked_selected_reduction_witnesses_program; intro RUN; bind_imp_destruct RUN original ORIGINAL.
  eapply compose_forward_simulations.
  - eapply InitializedDoubleSelectedCompiler.checked_selected_double_program_correct; exact ORIGINAL.
  - eapply checked_selected_reduction_double_program_correct; exact RUN.
Qed.
Definition compile_selected_reduction_witnesses_program chosen private_count schedule inherited_swaps reduction_swaps (program : Csyntax.program) : Base.imp (res Asm.program) :=
  match SimplExpr.transl_program program with Error errors => pure (Error errors) | OK clight =>
    match SimplLocals.transf_program clight with Error errors => pure (Error errors) | OK normalized =>
      BIND target <- checked_selected_reduction_witnesses_program chosen private_count schedule inherited_swaps reduction_swaps normalized -;
      pure (compile_clight_tail (Compiler.print Compiler.print_Clight target)) end end.
Theorem selected_reduction_witnesses_program_cstrategy_forward chosen private_count schedule inherited_swaps reduction_swaps program target :
  mayReturn (compile_selected_reduction_witnesses_program chosen private_count schedule inherited_swaps reduction_swaps program) (OK target) ->
  forward_simulation (Cstrategy.semantics program) (Asm.semantics target).
Proof.
  unfold compile_selected_reduction_witnesses_program; destruct (SimplExpr.transl_program program) as [clight|errors] eqn:P1;
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
  { eapply checked_selected_reduction_witnesses_program_correct; exact INSTALL. }
  eapply clight_tail_correct; exact RUN.
Qed.
Theorem compile_selected_reduction_witnesses_program_correct chosen private_count schedule inherited_swaps reduction_swaps program target :
  mayReturn (compile_selected_reduction_witnesses_program chosen private_count schedule inherited_swaps reduction_swaps program) (OK target) ->
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
      * eapply selected_reduction_witnesses_program_cstrategy_forward; exact RUN.
      * eapply sd_traces; eapply Asm.semantics_determinate.
    + apply atomic_receptive; apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
Qed.


Print Assumptions checked_selected_reduction_witnesses_program_correct.
Print Assumptions selected_reduction_witnesses_program_cstrategy_forward.
Print Assumptions compile_selected_reduction_witnesses_program_correct.
