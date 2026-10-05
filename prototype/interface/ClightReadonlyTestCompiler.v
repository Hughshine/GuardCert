From compcert.common Require Import Errors Smallstep Behaviors.
From compcert.cfrontend Require Import Clight Csyntax Csem Cstrategy SimplExpr
  SimplExprproof SimplLocals SimplLocalsproof.
From compcert.driver Require Import Compiler.
From Guard Require Import ClightGuard ClightCondition ClightTreeRewrite GuardCompiler.
From GuardInterface Require Import ClightReadonlyExpression ClightReadonlyTestSyntax ClightReadonlyTestProof.
Set Implicit Arguments.

Section USER_TEST_PASS.
Variable choose : forall source, option (readonly_expression_rule source).
Definition readonly_test_selection source : option (decision_tree * Clight.expr) :=
  match choose source with
  | Some rule => Some (expression_guard rule, expression_candidate rule)
  | None => None end.
Theorem readonly_test_selection_sound source guard candidate :
  readonly_test_selection source = Some (guard,candidate) -> expression_contract source guard candidate.
Proof.
  unfold readonly_test_selection; destruct (choose source) as [rule|]; [|discriminate].
  intro SAME; injection SAME as SAME SAME'; subst; apply readonly_expression_contract.
Qed.
Variable prior : Clight.program -> Clight.program.
Hypothesis PRIOR_CORRECT : forall p,
  forward_simulation (Clight.semantics2 p) (Clight.semantics2 (prior p)).
Definition compile_readonly_tests_after (p : Csyntax.program) : res Asm.program :=
  match SimplExpr.transl_program p with
  | Error err => Error err
  | OK p1 => match SimplLocals.transf_program p1 with
    | Error err => Error err
    | OK p2 => compile_clight_tail (Compiler.print Compiler.print_Clight
        (ClightReadonlyTestSyntax.transform_program readonly_test_selection (prior p2)))
    end end.
Theorem readonly_test_cstrategy_forward p target : compile_readonly_tests_after p = OK target ->
  forward_simulation (Cstrategy.semantics p) (Asm.semantics target).
Proof.
  intro COMPILE; unfold compile_readonly_tests_after in COMPILE.
  destruct (SimplExpr.transl_program p) as [p1|err] eqn:P1; try discriminate.
  destruct (SimplLocals.transf_program p1) as [p2|err] eqn:P2; try discriminate.
  rewrite Compiler.print_identity in COMPILE.
  eapply compose_forward_simulations.
  { eapply SimplExprproof.transl_program_correct; eauto using SimplExprproof.transf_program_match. }
  eapply compose_forward_simulations.
  { eapply SimplLocalsproof.transf_program_correct; eauto using SimplLocalsproof.match_transf_program. }
  eapply compose_forward_simulations.
  { apply PRIOR_CORRECT. }
  eapply compose_forward_simulations.
  { apply ClightReadonlyTestProof.transform_program_correct2; exact readonly_test_selection_sound. }
  eapply clight_tail_correct; eauto.
Qed.
Theorem compile_readonly_tests_after_correct p target : compile_readonly_tests_after p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof.
  intro COMPILE; apply compose_backward_simulation with (atomic (Cstrategy.semantics p)).
  - eapply sd_traces; eapply Asm.semantics_determinate.
  - apply factor_backward_simulation.
    + apply Cstrategy.strategy_simulation.
    + apply Csem.semantics_single_events.
    + eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.
  - apply forward_to_backward_simulation.
    + apply factor_forward_simulation.
      * eapply readonly_test_cstrategy_forward; eauto.
      * eapply sd_traces; eapply Asm.semantics_determinate.
    + apply atomic_receptive; apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
Qed.
End USER_TEST_PASS.
Lemma identical_clight_forward (p : Clight.program) :
  forward_simulation (Clight.semantics2 p) (Clight.semantics2 p).
Proof.
  apply forward_simulation_step with (match_states := @eq Clight.state).
  - reflexivity.
  - intros s INIT; exists s; split; [exact INIT|reflexivity].
  - intros s target result SAME FINAL; subst target; exact FINAL.
  - intros s events next STEP target SAME; subst target; exists next; split; [exact STEP|reflexivity].
Qed.
Definition compile_readonly_tests choose := compile_readonly_tests_after choose (fun p => p).
Theorem compile_readonly_tests_correct choose p target : compile_readonly_tests choose p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof.
  apply compile_readonly_tests_after_correct; intro program; apply identical_clight_forward.
Qed.
Print Assumptions readonly_test_selection_sound.
Print Assumptions compile_readonly_tests_correct.

Print Assumptions compile_readonly_tests_after_correct.
