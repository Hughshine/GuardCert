From compcert.common Require Import Errors Smallstep Behaviors.
From compcert.cfrontend Require Import Clight Csyntax Csem Cstrategy SimplExpr
  SimplExprproof SimplLocals SimplLocalsproof.
From compcert.driver Require Import Compiler Complements.
From Guard Require Import ClightGuard ClightGuardProof ClightNoWrap GuardCompiler
  ClightCondition ClightTreeRewrite ClightTreeRewriteProof ClightTreeExamples.

Definition compile_with_trees
  (branches : Clight.expr -> option Clight.expr)
  (expressions : Clight.expr -> option (decision_tree * Clight.expr))
  (p : Csyntax.program) : res Asm.program :=
  match SimplExpr.transl_program p with
  | Error err => Error err
  | OK p1 => match SimplLocals.transf_program p1 with
             | Error err => Error err
             | OK p2 => compile_clight_tail
                 (Compiler.print Compiler.print_Clight
                   (ClightTreeRewrite.transform_program expressions
                     (ClightGuard.transform_program branches p2)))
             end
  end.

Section TREE_COMPILER.
Variable branches : Clight.expr -> option Clight.expr.
Variable expressions : Clight.expr -> option (decision_tree * Clight.expr).
Hypothesis BRANCH_SOUND : forall a g, branches a = Some g -> guard_contract a g.
Hypothesis EXPRESSION_SOUND : forall a g c,
  expressions a = Some (g, c) -> ClightTreeRewrite.expression_contract a g c.

Theorem tree_cstrategy_forward : forall p tp,
  compile_with_trees branches expressions p = OK tp ->
  forward_simulation (Cstrategy.semantics p) (Asm.semantics tp).
Proof.
  intros p tp T; unfold compile_with_trees in T.
  destruct (SimplExpr.transl_program p) as [p1|err] eqn:P1; try discriminate.
  destruct (SimplLocals.transf_program p1) as [p2|err] eqn:P2; try discriminate.
  rewrite Compiler.print_identity in T.
  eapply compose_forward_simulations.
  { eapply SimplExprproof.transl_program_correct; eauto using SimplExprproof.transf_program_match. }
  eapply compose_forward_simulations.
  { eapply SimplLocalsproof.transf_program_correct; eauto using SimplLocalsproof.match_transf_program. }
  eapply compose_forward_simulations.
  { apply ClightGuardProof.transform_program_correct2; exact BRANCH_SOUND. }
  eapply compose_forward_simulations.
  { apply ClightTreeRewriteProof.transform_program_correct2; exact EXPRESSION_SOUND. }
  eapply clight_tail_correct; eauto.
Qed.

Theorem compile_with_trees_correct : forall p tp,
  compile_with_trees branches expressions p = OK tp ->
  backward_simulation (Csem.semantics p) (Asm.semantics tp).
Proof.
  intros p tp T.
  apply compose_backward_simulation with (atomic (Cstrategy.semantics p)).
  - eapply sd_traces; eapply Asm.semantics_determinate.
  - apply factor_backward_simulation.
    + apply Cstrategy.strategy_simulation.
    + apply Csem.semantics_single_events.
    + eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.
  - apply forward_to_backward_simulation.
    + apply factor_forward_simulation.
      * eapply tree_cstrategy_forward; eauto.
      * eapply sd_traces; eapply Asm.semantics_determinate.
    + apply atomic_receptive. apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
Qed.

Theorem compile_with_trees_preserves_spec : forall p tp spec,
  compile_with_trees branches expressions p = OK tp ->
  safety_enforcing_specification spec ->
  c_program_satisfies_spec p spec -> asm_program_satisfies_spec tp spec.
Proof.
  intros p tp spec T SAFE SOURCE beh TARGET.
  destruct (backward_simulation_behavior_improves
    (compile_with_trees_correct _ _ T) TARGET) as [src [EXEC IMPROVES]].
  specialize (SOURCE _ EXEC). destruct IMPROVES as [EQ|[t [WRONG PREFIX]]].
  - congruence.
  - subst src. exfalso. apply (SAFE _ SOURCE).
Qed.
End TREE_COMPILER.


Definition compile_property_rewrites := compile_with_trees select_no_wrap select_tree_common.

Corollary compile_property_rewrites_correct : forall p tp,
  compile_property_rewrites p = OK tp ->
  backward_simulation (Csem.semantics p) (Asm.semantics tp).
Proof.
  apply compile_with_trees_correct; auto using select_no_wrap_sound, select_tree_common_sound.
Qed.

Corollary compile_property_rewrites_preserves_spec : forall p tp spec,
  compile_property_rewrites p = OK tp ->
  safety_enforcing_specification spec ->
  c_program_satisfies_spec p spec -> asm_program_satisfies_spec tp spec.
Proof.
  apply compile_with_trees_preserves_spec; auto using select_no_wrap_sound, select_tree_common_sound.
Qed.

Print Assumptions Compiler.transf_c_program_correct.
Print Assumptions compile_property_rewrites_correct.
