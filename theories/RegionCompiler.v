From compcert.common Require Import Errors Smallstep Behaviors.
From compcert.cfrontend Require Import Clight Csyntax Csem Cstrategy SimplExpr
  SimplExprproof SimplLocals SimplLocalsproof.
From compcert.driver Require Import Compiler Complements.
From Guard Require Import ClightGuard ClightGuardProof ClightNoWrap GuardCompiler
  ClightCondition ClightTreeRewrite ClightTreeRewriteProof ClightTreeExamples ClightSameAddress
  ClightSignedCancel ClightRegionRewrite ClightRegionRewriteProof ClightRedundantSet.

Definition compile_with_regions
  (branches : Clight.expr -> option Clight.expr)
  (expressions : Clight.expr -> option (decision_tree * Clight.expr))
  (regions : Clight.statement -> option Clight.statement)
  (p : Csyntax.program) : res Asm.program :=
  match SimplExpr.transl_program p with
  | Error err => Error err
  | OK p1 => match SimplLocals.transf_program p1 with
             | Error err => Error err
             | OK p2 => compile_clight_tail
                 (Compiler.print Compiler.print_Clight
                   (ClightTreeRewrite.transform_program expressions
                     (ClightGuard.transform_program branches (ClightRegionRewrite.transform_program regions p2))))
             end
  end.

Section REGION_COMPILER.
Variable branches : Clight.expr -> option Clight.expr.
Variable expressions : Clight.expr -> option (decision_tree * Clight.expr).
Variable regions : Clight.statement -> option Clight.statement.
Hypothesis BRANCH_SOUND : forall a g, branches a = Some g -> guard_contract a g.
Hypothesis REGION_SOUND : forall s ts, regions s = Some ts -> region_contract s ts.
Hypothesis EXPRESSION_SOUND : forall a g c,
  expressions a = Some (g, c) -> ClightTreeRewrite.expression_contract a g c.

Theorem region_cstrategy_forward : forall p tp,
  compile_with_regions branches expressions regions p = OK tp ->
  forward_simulation (Cstrategy.semantics p) (Asm.semantics tp).
Proof.
  intros p tp T; unfold compile_with_regions in T.
  destruct (SimplExpr.transl_program p) as [p1|err] eqn:P1; try discriminate.
  destruct (SimplLocals.transf_program p1) as [p2|err] eqn:P2; try discriminate.
  rewrite Compiler.print_identity in T.
  eapply compose_forward_simulations.
  { eapply SimplExprproof.transl_program_correct; eauto using SimplExprproof.transf_program_match. }
  eapply compose_forward_simulations.
  { eapply SimplLocalsproof.transf_program_correct; eauto using SimplLocalsproof.match_transf_program. }
  eapply compose_forward_simulations.
  { apply ClightRegionRewriteProof.transform_program_correct2; exact REGION_SOUND. }
  eapply compose_forward_simulations.
  { apply ClightGuardProof.transform_program_correct2; exact BRANCH_SOUND. }
  eapply compose_forward_simulations.
  { apply ClightTreeRewriteProof.transform_program_correct2; exact EXPRESSION_SOUND. }
  eapply clight_tail_correct; eauto.
Qed.

Theorem compile_with_regions_correct : forall p tp,
  compile_with_regions branches expressions regions p = OK tp ->
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
      * eapply region_cstrategy_forward; eauto.
      * eapply sd_traces; eapply Asm.semantics_determinate.
    + apply atomic_receptive. apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
Qed.

Theorem compile_with_regions_preserves_spec : forall p tp spec,
  compile_with_regions branches expressions regions p = OK tp ->
  safety_enforcing_specification spec ->
  c_program_satisfies_spec p spec -> asm_program_satisfies_spec tp spec.
Proof.
  intros p tp spec T SAFE SOURCE beh TARGET.
  destruct (backward_simulation_behavior_improves
    (compile_with_regions_correct _ _ T) TARGET) as [src [EXEC IMPROVES]].
  specialize (SOURCE _ EXEC). destruct IMPROVES as [EQ|[t [WRONG PREFIX]]].
  - congruence.
  - subst src. exfalso. apply (SAFE _ SOURCE).
Qed.
End REGION_COMPILER.


Definition compile_property_regions := compile_with_regions select_no_wrap select_signed_memory_rewrites select_redundant_set.

Corollary compile_property_regions_correct : forall p tp,
  compile_property_regions p = OK tp ->
  backward_simulation (Csem.semantics p) (Asm.semantics tp).
Proof.
  apply compile_with_regions_correct; auto using select_no_wrap_sound, select_signed_memory_rewrites_sound, select_redundant_set_sound.
Qed.

Corollary compile_property_regions_preserves_spec : forall p tp spec,
  compile_property_regions p = OK tp ->
  safety_enforcing_specification spec ->
  c_program_satisfies_spec p spec -> asm_program_satisfies_spec tp spec.
Proof.
  apply compile_with_regions_preserves_spec; auto using select_no_wrap_sound, select_signed_memory_rewrites_sound, select_redundant_set_sound.
Qed.

Print Assumptions Compiler.transf_c_program_correct.
Print Assumptions compile_property_regions_correct.
