From compcert.common Require Import Errors Smallstep Behaviors.
From compcert.cfrontend Require Import Clight Csyntax Csem Cstrategy SimplExpr
  SimplExprproof SimplLocals SimplLocalsproof.
From compcert.driver Require Import Compiler Complements.
From Guard Require Import ClightGuard ClightGuardProof ClightNoWrap GuardCompiler
  ClightCondition ClightTreeRewrite ClightTreeRewriteProof ClightTreeExamples ClightSameAddress
  ClightSignedCancel ClightRegionRewrite ClightRegionRewriteProof ClightRedundantSet
  ClightAdaptiveRegion ClightAdaptiveRegionProof ClightRegionProgress ClightProgressClassifier
  ClightZeroTrip ClightFrontendRegion ClightStructuredProgress ClightMatrixSelector ClightPrivateRegion ClightPrivatePool ClightPrivateRule
  ClightTempFootprint ClightStripmineSelector RectangularCompiler.

Definition compile_with_private_regions
  (supported : Clight.statement -> bool)
  (private_regions : list AST.ident -> list (AST.ident * Ctypes.type) -> Clight.statement -> option Clight.statement)
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
                     (ClightGuard.transform_program branches (let p3 := AdaptiveRegion.transform_program supported regions p2 in
                       transform_private_program supported private_regions (propose_private_names (program_temps p3) 1) p3))))
             end
  end.

Section PRIVATE_REGION_COMPILER.
Variable supported : Clight.statement -> bool.
Variable private_regions : list AST.ident -> list (AST.ident * Ctypes.type) -> Clight.statement -> option Clight.statement.
Hypothesis PRIVATE_SOUND : forall live pool s ts, private_regions live pool s = Some ts ->
  PrivateRegion.projected_region_contract live s ts.
Hypothesis SUPPORTED_SOUND : forall s, supported s = true -> exists MODEL : region_progress s, True.
Variable branches : Clight.expr -> option Clight.expr.
Variable expressions : Clight.expr -> option (decision_tree * Clight.expr).
Variable regions : Clight.statement -> option Clight.statement.
Hypothesis BRANCH_SOUND : forall a g, branches a = Some g -> guard_contract a g.
Hypothesis REGION_SOUND : forall s ts, regions s = Some ts -> region_contract s ts.
Hypothesis EXPRESSION_SOUND : forall a g c,
  expressions a = Some (g, c) -> ClightTreeRewrite.expression_contract a g c.

Theorem private_region_cstrategy_forward : forall p tp,
  compile_with_private_regions supported private_regions branches expressions regions p = OK tp ->
  forward_simulation (Cstrategy.semantics p) (Asm.semantics tp).
Proof.
  intros p tp T; unfold compile_with_private_regions in T.
  destruct (SimplExpr.transl_program p) as [p1|err] eqn:P1; try discriminate.
  destruct (SimplLocals.transf_program p1) as [p2|err] eqn:P2; try discriminate.
  rewrite Compiler.print_identity in T.
  eapply compose_forward_simulations.
  { eapply SimplExprproof.transl_program_correct; eauto using SimplExprproof.transf_program_match. }
  eapply compose_forward_simulations.
  { eapply SimplLocalsproof.transf_program_correct; eauto using SimplLocalsproof.match_transf_program. }
  eapply compose_forward_simulations.
  { apply AdaptiveRegionProof.transform_program_correct2; [exact SUPPORTED_SOUND | exact REGION_SOUND]. }
  eapply compose_forward_simulations.
  { apply transform_private_program_correct; [exact SUPPORTED_SOUND|exact PRIVATE_SOUND]. }
  eapply compose_forward_simulations.
  { apply ClightGuardProof.transform_program_correct2; exact BRANCH_SOUND. }
  eapply compose_forward_simulations.
  { apply ClightTreeRewriteProof.transform_program_correct2; exact EXPRESSION_SOUND. }
  eapply clight_tail_correct; eauto.
Qed.

Theorem compile_with_private_regions_correct : forall p tp,
  compile_with_private_regions supported private_regions branches expressions regions p = OK tp ->
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
      * eapply private_region_cstrategy_forward; eauto.
      * eapply sd_traces; eapply Asm.semantics_determinate.
    + apply atomic_receptive. apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
Qed.

Theorem compile_with_private_regions_preserves_spec : forall p tp spec,
  compile_with_private_regions supported private_regions branches expressions regions p = OK tp ->
  safety_enforcing_specification spec ->
  c_program_satisfies_spec p spec -> asm_program_satisfies_spec tp spec.
Proof.
  intros p tp spec T SAFE SOURCE beh TARGET.
  destruct (backward_simulation_behavior_improves
    (compile_with_private_regions_correct _ _ T) TARGET) as [src [EXEC IMPROVES]].
  specialize (SOURCE _ EXEC). destruct IMPROVES as [EQ|[t [WRONG PREFIX]]].
  - congruence.
  - subst src. exfalso. apply (SAFE _ SOURCE).
Qed.
End PRIVATE_REGION_COMPILER.

Definition compile_stripmine_regions width := compile_with_private_regions structured_progress_supported
  (select_stripmine width) select_no_wrap select_signed_memory_rewrites select_rectangular_regions.
Corollary compile_stripmine_regions_correct : forall width p tp,
  compile_stripmine_regions width p = OK tp -> backward_simulation (Csem.semantics p) (Asm.semantics tp).
Proof.
  intro width; unfold compile_stripmine_regions; apply compile_with_private_regions_correct.
  - intros live pool source target SELECT; exact (@select_stripmine_sound width live pool source target SELECT).
  - exact structured_progress_supported_sound.
  - exact select_no_wrap_sound.
  - exact select_rectangular_regions_sound.
  - exact select_signed_memory_rewrites_sound.
Qed.
Corollary compile_stripmine_regions_preserves_spec : forall width p tp spec,
  compile_stripmine_regions width p = OK tp -> safety_enforcing_specification spec ->
  c_program_satisfies_spec p spec -> asm_program_satisfies_spec tp spec.
Proof.
  intro width; unfold compile_stripmine_regions; apply compile_with_private_regions_preserves_spec.
  - intros live pool source target SELECT; exact (@select_stripmine_sound width live pool source target SELECT).
  - exact structured_progress_supported_sound.
  - exact select_no_wrap_sound.
  - exact select_rectangular_regions_sound.
  - exact select_signed_memory_rewrites_sound.
Qed.
Print Assumptions Compiler.transf_c_program_correct.
Print Assumptions compile_stripmine_regions_correct.
