From compcert.lib Require Import Coqlib.
From compcert.common Require Import Errors AST Smallstep Behaviors.
From compcert.cfrontend Require Import Clight Csyntax Csem Cstrategy SimplExpr
  SimplExprproof SimplLocals SimplLocalsproof Cshmgen Cshmgenproof Cminorgen Cminorgenproof.
From compcert.backend Require Import Cminor RTL.
From compcert.driver Require Import Compiler Complements.
From Guard Require Import ClightGuard ClightGuardProof ClightNoWrap.
From Guard Require Import ClightExprRewrite ClightExprRewriteProof CommonRewrites.

(** The unchanged CompCert backend, factored out of its driver proof.  These
    lemmas reuse the upstream pass theorems rather than assuming a backend. *)
Lemma rtl_backend_correct : forall p tp,
  Compiler.transf_rtl_program p = OK tp ->
  forward_simulation (RTL.semantics p) (Asm.semantics tp).
Proof.
  intros p tp T.
  unfold Compiler.transf_rtl_program, Compiler.time in T.
  rewrite ! Compiler.compose_print_identity in T. simpl in T.
  set (p1 := Compiler.total_if Compopts.optim_tailcalls Tailcall.transf_program p) in *.
  destruct (Inlining.transf_program p1) as [p2|err] eqn:P2; simpl in T; try discriminate.
  set (p3 := Renumber.transf_program p2) in *.
  set (p4 := Compiler.total_if Compopts.optim_constprop Constprop.transf_program p3) in *.
  set (p5 := Compiler.total_if Compopts.optim_constprop Renumber.transf_program p4) in *.
  destruct (Compiler.partial_if Compopts.optim_CSE CSE.transf_program p5)
    as [p6|err] eqn:P6; simpl in T; try discriminate.
  destruct (Compiler.partial_if Compopts.optim_redundancy Deadcode.transf_program p6)
    as [p7|err] eqn:P7; simpl in T; try discriminate.
  destruct (Unusedglob.transform_program p7) as [p8|err] eqn:P8; simpl in T; try discriminate.
  destruct (Allocation.transf_program p8) as [p9|err] eqn:P9; simpl in T; try discriminate.
  set (p10 := Tunneling.tunnel_program p9) in *.
  destruct (Linearize.transf_program p10) as [p11|err] eqn:P11; simpl in T; try discriminate.
  set (p12 := CleanupLabels.transf_program p11) in *.
  destruct (Compiler.partial_if Compopts.debug Debugvar.transf_program p12)
    as [p13|err] eqn:P13; simpl in T; try discriminate.
  destruct (Stacking.transf_program p13) as [p14|err] eqn:P14; simpl in T; try discriminate.
  eapply compose_forward_simulations.
  { eapply Compiler.match_if_simulation.
    - apply Compiler.total_if_match. apply Tailcallproof.transf_program_match.
    - exact Tailcallproof.transf_program_correct. }
  eapply compose_forward_simulations.
  { eapply Inliningproof.transf_program_correct; eauto using Inliningproof.transf_program_match. }
  eapply compose_forward_simulations.
  { apply Renumberproof.transf_program_correct. apply Renumberproof.transf_program_match. }
  eapply compose_forward_simulations.
  { eapply Compiler.match_if_simulation.
    - apply Compiler.total_if_match. apply Constpropproof.transf_program_match.
    - exact Constpropproof.transf_program_correct. }
  eapply compose_forward_simulations.
  { eapply Compiler.match_if_simulation.
    - apply Compiler.total_if_match. apply Renumberproof.transf_program_match.
    - exact Renumberproof.transf_program_correct. }
  eapply compose_forward_simulations.
  { eapply Compiler.match_if_simulation.
    - eapply Compiler.partial_if_match; [exact CSEproof.transf_program_match|exact P6].
    - exact CSEproof.transf_program_correct. }
  eapply compose_forward_simulations.
  { eapply Compiler.match_if_simulation.
    - eapply Compiler.partial_if_match; [exact Deadcodeproof.transf_program_match|exact P7].
    - exact Deadcodeproof.transf_program_correct. }
  eapply compose_forward_simulations.
  { eapply Unusedglobproof.transf_program_correct; eauto using Unusedglobproof.transf_program_match. }
  eapply compose_forward_simulations.
  { eapply Allocproof.transf_program_correct; eauto using Allocproof.transf_program_match. }
  eapply compose_forward_simulations.
  { apply Tunnelingproof.transf_program_correct. apply Tunnelingproof.transf_program_match. }
  eapply compose_forward_simulations.
  { eapply Linearizeproof.transf_program_correct; eauto using Linearizeproof.transf_program_match. }
  eapply compose_forward_simulations.
  { apply CleanupLabelsproof.transf_program_correct. apply CleanupLabelsproof.transf_program_match. }
  eapply compose_forward_simulations.
  { eapply Compiler.match_if_simulation.
    - eapply Compiler.partial_if_match; [exact Debugvarproof.transf_program_match|exact P13].
    - exact Debugvarproof.transf_program_correct. }
  eapply compose_forward_simulations.
  { eapply Stackingproof.transf_program_correct with
      (return_address_offset := Asmgenproof0.return_address_offset).
    - exact Asmgenproof.return_address_exists.
    - eauto using Stackingproof.transf_program_match. }
  eapply Asmgenproof.transf_program_correct; eauto using Asmgenproof.transf_program_match.
Qed.

Lemma cminor_backend_correct : forall p tp,
  Compiler.transf_cminor_program p = OK tp ->
  forward_simulation (Cminor.semantics p) (Asm.semantics tp).
Proof.
  intros p tp T. unfold Compiler.transf_cminor_program, Compiler.time in T.
  rewrite ! Compiler.compose_print_identity in T. simpl in T.
  destruct (Selection.sel_program p) as [p1|err] eqn:P1; simpl in T; try discriminate.
  destruct (RTLgen.transl_program p1) as [p2|err] eqn:P2; simpl in T; try discriminate.
  eapply compose_forward_simulations.
  { eapply Selectionproof.transf_program_correct; eauto using Selectionproof.transf_program_match. }
  eapply compose_forward_simulations.
  { eapply RTLgenproof.transf_program_correct; eauto using RTLgenproof.transf_program_match. }
  eapply rtl_backend_correct; eauto.
Qed.

Definition compile_clight_tail (p : Clight.program) : res Asm.program :=
  match Cshmgen.transl_program p with
  | Error err => Error err
  | OK p1 => match Cminorgen.transl_program p1 with
             | Error err => Error err
             | OK p2 => Compiler.transf_cminor_program p2
             end
  end.

Lemma clight_tail_correct : forall p tp,
  compile_clight_tail p = OK tp ->
  forward_simulation (Clight.semantics2 p) (Asm.semantics tp).
Proof.
  intros p tp T; unfold compile_clight_tail in T.
  destruct (Cshmgen.transl_program p) as [p1|err] eqn:P1; try discriminate.
  destruct (Cminorgen.transl_program p1) as [p2|err] eqn:P2; try discriminate.
  eapply compose_forward_simulations.
  { eapply Cshmgenproof.transl_program_correct; eauto using Cshmgenproof.transf_program_match. }
  eapply compose_forward_simulations.
  { eapply Cminorgenproof.transl_program_correct; eauto using Cminorgenproof.transf_program_match. }
  eapply cminor_backend_correct; eauto.
Qed.

(** A real compiler function.  SimplLocals exposes non-address-taken scalar
    locals as temporaries; the generic guarded pass then runs on semantics2. *)
Definition compile_with_guards (select : Clight.expr -> option Clight.expr)
  (p : Csyntax.program) : res Asm.program :=
  match SimplExpr.transl_program p with
  | Error err => Error err
  | OK p1 => match SimplLocals.transf_program p1 with
             | Error err => Error err
             | OK p2 => compile_clight_tail
                 (Compiler.print Compiler.print_Clight (ClightGuard.transform_program select p2))
             end
  end.

Section COMPILER_CORRECTNESS.
Variable select : Clight.expr -> option Clight.expr.
Hypothesis SELECT_SOUND : forall a g, select a = Some g -> guard_contract a g.

Theorem guarded_cstrategy_forward : forall p tp,
  compile_with_guards select p = OK tp ->
  forward_simulation (Cstrategy.semantics p) (Asm.semantics tp).
Proof.
  intros p tp T; unfold compile_with_guards in T.
  destruct (SimplExpr.transl_program p) as [p1|err] eqn:P1; try discriminate.
  destruct (SimplLocals.transf_program p1) as [p2|err] eqn:P2; try discriminate.
  rewrite Compiler.print_identity in T.
  eapply compose_forward_simulations.
  { eapply SimplExprproof.transl_program_correct; eauto using SimplExprproof.transf_program_match. }
  eapply compose_forward_simulations.
  { eapply SimplLocalsproof.transf_program_correct; eauto using SimplLocalsproof.match_transf_program. }
  eapply compose_forward_simulations.
  { apply ClightGuardProof.transform_program_correct2; exact SELECT_SOUND. }
  eapply clight_tail_correct; eauto.
Qed.

Theorem compile_with_guards_correct : forall p tp,
  compile_with_guards select p = OK tp ->
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
      * eapply guarded_cstrategy_forward; eauto.
      * eapply sd_traces; eapply Asm.semantics_determinate.
    + apply atomic_receptive. apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
Qed.

Theorem compile_with_guards_preserves_spec : forall p tp spec,
  compile_with_guards select p = OK tp ->
  safety_enforcing_specification spec ->
  c_program_satisfies_spec p spec -> asm_program_satisfies_spec tp spec.
Proof.
  intros p tp spec T SAFE SOURCE beh TARGET.
  destruct (backward_simulation_behavior_improves
    (compile_with_guards_correct _ _ T) TARGET) as [src [EXEC IMPROVES]].
  specialize (SOURCE _ EXEC). destruct IMPROVES as [EQ|[t [WRONG PREFIX]]].
  - congruence.
  - subst src. exfalso. apply (SAFE _ SOURCE).
Qed.
End COMPILER_CORRECTNESS.

Definition compile_no_wrap := compile_with_guards select_no_wrap.

Corollary compile_no_wrap_correct : forall p tp,
  compile_no_wrap p = OK tp ->
  backward_simulation (Csem.semantics p) (Asm.semantics tp).
Proof. apply compile_with_guards_correct. apply select_no_wrap_sound. Qed.

Print Assumptions Compiler.transf_c_program_correct.
Print Assumptions compile_no_wrap_correct.

(** Branch and expression plugins compose at the same post-SimplLocals point.
    The selector soundness hypotheses are discharged when a concrete compiler
    is defined; they are not runtime or source-program assumptions. *)
Definition compile_with_rewrites
  (branches : Clight.expr -> option Clight.expr)
  (expressions : Clight.expr -> option (Clight.expr * Clight.expr))
  (p : Csyntax.program) : res Asm.program :=
  match SimplExpr.transl_program p with
  | Error err => Error err
  | OK p1 => match SimplLocals.transf_program p1 with
             | Error err => Error err
             | OK p2 => compile_clight_tail
                 (Compiler.print Compiler.print_Clight
                   (ClightExprRewrite.transform_program expressions
                     (ClightGuard.transform_program branches p2)))
             end
  end.

Section REWRITE_COMPILER.
Variable branches : Clight.expr -> option Clight.expr.
Variable expressions : Clight.expr -> option (Clight.expr * Clight.expr).
Hypothesis BRANCH_SOUND : forall a g, branches a = Some g -> guard_contract a g.
Hypothesis EXPRESSION_SOUND : forall a g c,
  expressions a = Some (g, c) -> expression_contract a g c.

Theorem rewrite_cstrategy_forward : forall p tp,
  compile_with_rewrites branches expressions p = OK tp ->
  forward_simulation (Cstrategy.semantics p) (Asm.semantics tp).
Proof.
  intros p tp T; unfold compile_with_rewrites in T.
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
  { apply ClightExprRewriteProof.transform_program_correct2; exact EXPRESSION_SOUND. }
  eapply clight_tail_correct; eauto.
Qed.

Theorem compile_with_rewrites_correct : forall p tp,
  compile_with_rewrites branches expressions p = OK tp ->
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
      * eapply rewrite_cstrategy_forward; eauto.
      * eapply sd_traces; eapply Asm.semantics_determinate.
    + apply atomic_receptive. apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
Qed.

Theorem compile_with_rewrites_preserves_spec : forall p tp spec,
  compile_with_rewrites branches expressions p = OK tp ->
  safety_enforcing_specification spec ->
  c_program_satisfies_spec p spec -> asm_program_satisfies_spec tp spec.
Proof.
  intros p tp spec T SAFE SOURCE beh TARGET.
  destruct (backward_simulation_behavior_improves
    (compile_with_rewrites_correct _ _ T) TARGET) as [src [EXEC IMPROVES]].
  specialize (SOURCE _ EXEC). destruct IMPROVES as [EQ|[t [WRONG PREFIX]]].
  - congruence.
  - subst src. exfalso. apply (SAFE _ SOURCE).
Qed.
End REWRITE_COMPILER.

Definition compile_common_rewrites := compile_with_rewrites select_no_wrap select_common.

Corollary compile_common_rewrites_correct : forall p tp,
  compile_common_rewrites p = OK tp ->
  backward_simulation (Csem.semantics p) (Asm.semantics tp).
Proof.
  apply compile_with_rewrites_correct; auto using select_no_wrap_sound, select_common_sound.
Qed.

Corollary compile_common_rewrites_preserves_spec : forall p tp spec,
  compile_common_rewrites p = OK tp ->
  safety_enforcing_specification spec ->
  c_program_satisfies_spec p spec -> asm_program_satisfies_spec tp spec.
Proof.
  apply compile_with_rewrites_preserves_spec; auto using select_no_wrap_sound, select_common_sound.
Qed.

Print Assumptions compile_common_rewrites_correct.
