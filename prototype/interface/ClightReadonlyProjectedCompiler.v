From Stdlib Require Import List.
From compcert.common Require Import AST Values Memory Events Errors Smallstep.
From compcert.cfrontend Require Import Csyntax Csem Cstrategy
  SimplExpr SimplExprproof SimplLocals SimplLocalsproof Clight ClightBigstep.
From compcert.driver Require Import Compiler Complements.
From compcert.x86 Require Import Asm.
From Guard Require Import ClightGuard ClightCondition ClightRegionProgress ClightRegionRewrite
  ClightTempFrame ClightTempFootprint ClightProjectedExecution ClightPrivateRegion
  ClightPrivatePool CompCertMemoryEquivalence GuardCompiler.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite ClightRegionBoundary.
Import ListNotations.
Set Implicit Arguments.

(** These ports specify the observer only; an empty write set here is not a
    write-frame certificate. The caller separately supplies source scope and
    temp-write bounds. The host protects every original program temporary. *)
Definition public_exit_ports live :=
  {| region_inputs := live; region_stable := []; region_live_out := live;
     region_written := []; region_private := []; region_write_bytes := fun _ _ _ => False |}.

Record readonly_projected_clight_rule (live : list ident) (source : Clight.statement) := ReadonlyProjectedClightRule {
  projected_candidate : Clight.statement;
  projected_guard : decision_tree;
  projected_domain : clight_entry -> Prop;
  projected_premise : clight_entry -> Prop;
  projected_source_writes : list ident;
  projected_source_write_bound : writes_only projected_source_writes source;
  projected_rule_check : forall temps,
    readonly_condition (readonly_clight_host (adapter_entry temps) (boundary_observe (public_exit_ports live)))
      projected_domain projected_premise projected_guard;
  projected_rule_local : forall temps,
    conditional_equivalence (readonly_clight_host (adapter_entry temps) (boundary_observe (public_exit_ports live)))
      projected_domain projected_premise source projected_candidate;
  projected_rule_entry : forall temps (p : Clight.program) e le m le' m',
    exec_stmt (adapter_entry temps) (Clight.globalenv p) e le m source E0 le' m' Out_normal ->
    projected_domain (Entry (Clight.globalenv p) e le m)
}.

Definition projected_readonly_replacement {live source} (rule : readonly_projected_clight_rule live source) :=
  tree_statement (projected_guard rule) (projected_candidate rule) source.

Theorem projected_readonly_rule_region_contract live source
  (rule : readonly_projected_clight_rule live source) :
  PrivateRegion.projected_region_contract live source (projected_readonly_replacement rule).
Proof.
  intros temps p locals le target memory after final SCOPE AGREE SOURCE fn outside.
  destruct (@structured_execution_temp_transport (adapter_entry temps) (Clight.globalenv p)
    locals le memory source E0 after final Out_normal SOURCE live target
    (projected_source_writes rule) (projected_source_write_bound rule) SCOPE AGREE)
    as [source_exit [TRANSPORTED EXIT_AGREE]].
  pose proof (projected_rule_entry rule TRANSPORTED) as DOMAIN.
  destruct (readonly_available (projected_rule_check rule temps) _ DOMAIN) as
    [accepted [checked [CHECK SAME]]]; subst checked.
  assert (SELECTED : exists target_exit target_memory,
    clight_fragment_run (adapter_entry temps) (if accepted then projected_candidate rule else source)
      (Entry (Clight.globalenv p) locals target memory)
      (FragmentObservation E0 target_exit target_memory Out_normal) /\
    temp_agree live after target_exit /\ memory_equivalent final target_memory).
  { destruct accepted eqn:ACCEPT.
    - destruct (readonly_sound (projected_rule_check rule temps) _ _ _ DOMAIN (conj CHECK eq_refl))
        as [_ PREMISE].
      assert (VISIBLE_SOURCE : runs
        (readonly_clight_host (adapter_entry temps) (boundary_observe (public_exit_ports live)))
        source (Entry (Clight.globalenv p) locals target memory)
        (FragmentObservation E0 source_exit final Out_normal)).
      { exists (FragmentObservation E0 source_exit final Out_normal); split;
          [exact TRANSPORTED|apply boundary_observe_refl]. }
      apply (proj2 (@projected_rule_local live source rule temps _ _
        (conj DOMAIN (PREMISE eq_refl)))) in VISIBLE_SOURCE.
      destruct VISIBLE_SOURCE as [[trace target_exit target_memory out]
        [RUN [TRACE [OUTCOME [TEMPS MEMORY]]]]].
      cbn in TRACE, OUTCOME, TEMPS, MEMORY; subst trace out.
      exists target_exit, target_memory; split; [exact RUN|split].
      + eapply temp_agree_trans; [exact EXIT_AGREE|exact TEMPS].
      + exact MEMORY.
    - exists source_exit, final; split; [exact TRANSPORTED|split;
        [exact EXIT_AGREE|apply memory_equivalent_refl]]. }
  destruct SELECTED as [target_exit [target_memory [LEAF [TEMPS MEMORY]]]].
  assert (RUN : exec_stmt (adapter_entry temps) (Clight.globalenv p) locals target memory
    (projected_readonly_replacement rule) E0 target_exit target_memory Out_normal).
  { change (clight_fragment_run (adapter_entry temps)
      (tree_statement (projected_guard rule) (projected_candidate rule) source)
      (Entry (Clight.globalenv p) locals target memory)
      (FragmentObservation E0 target_exit target_memory Out_normal)).
    apply (proj2 (@readonly_tree_execution_exact (adapter_entry temps)
      (projected_guard rule) (projected_candidate rule) source
      (Entry (Clight.globalenv p) locals target memory)
      (FragmentObservation E0 target_exit target_memory Out_normal))).
    exists accepted; split; [exact CHECK|exact LEAF]. }
  destruct (exec_stmt_steps (adapter_entry temps) p _ _ _ _ _ _ _ _ RUN fn outside)
    as [next [STEPS EXIT]].
  inversion EXIT; subst next; exists target_exit, target_memory; auto.
Qed.

Section USER_PASS.
Variable choose : forall (live : list ident) (pool : list (ident * Ctypes.type)) source,
  option (readonly_projected_clight_rule live source).
Variable supported : Clight.statement -> bool.
Hypothesis SUPPORTED : forall source, supported source = true -> exists MODEL : region_progress source, True.
Variable private_count : nat.

Definition projected_readonly_selection live pool source : option Clight.statement :=
  match choose live pool source with
  | Some rule => Some (projected_readonly_replacement rule)
  | None => None end.

Lemma projected_readonly_selection_sound live pool source target :
  projected_readonly_selection live pool source = Some target ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  unfold projected_readonly_selection; destruct (choose live pool source) as [rule|]; [|discriminate].
  intro SAME; injection SAME as SAME; subst target; apply projected_readonly_rule_region_contract.
Qed.

Definition transform_projected_readonly (p : Clight.program) :=
  transform_private_program supported projected_readonly_selection
    (propose_private_names (program_temps p) private_count) p.

Theorem transform_projected_readonly_correct p :
  forward_simulation (Clight.semantics2 p) (Clight.semantics2 (transform_projected_readonly p)).
Proof.
  apply transform_private_program_correct; [exact SUPPORTED|apply projected_readonly_selection_sound].
Qed.

Definition compile_projected_readonly (p : Csyntax.program) : res Asm.program :=
  match SimplExpr.transl_program p with
  | Error err => Error err
  | OK p1 => match SimplLocals.transf_program p1 with
    | Error err => Error err
    | OK p2 => compile_clight_tail
        (Compiler.print Compiler.print_Clight (transform_projected_readonly p2)) end end.

Theorem projected_readonly_cstrategy_forward p target :
  compile_projected_readonly p = OK target ->
  forward_simulation (Cstrategy.semantics p) (Asm.semantics target).
Proof.
  unfold compile_projected_readonly; intro COMPILE.
  destruct (SimplExpr.transl_program p) as [p1|err] eqn:P1; try discriminate.
  destruct (SimplLocals.transf_program p1) as [p2|err] eqn:P2; try discriminate.
  rewrite Compiler.print_identity in COMPILE.
  eapply compose_forward_simulations.
  { eapply SimplExprproof.transl_program_correct; eauto using SimplExprproof.transf_program_match. }
  eapply compose_forward_simulations.
  { eapply SimplLocalsproof.transf_program_correct; eauto using SimplLocalsproof.match_transf_program. }
  eapply compose_forward_simulations.
  { apply transform_projected_readonly_correct. }
  eapply clight_tail_correct; exact COMPILE.
Qed.

Theorem compile_projected_readonly_correct p target :
  compile_projected_readonly p = OK target ->
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
      * eapply projected_readonly_cstrategy_forward; exact COMPILE.
      * eapply sd_traces; eapply Asm.semantics_determinate.
    + apply atomic_receptive; apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
Qed.
End USER_PASS.

Print Assumptions projected_readonly_rule_region_contract.
Print Assumptions projected_readonly_selection_sound.
Print Assumptions transform_projected_readonly_correct.
Print Assumptions compile_projected_readonly_correct.
