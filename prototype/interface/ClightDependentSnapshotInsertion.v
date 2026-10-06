From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightPrivateRegion ClightProjectedExecution.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightDependentBoundSyntax
  ClightLoadedSnapshotInsertion ClightCheckPlanFrame ClightStrictLoopProgress.
Import ListNotations.
Set Implicit Arguments.

Definition dependent_snapshot_original prefix row root body suffix :=
  Ssequence prefix (Ssequence (dependent_bound_loop row root body) suffix).
Definition dependent_snapshot_prepared prefix row root body suffix pointer_cache bound_cache :=
  Ssequence prefix (Ssequence (Sset pointer_cache (dependent_pointer_load root))
    (Ssequence (Sset bound_cache (signed_load pointer_cache)) (Ssequence (dependent_bound_loop row root body) suffix))).

Lemma dependent_snapshot_root_scope live prefix row root body suffix :
  statement_scope live (dependent_snapshot_original prefix row root body suffix) -> In root live.
Proof.
  intro SCOPE; apply SCOPE.
  unfold dependent_snapshot_original,dependent_bound_loop,dependent_bound_test,dependent_signed_load,
    dependent_pointer_load,signed_pointer_cell_temp,strict_frontend_loop.
  cbn [statement_temps expression_temps]; apply in_or_app; right; apply in_or_app; left;
    apply in_or_app; left; apply in_or_app; left; cbn; auto.
Qed.

Lemma dependent_snapshot_prepared_scope live prefix row root body suffix pointer_cache bound_cache :
  statement_scope live (dependent_snapshot_original prefix row root body suffix) ->
  statement_scope ([pointer_cache;bound_cache]++live)
    (dependent_snapshot_prepared prefix row root body suffix pointer_cache bound_cache).
Proof.
  intro SCOPE; pose proof (dependent_snapshot_root_scope SCOPE) as ROOT.
  unfold statement_scope,dependent_snapshot_prepared,dependent_snapshot_original in *.
  cbn [statement_temps expression_temps dependent_pointer_load signed_pointer_cell_temp signed_load signed_pointer_temp].
  intros id IN; repeat rewrite in_app_iff in IN; cbn in IN |- *.
  destruct IN as [PREFIX|[[POINTER|[ADDRESS|[]]]|[[BOUND|[CACHE|[]]]|TAIL]]].
  - right; right; apply SCOPE,in_or_app; left; exact PREFIX.
  - left; exact POINTER.
  - right; right; subst id; exact ROOT.
  - right; left; exact BOUND.
  - left; exact CACHE.
  - right; right; apply SCOPE,in_or_app; right; cbn; rewrite in_app_iff; tauto.
Qed.

Lemma dependent_snapshot_tail_fresh live prefix row root body suffix identifier :
  ~ In identifier (statement_temps (dependent_snapshot_original prefix row root body suffix)++live) ->
  ~ In identifier (statement_temps (Ssequence (dependent_bound_loop row root body) suffix)++live).
Proof.
  unfold dependent_snapshot_original; cbn [statement_temps]; intros FRESH IN; apply FRESH.
  apply in_app_or in IN as [TAIL|PUBLIC].
  - apply in_or_app; left; apply in_or_app; right; exact TAIL.
  - apply in_or_app; right; exact PUBLIC.
Qed.

(** Both extra reads occur where the original header already reads both cells.
    Their order is explicit and the original compound header remains in the
    tail. This theorem does not establish either cell's future stability. *)
Theorem dependent_snapshot_insertion_execution live prefix row root body suffix pointer_cache bound_cache
  fe ge locals temps memory after final :
  check_plan_frameable (Ssequence (dependent_bound_loop row root body) suffix) = true ->
  ~ In pointer_cache (statement_temps (dependent_snapshot_original prefix row root body suffix)++live) ->
  ~ In bound_cache (statement_temps (dependent_snapshot_original prefix row root body suffix)++live) ->
  exec_stmt fe ge locals temps memory (dependent_snapshot_original prefix row root body suffix) E0 after final Out_normal ->
  exists prepared_after,
    exec_stmt fe ge locals temps memory (dependent_snapshot_prepared prefix row root body suffix pointer_cache bound_cache)
      E0 prepared_after final Out_normal /\ temp_agree live after prepared_after.
Proof.
  intros FRAMEABLE POINTER_PRIVATE BOUND_PRIVATE SOURCE.
  unfold dependent_snapshot_original in SOURCE; inversion SOURCE; subst; [|contradiction].
  match goal with EMPTY : _ ** _ = E0 |- _ => apply Eapp_E0_inv in EMPTY as [LEFT RIGHT]; subst end.
  match goal with RUN : exec_stmt _ _ _ _ _ (Ssequence (dependent_bound_loop row root body) suffix) _ _ _ _ |- _ =>
    pose proof RUN as TAIL; inversion RUN; subst; [|contradiction] end.
  match goal with EMPTY : _ ** _ = E0 |- _ => apply Eapp_E0_inv in EMPTY as [LEFT RIGHT]; subst end.
  match goal with RUN : exec_stmt _ _ _ _ _ (dependent_bound_loop row root body) _ _ _ _ |- _ =>
    destruct (dependent_bound_completed_header RUN) as [flag TEST];
    destruct (dependent_bound_test_facts TEST) as [counter [bound [block [offset [target [address
      [ROW [ROOT [POINTER [READ FLAG]]]]]]]]]] end.
  pose proof (@dependent_snapshot_tail_fresh live prefix row root body suffix pointer_cache POINTER_PRIVATE) as POINTER_FRESH.
  pose proof (@dependent_snapshot_tail_fresh live prefix row root body suffix bound_cache BOUND_PRIVATE) as BOUND_FRESH.
  match type of TAIL with exec_stmt _ _ _ ?entry ?at_memory _ _ _ _ _ =>
    assert (POINTER_EVAL : eval_expr ge locals entry at_memory (dependent_pointer_load root) (Vptr target address))
      by (eapply eval_Elvalue with (loc:=block) (ofs:=offset) (bf:=Full);
        [apply eval_Ederef,eval_Etempvar; exact ROOT|apply deref_loc_value with (chunk:=Mptr); [reflexivity|exact POINTER]]);
    assert (BOUND_EVAL : eval_expr ge locals (PTree.set pointer_cache (Vptr target address) entry) at_memory
      (signed_load pointer_cache) (Vint bound))
      by (eapply eval_Elvalue with (loc:=target) (ofs:=address) (bf:=Full);
        [apply eval_Ederef,eval_Etempvar,PTree.gss|apply deref_loc_value with (chunk:=Mint32); [reflexivity|exact READ]]);
    assert (FRAME : temp_agree (statement_temps (Ssequence (dependent_bound_loop row root body) suffix)++live)
      entry (PTree.set bound_cache (Vint bound) (PTree.set pointer_cache (Vptr target address) entry)))
      by (eapply temp_agree_trans; [apply temp_agree_set; exact POINTER_FRESH|apply temp_agree_set; exact BOUND_FRESH]);
    destruct (@structured_execution_temp_transport fe ge locals entry at_memory
      (Ssequence (dependent_bound_loop row root body) suffix) E0 after final Out_normal TAIL
      (statement_temps (Ssequence (dependent_bound_loop row root body) suffix)++live)
      (PTree.set bound_cache (Vint bound) (PTree.set pointer_cache (Vptr target address) entry))
      (statement_temps (Ssequence (dependent_bound_loop row root body) suffix))
      (@check_plan_frameable_writes _ FRAMEABLE)
      ltac:(unfold statement_scope; intros id IN; apply in_or_app; left; exact IN) FRAME)
      as [prepared_after [PREPARED PUBLIC]] end.
  exists prepared_after; split.
  - unfold dependent_snapshot_prepared; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [eassumption|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [constructor; exact POINTER_EVAL|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [constructor; exact BOUND_EVAL|exact PREPARED].
  - eapply temp_agree_weaken; [intros id IN; apply in_or_app; right; exact IN|exact PUBLIC].
Qed.

Theorem dependent_snapshot_insertion_contract live prefix row root body suffix pointer_cache bound_cache target :
  check_plan_frameable (dependent_snapshot_original prefix row root body suffix) = true ->
  ~ In pointer_cache (statement_temps (dependent_snapshot_original prefix row root body suffix)++live) ->
  ~ In bound_cache (statement_temps (dependent_snapshot_original prefix row root body suffix)++live) ->
  PrivateRegion.projected_region_contract ([pointer_cache;bound_cache]++live)
    (dependent_snapshot_prepared prefix row root body suffix pointer_cache bound_cache) target ->
  PrivateRegion.projected_region_contract live (dependent_snapshot_original prefix row root body suffix) target.
Proof.
  intros FRAMEABLE POINTER_PRIVATE BOUND_PRIVATE CONTRACT.
  eapply private_source_preparation_contract; [exact FRAMEABLE|apply dependent_snapshot_prepared_scope| |exact CONTRACT].
  intros; eapply dependent_snapshot_insertion_execution; [|exact POINTER_PRIVATE|exact BOUND_PRIVATE|eassumption].
  unfold dependent_snapshot_original in FRAMEABLE; cbn [check_plan_frameable] in FRAMEABLE;
    apply andb_true_iff in FRAMEABLE; tauto.
Qed.

Print Assumptions dependent_snapshot_root_scope.
Print Assumptions dependent_snapshot_prepared_scope.
Print Assumptions dependent_snapshot_insertion_execution.
Print Assumptions dependent_snapshot_insertion_contract.
