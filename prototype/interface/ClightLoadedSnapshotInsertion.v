From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightTempFrame ClightTempFootprint
  ClightPrivateRegion ClightProjectedExecution ClightStraightLine.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightAffineLoadedBoundTransport
  ClightStrictLoopProgress ClightCheckPlanFrame ClightSourceObservation ClightPrivateScan ClightSequenceContracts.
Import ListNotations.
Set Implicit Arguments.

(** A language-host bridge for a private preparation step. The checked
    intermediate source is scoped with extra private temporaries; installation
    exposes only the original public scope. A source execution is transported
    to the actual entry before preparation, so private initial values need not
    agree and no intermediate-source progress premise is assumed. *)
Theorem private_source_preparation_contract live extra source prepared target :
  check_plan_frameable source = true ->
  (statement_scope live source -> statement_scope (extra++live) prepared) ->
  (forall fe ge locals temps memory after final,
    exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
    exists prepared_after, exec_stmt fe ge locals temps memory prepared E0 prepared_after final Out_normal /\
      temp_agree live after prepared_after) ->
  PrivateRegion.projected_region_contract (extra++live) prepared target ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  intros FRAMEABLE SCOPE_PREP PREPARE CONTRACT temps p locals entry current memory after final SCOPE AGREE SOURCE fn continuation.
  destruct (@structured_execution_temp_transport (adapter_entry temps) (globalenv p) locals entry memory source
    E0 after final Out_normal SOURCE live current (statement_temps source)
    (@check_plan_frameable_writes source FRAMEABLE) SCOPE AGREE) as [middle [ACTUAL PUBLIC]].
  destruct (PREPARE _ _ _ _ _ _ _ ACTUAL) as [prepared_after [PREPARED PREPARED_PUBLIC]].
  destruct (CONTRACT _ _ _ _ _ _ _ _ (SCOPE_PREP SCOPE) (temp_agree_refl _ _) PREPARED fn continuation)
    as [exit [result [STEPS [EXIT MEMORY]]]].
  exists exit,result; split; [exact STEPS|split; [|exact MEMORY]].
  eapply temp_agree_trans; [exact PUBLIC|].
  eapply temp_agree_trans; [exact PREPARED_PUBLIC|].
  eapply temp_agree_weaken; [intros id IN; apply in_or_app; right; exact IN|exact EXIT].
Qed.

Definition loaded_snapshot_original loads row pointer body suffix :=
  Ssequence (source_load_prefix loads) (Ssequence (loaded_bound_loop row pointer body) suffix).
Definition loaded_snapshot_prepared loads row pointer body suffix cache :=
  Ssequence (source_load_prefix loads)
    (Ssequence (Sset cache (signed_load pointer)) (Ssequence (loaded_bound_loop row pointer body) suffix)).

(** The first real header supplies this receipt even on a zero-trip source.
    Future stores may change the cell; no stability or candidate premise is
    needed to make the extra nonvolatile read safe at this exact position. *)
Lemma loaded_header_snapshot_read fe ge locals temps memory row pointer body trace after final outcome :
  exec_stmt fe ge locals temps memory (loaded_bound_loop row pointer body) trace after final outcome ->
  exists word, eval_expr ge locals temps memory (signed_load pointer) (Vint word).
Proof.
  intro SOURCE; destruct (loaded_bound_completed_header SOURCE) as [flag HEADER].
  destruct (loaded_bound_test_facts HEADER) as [row_word [word [block [offset [ROW [POINTER [READ _]]]]]]].
  exists word; apply eval_Elvalue with (loc:=block) (ofs:=offset) (bf:=Full).
  - apply eval_Ederef,eval_Etempvar; exact POINTER.
  - apply deref_loc_value with (chunk:=Mint32); [reflexivity|exact READ].
Qed.

Lemma loaded_snapshot_pointer_scope live loads row pointer body suffix :
  statement_scope live (loaded_snapshot_original loads row pointer body suffix) -> In pointer live.
Proof.
  intro SCOPE; apply SCOPE; unfold loaded_snapshot_original,loaded_bound_loop,strict_frontend_loop,
    loaded_bound_test,signed_load,signed_pointer_temp; cbn [statement_temps expression_temps].
  apply in_or_app; right; apply in_or_app; left; apply in_or_app; left;
    apply in_or_app; left; cbn; auto.
Qed.

Lemma loaded_snapshot_prepared_scope live loads row pointer body suffix cache :
  statement_scope live (loaded_snapshot_original loads row pointer body suffix) ->
  statement_scope ([cache]++live) (loaded_snapshot_prepared loads row pointer body suffix cache).
Proof.
  intro SCOPE; pose proof (loaded_snapshot_pointer_scope SCOPE) as POINTER.
  unfold statement_scope,loaded_snapshot_prepared,loaded_snapshot_original in *.
  cbn [statement_temps expression_temps signed_load signed_pointer_temp].
  intros id IN; repeat rewrite in_app_iff in IN; cbn in IN |- *.
  destruct IN as [PREFIX|[[CACHE|[ADDRESS|[]]]|TAIL]]; [right; apply SCOPE,in_or_app; left; exact PREFIX|
    left; exact CACHE|right; subst id; exact POINTER|right; apply SCOPE,in_or_app; right; cbn; rewrite in_app_iff; tauto].
Qed.

Theorem loaded_snapshot_insertion_execution live loads row pointer body suffix cache fe ge locals temps memory after final :
  check_plan_frameable (Ssequence (loaded_bound_loop row pointer body) suffix) = true ->
  ~ In cache (statement_temps (loaded_snapshot_original loads row pointer body suffix)++live) ->
  exec_stmt fe ge locals temps memory (loaded_snapshot_original loads row pointer body suffix) E0 after final Out_normal ->
  exists prepared_after,
    exec_stmt fe ge locals temps memory (loaded_snapshot_prepared loads row pointer body suffix cache)
      E0 prepared_after final Out_normal /\ temp_agree live after prepared_after.
Proof.
  intros FRAMEABLE PRIVATE SOURCE; unfold loaded_snapshot_original in SOURCE; inversion SOURCE; subst; [|contradiction].
  match goal with RUN : exec_stmt _ _ _ _ _ (source_load_prefix loads) _ _ _ _ |- _ =>
    destruct (@private_scan_completed_shape _ _ _ _ _ _ _ _ _ _ RUN (source_load_prefix_supported loads))
      as [TRACE [MEMORY _]]; subst; rename RUN into PREFIX end.
  match goal with EMPTY : E0 ** _ = E0 |- _ => cbn in EMPTY; subst end.
  match goal with RUN : exec_stmt _ _ _ _ _ (Ssequence (loaded_bound_loop row pointer body) suffix) _ _ _ _ |- _ =>
    pose proof RUN as TAIL; inversion RUN; subst; [|contradiction] end.
  match goal with EMPTY : _ ** _ = E0 |- _ =>
    apply Eapp_E0_inv in EMPTY as [LEFT RIGHT]; subst end.
  match goal with RUN : exec_stmt _ _ _ _ _ (loaded_bound_loop row pointer body) _ _ _ _ |- _ =>
    destruct (loaded_header_snapshot_read RUN) as [word READ] end.
  assert (TAIL_PRIVATE : ~ In cache (statement_temps (Ssequence (loaded_bound_loop row pointer body) suffix)++live)).
  { change (~ In cache ((statement_temps (source_load_prefix loads)++
      statement_temps (Ssequence (loaded_bound_loop row pointer body) suffix))++live)) in PRIVATE.
    intro IN; apply PRIVATE; apply in_app_or in IN as [TAIL_IN|LIVE_IN].
    - apply in_or_app; left; apply in_or_app; right; exact TAIL_IN.
    - apply in_or_app; right; exact LIVE_IN. }
  match type of READ with eval_expr _ _ ?entry _ _ _ =>
    destruct (@structured_execution_temp_transport fe ge locals entry memory
      (Ssequence (loaded_bound_loop row pointer body) suffix) E0 after final Out_normal TAIL
      (statement_temps (Ssequence (loaded_bound_loop row pointer body) suffix)++live)
      (PTree.set cache (Vint word) entry)
      (statement_temps (Ssequence (loaded_bound_loop row pointer body) suffix))
      (@check_plan_frameable_writes _ FRAMEABLE)
      ltac:(unfold statement_scope; intros id IN; apply in_or_app; left; exact IN)
      (@temp_agree_set _ entry cache (Vint word) TAIL_PRIVATE)) as [prepared_after [PREPARED PUBLIC]] end.
  exists prepared_after; split.
  - unfold loaded_snapshot_prepared; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [exact PREFIX|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [constructor; exact READ|exact PREPARED].
  - eapply temp_agree_weaken; [intros id IN; apply in_or_app; right; exact IN|exact PUBLIC].
Qed.

Theorem loaded_snapshot_insertion_contract live loads row pointer body suffix cache target :
  check_plan_frameable (loaded_snapshot_original loads row pointer body suffix) = true ->
  ~ In cache (statement_temps (loaded_snapshot_original loads row pointer body suffix)++live) ->
  PrivateRegion.projected_region_contract ([cache]++live)
    (loaded_snapshot_prepared loads row pointer body suffix cache) target ->
  PrivateRegion.projected_region_contract live (loaded_snapshot_original loads row pointer body suffix) target.
Proof.
  intros FRAMEABLE PRIVATE CONTRACT; eapply private_source_preparation_contract; [exact FRAMEABLE| | |exact CONTRACT].
  - apply loaded_snapshot_prepared_scope.
  - intros; eapply loaded_snapshot_insertion_execution; [|exact PRIVATE|eassumption].
    unfold loaded_snapshot_original in FRAMEABLE; cbn [check_plan_frameable] in FRAMEABLE;
      apply andb_true_iff in FRAMEABLE; tauto.
Qed.

Print Assumptions private_source_preparation_contract.
Print Assumptions loaded_header_snapshot_read.
Print Assumptions loaded_snapshot_pointer_scope.
Print Assumptions loaded_snapshot_prepared_scope.
Print Assumptions loaded_snapshot_insertion_execution.
Print Assumptions loaded_snapshot_insertion_contract.
