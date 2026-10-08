(** The joint leaf check runs at the actual private row/column cursor state.
    It reads addresses only, not RHS data from future source stores. *)
From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint.
From GuardInterface Require Import ClightWordArithmeticTransport ClightWordCoordinateRename
  ClightDirectWordObservation ClightAffineJointObservation ClightLoadedBoundSyntax ClightLoadedOffsetHeader
  ClightWordStoreSequence ClightWordStoreSequenceFactory ClightWordStoreSequenceLoaded
  ClightWordStoreSequenceRuntime ClightWordStoreNestedPrefix.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition word_store_nested_point_code rename sites pointer child_pointer flag :=
  tree_statement (word_store_nested_probe rename sites pointer child_pointer)
    (Sset flag (Econst_int Int.one type_int32s)) (Sset flag (Econst_int Int.zero type_int32s)).

Section RUNTIME.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variables row cache pointer column child_cache child_pointer row_cursor column_cursor : ident.
Variables delta child_delta : int.
Variable body : statement.
Variable checked : checked_word_store_body body.
Variable stable : list ident.
Variable rename : ident -> ident.
Hypotheses (POINTER_STABLE : In pointer stable) (CHILD_POINTER_STABLE : In child_pointer stable)
  (CACHE_STABLE : In cache stable) (CHILD_CACHE_STABLE : In child_cache stable)
  (ROW_PRIVATE : ~In row stable) (COLUMN_PRIVATE : ~In column stable) (ROW_COLUMN : row<>column)
  (ROW_CURSOR_PRIVATE : ~In row_cursor stable) (COLUMN_CURSOR_PRIVATE : ~In column_cursor stable)
  (CURSORS_DISTINCT : row_cursor<>column_cursor)
  (RENAME_ROW : rename row=row_cursor) (RENAME_COLUMN : rename column=column_cursor).
Hypothesis RENAME_STABLE : forall id, In id stable -> rename id=id.
Hypothesis SITE_POINTERS : forall site, In site (wsbody_sites checked) -> In (wss_pointer site) stable.
Hypothesis SITE_INDICES : forall site, In site (wsbody_sites checked) ->
  expression_scope (row::column::stable) (wss_index site).
Let sites := wsbody_sites checked.
Let ready := word_store_nested_ready pointer delta cache child_pointer child_delta child_cache.
Let inner i j entry := word_store_nested_inner_prefix fe row cache pointer delta column child_cache child_pointer
  child_delta body stable i j entry.
Let point i j entry := word_store_nested_point_result row_cursor column_cursor rename sites pointer child_pointer i j entry.

Lemma word_store_nested_runtime_read_scope entry :
  ready entry -> incl (word_store_sequence_probe_reads rename sites
    (word_store_nested_observers pointer child_pointer entry)) (row_cursor::column_cursor::stable).
Proof.
  intros READY identifier MEMBER; unfold word_store_sequence_probe_reads in MEMBER;
    apply in_app_or in MEMBER; destruct MEMBER as [SITE|OBSERVER].
  - unfold word_store_sequence_address_reads in SITE; apply in_flat_map in SITE as [site [SITE READ]].
    destruct READ as [SAME|INDEX].
    + subst identifier; right; right; apply SITE_POINTERS; exact SITE.
    + assert (WORD : word_arithmetic (wss_index site)).
      { pose proof (wsbody_words checked) as WORDS; rewrite Forall_forall in WORDS; apply WORDS; exact SITE. }
      rewrite word_rename_temps in INDEX by exact WORD.
      apply in_map_iff in INDEX as [original [SAME READ]]; subst identifier.
      destruct (SITE_INDICES site SITE original READ) as [ROW|[COLUMN|STABLE]].
      * subst original; rewrite RENAME_ROW; left; reflexivity.
      * subst original; rewrite RENAME_COLUMN; right; left; reflexivity.
      * rewrite RENAME_STABLE by exact STABLE; right; right; exact STABLE.
  - apply in_flat_map in OBSERVER as [observer [OBSERVER READ]]; right; right.
    eapply word_store_nested_observer_scope; [exact POINTER_STABLE|exact CHILD_POINTER_STABLE|exact READY|exact OBSERVER|exact READ].
Qed.

Lemma word_store_nested_runtime_frame i j entry current :
  ready entry -> current!row_cursor=Some(Vint(Int.repr i)) -> current!column_cursor=Some(Vint(Int.repr j)) ->
  temp_agree stable (entry_temps entry) current ->
  temp_agree (word_store_sequence_probe_reads rename sites (word_store_nested_observers pointer child_pointer entry))
    (entry_temps(word_store_nested_check_entry row_cursor column_cursor i j entry)) current.
Proof.
  intros READY ROW COLUMN FRAME identifier MEMBER.
  destruct (word_store_nested_runtime_read_scope READY identifier MEMBER) as [SAME|[SAME|STABLE]].
  - subst identifier; cbn [word_store_nested_check_entry entry_temps];
      rewrite PTree.gso by exact CURSORS_DISTINCT; rewrite PTree.gss; exact ROW.
  - subst identifier; cbn [word_store_nested_check_entry entry_temps]; rewrite PTree.gss; exact COLUMN.
  - change (In identifier stable) in STABLE; cbn [word_store_nested_check_entry entry_temps];
      rewrite !PTree.gso by (intro SAME; first [apply ROW_CURSOR_PRIVATE|apply COLUMN_CURSOR_PRIVATE]; congruence).
    apply FRAME; exact STABLE.
Qed.

Theorem word_store_nested_point_runtime i j entry current flag :
  inner i j entry -> j<Int.signed(ClightNoWrap.temp_word child_cache(entry_temps entry)) ->
  current!row_cursor=Some(Vint(Int.repr i)) -> current!column_cursor=Some(Vint(Int.repr j)) ->
  temp_agree stable (entry_temps entry) current ->
  exec_stmt fe(entry_ge entry)(entry_env entry) current(entry_memory entry)
    (word_store_nested_point_code rename sites pointer child_pointer flag) E0
    (PTree.set flag (Vint(if point i j entry then Int.one else Int.zero)) current) (entry_memory entry) Out_normal.
Proof.
  intros PREFIX ACTIVE ROW COLUMN FRAME; pose proof PREFIX as [READY REST].
  assert (DOMAIN : word_store_sequence_domain fe rename sites (word_store_nested_observers pointer child_pointer entry)
    (word_store_nested_check_entry row_cursor column_cursor i j entry)).
  { eapply word_store_nested_point_domain with (checked:=checked) (stable:=stable)
      (row:=row) (cache:=cache) (column:=column) (child_cache:=child_cache) (delta:=delta) (child_delta:=child_delta);
      try eassumption. }
  pose proof (@word_store_sequence_runtime_check fe rename sites (word_store_nested_observers pointer child_pointer entry)
    (entry_ge entry) (entry_env entry) (entry_temps(word_store_nested_check_entry row_cursor column_cursor i j entry))
    current (entry_memory entry) flag (wsbody_words checked) DOMAIN
    (word_store_nested_runtime_frame READY ROW COLUMN FRAME)) as RUN.
  unfold word_store_sequence_check_code in RUN; rewrite (word_store_nested_probe_static rename sites READY) in RUN; exact RUN.
Qed.
End RUNTIME.

Print Assumptions word_store_nested_runtime_read_scope.
Print Assumptions word_store_nested_runtime_frame.
Print Assumptions word_store_nested_point_runtime.
