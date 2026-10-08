(** Two loaded source axes and arbitrary checked assignment lists.
    Every leaf is licensed by the original nested execution. Joint header
    preservation is established before opening the next source prefix. *)
From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightNoWrap
  ClightRedundantSet ClightLoopSyntax ClightStraightLine ClightRegionProgress CompCertMemoryActions.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightLoadedOffsetHeader
  ClightNestedLoadedOffset ClightNestedExpressionCapture ClightNestedExpressionPrefix
  ClightExpressionBodyPrefix ClightObservedHeaderPrefix ClightWordArithmeticTransport
  ClightWordCoordinateRename ClightDirectWordObservation ClightAffineJointObservation
  ClightWordStoreSequence ClightWordStoreSequenceFactory ClightWordStoreSequenceLoaded
  ClightWordStoreSequenceRuntime ClightAnchoredExpressionPrefix ClightStorePermissions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition word_store_nested_ready pointer delta cache child_pointer child_delta child_cache entry :=
  loaded_offset_cached_header pointer delta cache entry /\
  loaded_offset_cached_header child_pointer child_delta child_cache entry.
Definition word_store_nested_observers pointer child_pointer entry :=
  word_store_loaded_observers pointer entry ++ word_store_loaded_observers child_pointer entry.
Definition word_store_nested_check_entry row_cursor column_cursor i j entry :=
  Entry (entry_ge entry) (entry_env entry)
    (PTree.set column_cursor (Vint (Int.repr j))
      (PTree.set row_cursor (Vint (Int.repr i)) (entry_temps entry))) (entry_memory entry).
Definition word_store_nested_probe rename sites pointer child_pointer :=
  word_store_sequence_tree rename sites
    [ClightWordObserver (signed_pointer_temp pointer) 1%positive Ptrofs.zero Vundef;
     ClightWordObserver (signed_pointer_temp child_pointer) 1%positive Ptrofs.zero Vundef].
Definition word_store_nested_point_result row_cursor column_cursor rename sites pointer child_pointer i j entry :=
  word_store_sequence_flag rename sites (word_store_nested_observers pointer child_pointer entry)
    (word_store_nested_check_entry row_cursor column_cursor i j entry).
Definition word_store_nested_outer_prefix fe row cache pointer delta column child_cache child_pointer child_delta
  body stable i entry :=
  expression_body_prefix fe row cache (signed_load_offset pointer delta)
    (nested_expression_body column (signed_load_offset child_pointer child_delta) body) stable
    (word_store_nested_ready pointer delta cache child_pointer child_delta child_cache)
    (nested_loaded_offset_observations pointer child_pointer) i entry.
Definition word_store_nested_inner_prefix fe row cache pointer delta column child_cache child_pointer child_delta
  body stable i j entry :=
  expression_body_prefix fe column child_cache (signed_load_offset child_pointer child_delta) body (row::stable)
    (fun _=>word_store_nested_ready pointer delta cache child_pointer child_delta child_cache entry)
    (fun _=>nested_loaded_offset_observations pointer child_pointer entry) j
    (nested_expression_inner_entry row column i entry).

Lemma word_store_nested_observers_receipt pointer delta cache child_pointer child_delta child_cache entry :
  word_store_nested_ready pointer delta cache child_pointer child_delta child_cache entry ->
  Forall (word_observer_receipt (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry))
    (word_store_nested_observers pointer child_pointer entry) /\
  map word_observer_snapshot (word_store_nested_observers pointer child_pointer entry) =
    nested_loaded_offset_observations pointer child_pointer entry.
Proof.
  intros [ROOT CHILD]; destruct (word_store_loaded_observers_receipt ROOT) as [ROOT_READ ROOT_SNAPSHOT];
    destruct (word_store_loaded_observers_receipt CHILD) as [CHILD_READ CHILD_SNAPSHOT].
  unfold word_store_nested_observers,nested_loaded_offset_observations; split.
  - apply Forall_app; split; assumption.
  - rewrite map_app,ROOT_SNAPSHOT,CHILD_SNAPSHOT; reflexivity.
Qed.
Lemma word_store_nested_probe_static rename sites pointer delta cache child_pointer child_delta child_cache entry :
  word_store_nested_ready pointer delta cache child_pointer child_delta child_cache entry ->
  word_store_sequence_tree rename sites (word_store_nested_observers pointer child_pointer entry) =
    word_store_nested_probe rename sites pointer child_pointer.
Proof.
  intros [[block [offset [raw [PTR [READ CACHE]]]]] [child_block [child_offset [child_raw [CPTR [CREAD CCACHE]]]]]].
  apply word_store_sequence_observer_addresses; unfold word_store_nested_observers,word_store_loaded_observers;
    rewrite PTR,READ,CPTR,CREAD; reflexivity.
Qed.

Section PREFIX.
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
Let observations := nested_loaded_offset_observations pointer child_pointer.
Let root_count entry := Int.signed(temp_word cache (entry_temps entry)).
Let child_count entry := Int.signed(temp_word child_cache (entry_temps entry)).
Let outer i entry := word_store_nested_outer_prefix fe row cache pointer delta column child_cache child_pointer
  child_delta body stable i entry.
Let inner i j entry := word_store_nested_inner_prefix fe row cache pointer delta column child_cache child_pointer
  child_delta body stable i j entry.
Let point i j entry := word_store_nested_point_result row_cursor column_cursor rename sites pointer child_pointer i j entry.

Lemma word_store_nested_inner_frame i entry :
  temp_agree stable (entry_temps entry) (entry_temps (nested_expression_inner_entry row column i entry)).
Proof. eapply temp_agree_trans; apply temp_agree_set; assumption. Qed.
Lemma word_store_nested_check_frame i j entry :
  temp_agree stable (entry_temps entry) (entry_temps (word_store_nested_check_entry row_cursor column_cursor i j entry)).
Proof. eapply temp_agree_trans; apply temp_agree_set; assumption. Qed.
Lemma word_store_nested_inner_cache i entry :
  (entry_temps (nested_expression_inner_entry row column i entry))!child_cache = (entry_temps entry)!child_cache.
Proof. apply word_store_nested_inner_frame; exact CHILD_CACHE_STABLE. Qed.
Lemma word_store_nested_root_header entry current memory :
  ready entry -> temp_agree stable (entry_temps entry) current ->
  header_observations_match (observations entry) memory ->
  eval_expr (entry_ge entry) (entry_env entry) current memory (signed_load_offset pointer delta)
    (Vint(temp_word cache (entry_temps entry))).
Proof.
  intros [ROOT CHILD] FRAME OBSERVED; eapply nested_loaded_offset_outer_header;
    [exact POINTER_STABLE|exact ROOT| |exact FRAME|exact OBSERVED].
  destruct ROOT as [block [offset [raw [PTR [READ CACHE]]]]]; unfold temp_word; rewrite CACHE; reflexivity.
Qed.
Lemma word_store_nested_child_header entry current memory :
  ready entry -> temp_agree stable (entry_temps entry) current ->
  header_observations_match (observations entry) memory ->
  eval_expr (entry_ge entry) (entry_env entry) current memory (signed_load_offset child_pointer child_delta)
    (Vint(temp_word child_cache (entry_temps entry))).
Proof.
  intros [ROOT CHILD] FRAME OBSERVED; eapply nested_loaded_offset_child_header;
    [exact CHILD_POINTER_STABLE|exact CHILD| |exact FRAME|exact OBSERVED].
  destruct CHILD as [block [offset [raw [PTR [READ CACHE]]]]]; unfold temp_word; rewrite CACHE; reflexivity.
Qed.

Theorem word_store_nested_outer_initial entry after final :
  ready entry -> 0<=root_count entry -> (entry_temps entry)!row=Some(Vint Int.zero) ->
  exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    (nested_loaded_offset_source row pointer delta column child_pointer child_delta body) E0 after final Out_normal ->
  outer 0 entry.
Proof.
  intros READY NONNEGATIVE ROW SOURCE; eapply expression_body_prefix_initial;
    [exact READY| |exact NONNEGATIVE|exact ROW| |exact SOURCE].
  - destruct READY as [ROOT CHILD]; destruct ROOT as [block [offset [raw [PTR [READ CACHE]]]]]; eexists; exact CACHE.
  - destruct READY as [ROOT CHILD]; eapply nested_loaded_offset_observations_initial; eassumption.
Qed.

Theorem word_store_nested_inner_open i entry :
  outer i entry -> i<root_count entry -> 0<=child_count entry -> inner i 0 entry.
Proof.
  intros PREFIX ACTIVE NONNEGATIVE; pose proof PREFIX as [READY REST].
  eapply nested_expression_prefix_open with (bound:=signed_load_offset pointer delta)
    (child_bound:=signed_load_offset child_pointer child_delta) (cache:=cache) (stable:=stable)
    (ready:=ready) (observations:=observations);
    [reflexivity|exact(wsbody_quiet checked)|exact ROW_PRIVATE|exact COLUMN_PRIVATE|exact ROW_COLUMN|
     exact CHILD_CACHE_STABLE| |exact NONNEGATIVE| |exact PREFIX|exact ACTIVE].
  - destruct READY as [ROOT CHILD]; destruct CHILD as [block [offset [raw [PTR [READ CACHE]]]]]; eexists; exact CACHE.
  - intros current memory ROW FRAME OBSERVED; apply word_store_nested_root_header; assumption.
Qed.

Lemma word_store_nested_observer_scope entry observer :
  ready entry -> In observer (word_store_nested_observers pointer child_pointer entry) ->
  expression_scope stable (word_observer_address observer).
Proof.
  intros [[block [offset [raw [PTR [READ CACHE]]]]] [child_block [child_offset [child_raw [CPTR [CREAD CCACHE]]]]]] MEMBER.
  unfold word_store_nested_observers,word_store_loaded_observers in MEMBER; rewrite PTR,READ,CPTR,CREAD in MEMBER.
  cbn in MEMBER; destruct MEMBER as [<-|[<-|BAD]];
    [intros id [<-|BAD]; [exact POINTER_STABLE|contradiction]|
     intros id [<-|BAD]; [exact CHILD_POINTER_STABLE|contradiction]|contradiction].
Qed.
Lemma word_store_nested_site_frame entry i j current site :
  In (wss_pointer site) stable -> expression_scope (row::column::stable) (wss_index site) ->
  current!row=Some(Vint(Int.repr i)) -> current!column=Some(Vint(Int.repr j)) ->
  temp_agree stable (entry_temps entry) current ->
  word_store_site_frame rename site current (entry_temps(word_store_nested_check_entry row_cursor column_cursor i j entry)).
Proof.
  intros POINTER INDEX ROW COLUMN FRAME; split.
  - rewrite word_store_nested_check_frame by exact POINTER; apply FRAME; exact POINTER.
  - intros id READ; destruct (INDEX id READ) as [SAME|[SAME|MEMBER]].
    + subst id; rewrite RENAME_ROW; cbn [word_store_nested_check_entry entry_temps];
        rewrite PTree.gso by exact CURSORS_DISTINCT; rewrite PTree.gss; exact ROW.
    + subst id; rewrite RENAME_COLUMN; cbn [word_store_nested_check_entry entry_temps]; rewrite PTree.gss; exact COLUMN.
    + rewrite RENAME_STABLE by exact MEMBER; rewrite word_store_nested_check_frame by exact MEMBER;
        apply FRAME; exact MEMBER.
Qed.

Theorem word_store_nested_inner_receipt i j entry :
  inner i j entry -> j<child_count entry ->
  exists current memory after final,
    current!row=Some(Vint(Int.repr i)) /\ current!column=Some(Vint(Int.repr j)) /\
    temp_agree stable (entry_temps entry) current /\ header_observations_match(observations entry) memory /\
    memory_accesses_back(entry_memory entry) memory /\
    exec_stmt fe (entry_ge entry) (entry_env entry) current memory body E0 after final Out_normal.
Proof.
  intros PREFIX ACTIVE; pose proof PREFIX as [READY REST].
  assert (CHILD_ACTIVE : j<Int.signed(temp_word child_cache
    (entry_temps(nested_expression_inner_entry row column i entry)))).
  { unfold temp_word; rewrite word_store_nested_inner_cache; exact ACTIVE. }
  destruct (@expression_prefix_local_receipt fe column child_cache (signed_load_offset child_pointer child_delta) body
    (row::stable) (fun _=>ready entry) (fun _=>observations entry)
    (nested_expression_inner_entry row column i entry) eq_refl (wsbody_normal checked) (wsbody_quiet checked)
    ltac:(intros index current memory READY' RANGE COLUMN FRAME OBSERVED;
      unfold temp_word; rewrite word_store_nested_inner_cache;
      apply word_store_nested_child_header with (entry:=entry); [exact READY'| |exact OBSERVED];
      eapply temp_agree_trans; [apply word_store_nested_inner_frame|];
      eapply temp_agree_weaken with (big:=row::stable); [intros id MEMBER; right; exact MEMBER|exact FRAME])
    j PREFIX CHILD_ACTIVE)
    as [current [memory [after [final [COLUMN [FRAME [OBSERVED [BACK SOURCE]]]]]]]].
  exists current,memory,after,final; split.
  - rewrite (FRAME row (or_introl eq_refl)); cbn [nested_expression_inner_entry entry_temps];
      rewrite PTree.gso by exact ROW_COLUMN; apply PTree.gss.
  - split; [exact COLUMN|split; [|split; [exact OBSERVED|split; [exact BACK|exact SOURCE]]]].
    eapply temp_agree_trans; [apply word_store_nested_inner_frame|].
    eapply temp_agree_weaken with (big:=row::stable); [intros id MEMBER; right; exact MEMBER|exact FRAME].
Qed.

Theorem word_store_nested_point_domain i j entry :
  inner i j entry -> j<child_count entry ->
  word_store_sequence_domain fe rename sites (word_store_nested_observers pointer child_pointer entry)
    (word_store_nested_check_entry row_cursor column_cursor i j entry).
Proof.
  intros PREFIX ACTIVE; pose proof PREFIX as [READY REST].
  destruct (word_store_nested_inner_receipt PREFIX ACTIVE)
    as [current [memory [after [final [ROW [COLUMN [FRAME [OBSERVED [BACK SOURCE]]]]]]]]].
  eapply word_store_sequence_domain_from_body with (body:=body) (current:=current) (memory:=memory);
    [exact(wsbody_flatten checked)| | |exact BACK|exact SOURCE].
  - destruct (word_store_nested_observers_receipt READY) as [READS SNAPSHOTS].
    apply Forall_forall; intros observer MEMBER; eapply word_observer_receipt_frame with (live:=stable).
    + rewrite Forall_forall in READS; apply READS; exact MEMBER.
    + eapply word_store_nested_observer_scope; eassumption.
    + apply word_store_nested_check_frame.
  - apply Forall_forall; intros site MEMBER; eapply word_store_nested_site_frame;
      [apply SITE_POINTERS; exact MEMBER|apply SITE_INDICES; exact MEMBER|exact ROW|exact COLUMN|exact FRAME].
Qed.

Theorem word_store_nested_point_preserved i j entry :
  inner i j entry -> j<child_count entry -> point i j entry=true ->
  forall current memory after final,
    current!row=Some(Vint(Int.repr i)) -> current!column=Some(Vint(Int.repr j)) ->
    temp_agree stable (entry_temps entry) current -> header_observations_match(observations entry) memory ->
    exec_stmt fe (entry_ge entry) (entry_env entry) current memory body E0 after final Out_normal ->
    header_observations_match(observations entry) final.
Proof.
  intros PREFIX ACTIVE ACCEPT; pose proof PREFIX as [READY REST].
  pose proof (@word_store_sequence_sound fe rename sites (word_store_nested_observers pointer child_pointer entry)
    (word_store_nested_check_entry row_cursor column_cursor i j entry) (wsbody_words checked)
    (word_store_nested_point_domain PREFIX ACTIVE) ACCEPT) as PRESERVE.
  destruct (word_store_nested_observers_receipt READY) as [READS SNAPSHOTS].
  intros current memory after final ROW COLUMN FRAME OBSERVED SOURCE.
  unfold observations in OBSERVED |- *.
  rewrite <-SNAPSHOTS in OBSERVED |- *; eapply PRESERVE.
  - apply Forall_forall; intros site MEMBER; eapply word_store_nested_site_frame;
      [apply SITE_POINTERS; exact MEMBER|apply SITE_INDICES; exact MEMBER|exact ROW|exact COLUMN|exact FRAME].
  - exact OBSERVED.
  - apply flatten_region_execution in SOURCE; rewrite(wsbody_flatten checked) in SOURCE; exact SOURCE.
Qed.

Theorem word_store_nested_inner_advance i j entry :
  inner i j entry -> j<child_count entry -> point i j entry=true -> inner i (j+1) entry.
Proof.
  intros PREFIX ACTIVE ACCEPT; pose proof PREFIX as [READY REST].
  eapply expression_prefix_local_advance with (written:=[]) (bound:=signed_load_offset child_pointer child_delta)
    (cache:=child_cache) (stable:=row::stable) (ready:=fun _=>ready entry) (observations:=fun _=>observations entry);
    try exact PREFIX; try reflexivity; try exact(wsbody_normal checked); try exact(wsbody_quiet checked);
    try exact(wsbody_writes checked); try solve [cbn; tauto];
    try solve [intros [SAME|BAD]; [apply ROW_COLUMN; exact SAME|apply COLUMN_PRIVATE; exact BAD]].
  - intros index current memory READY' RANGE COLUMN FRAME OBSERVED;
      unfold temp_word; rewrite word_store_nested_inner_cache;
      apply word_store_nested_child_header with (entry:=entry); [exact READY'| |exact OBSERVED].
    eapply temp_agree_trans; [apply word_store_nested_inner_frame|].
    eapply temp_agree_weaken with (big:=row::stable); [intros id MEMBER; right; exact MEMBER|exact FRAME].
  - intros ge locals current memory after final RUN; exact(proj2(word_store_loaded_source_permissions checked RUN)).
  - unfold temp_word; rewrite word_store_nested_inner_cache; exact ACTIVE.
  - intros current memory after final COLUMN FRAME OBSERVED SOURCE.
    eapply word_store_nested_point_preserved; [exact PREFIX|exact ACTIVE|exact ACCEPT| |exact COLUMN| |exact OBSERVED|exact SOURCE].
    + rewrite (FRAME row (or_introl eq_refl)); cbn [nested_expression_inner_entry entry_temps];
        rewrite PTree.gso by exact ROW_COLUMN; apply PTree.gss.
    + eapply temp_agree_trans; [apply word_store_nested_inner_frame|].
      eapply temp_agree_weaken with (big:=row::stable); [intros id MEMBER; right; exact MEMBER|exact FRAME].
Qed.

(** Only this current row's accepted leaves are required. No future-row
    permission or cached-child execution is a premise. *)
Theorem word_store_nested_outer_advance i entry :
  outer i entry -> i<root_count entry -> 0<=child_count entry ->
  (forall j, 0<=j<child_count entry -> inner i j entry /\ point i j entry=true) ->
  outer (i+1) entry.
Proof.
  intros PREFIX ACTIVE NONNEGATIVE ACCEPTED; pose proof PREFIX as [READY REST].
  eapply nested_expression_prefix_advance with (written:=[]) (bound:=signed_load_offset pointer delta)
    (child_bound:=signed_load_offset child_pointer child_delta) (cache:=cache) (child_cache:=child_cache)
    (stable:=stable) (ready:=ready) (observations:=observations);
    try reflexivity; try exact ROW_PRIVATE; try exact COLUMN_PRIVATE; try exact ROW_COLUMN;
    try exact CHILD_CACHE_STABLE; try exact(wsbody_normal checked); try exact(wsbody_quiet checked);
    try exact(wsbody_writes checked); try exact NONNEGATIVE; try exact PREFIX; try exact ACTIVE;
    try solve [cbn; tauto].
  - intros state index current memory READY' RANGE ROW FRAME OBSERVED; apply word_store_nested_root_header; assumption.
  - destruct READY as [ROOT CHILD]; destruct CHILD as [block [offset [raw [PTR [READ CACHE]]]]]; eexists; exact CACHE.
  - intros j current memory RANGE ROW COLUMN FRAME OBSERVED; apply word_store_nested_child_header; assumption.
  - intros j current memory after final RANGE ROW COLUMN FRAME OBSERVED SOURCE.
    destruct (ACCEPTED j RANGE) as [INV ACCEPT]; eapply word_store_nested_point_preserved;
      [exact INV|exact(proj2 RANGE)|exact ACCEPT|exact ROW|exact COLUMN|exact FRAME|exact OBSERVED|exact SOURCE].
Qed.
End PREFIX.

Print Assumptions word_store_nested_observers_receipt.
Print Assumptions word_store_nested_probe_static.
Print Assumptions word_store_nested_inner_frame.
Print Assumptions word_store_nested_check_frame.
Print Assumptions word_store_nested_inner_cache.
Print Assumptions word_store_nested_root_header.
Print Assumptions word_store_nested_child_header.
Print Assumptions word_store_nested_outer_initial.
Print Assumptions word_store_nested_inner_open.
Print Assumptions word_store_nested_observer_scope.
Print Assumptions word_store_nested_site_frame.
Print Assumptions word_store_nested_inner_receipt.
Print Assumptions word_store_nested_point_domain.
Print Assumptions word_store_nested_point_preserved.
Print Assumptions word_store_nested_inner_advance.
Print Assumptions word_store_nested_outer_advance.
