(** An accepted actual store sequence licenses the next loaded source test.
    The cached loop is not an input assumption of this prefix construction. *)
From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightRedundantSet
  ClightNoWrap ClightPureExpr ClightStraightLine ClightLoopSyntax ClightRegionProgress.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightLoadedOffsetHeader
  ClightExpressionBodyPrefix ClightExpressionHeaderCapture ClightObservedHeaderPrefix
  ClightAffineJointObservation ClightWordCoordinateRename ClightWordArithmeticTransport
  ClightDirectWordObservation ClightRenamedWordObservation ClightStorePermissions
  ClightWordStoreSequence ClightWordStoreSequenceFactory.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition word_store_loaded_observers pointer entry :=
  match (entry_temps entry)!pointer with
  | Some (Vptr block offset) => match Mem.loadv Mint32 (entry_memory entry) (Vptr block offset) with
    | Some value => [ClightWordObserver (signed_pointer_temp pointer) block offset value]
    | None => [] end
  | _ => [] end.
Definition word_store_loaded_probe rename sites pointer :=
  word_store_sequence_tree rename sites
    [ClightWordObserver (signed_pointer_temp pointer) 1%positive Ptrofs.zero Vundef].
Definition word_store_loaded_entry cursor i entry :=
  Entry (entry_ge entry) (entry_env entry)
    (PTree.set cursor (Vint (Int.repr i)) (entry_temps entry)) (entry_memory entry).
Definition word_store_loaded_prefix fe row cache pointer delta body stable i entry :=
  expression_body_prefix fe row cache (signed_load_offset pointer delta) body stable
    (loaded_offset_cached_header pointer delta cache) (loaded_offset_observations pointer) i entry.

Lemma word_store_sequence_observer_addresses rename sites first second :
  map word_observer_address first = map word_observer_address second ->
  word_store_sequence_tree rename sites first = word_store_sequence_tree rename sites second.
Proof.
  intro ADDRESSES; induction sites as [|site rest IH]; cbn [word_store_sequence_tree]; [reflexivity|].
  unfold renamed_word_observer_tree; rewrite (@direct_word_observer_tree_addresses
    (fun _ => None) (wss_pointer site) (word_rename rename (wss_index site)) first second ADDRESSES), IH;
    reflexivity.
Qed.
Lemma word_store_loaded_observers_receipt pointer delta cache entry :
  loaded_offset_cached_header pointer delta cache entry ->
  Forall (word_observer_receipt (entry_ge entry) (entry_env entry)
    (entry_temps entry) (entry_memory entry)) (word_store_loaded_observers pointer entry) /\
  map word_observer_snapshot (word_store_loaded_observers pointer entry) = loaded_offset_observations pointer entry.
Proof.
  intros [block [offset [raw [POINTER [READ CACHE]]]]].
  unfold word_store_loaded_observers,loaded_offset_observations; rewrite POINTER,READ; split.
  - constructor; [split; [reflexivity|split; [constructor; exact POINTER|exact READ]]|constructor].
  - reflexivity.
Qed.
Lemma word_store_loaded_probe_static rename sites pointer delta cache entry :
  loaded_offset_cached_header pointer delta cache entry ->
  word_store_sequence_tree rename sites (word_store_loaded_observers pointer entry) =
    word_store_loaded_probe rename sites pointer.
Proof.
  intros [block [offset [raw [POINTER [READ CACHE]]]]].
  apply word_store_sequence_observer_addresses.
  unfold word_store_loaded_observers; rewrite POINTER,READ; reflexivity.
Qed.

Theorem word_store_loaded_source_permissions body (checked : checked_word_store_body body)
    fe ge locals current memory after final :
  exec_stmt fe ge locals current memory body E0 after final Out_normal ->
  after = current /\ memory_accesses_back memory final.
Proof.
  intro RUN; apply flatten_region_execution in RUN; rewrite (wsbody_flatten checked) in RUN.
  eapply word_store_sequence_permissions; exact RUN.
Qed.

Lemma word_store_loaded_site_frame rename row cursor stable entry i current site :
  In (wss_pointer site) stable -> expression_scope (row :: stable) (wss_index site) ->
  ~In cursor stable -> rename row = cursor -> (forall id, In id stable -> rename id = id) ->
  current!row = Some (Vint (Int.repr i)) -> temp_agree stable (entry_temps entry) current ->
  word_store_site_frame rename site current (entry_temps (word_store_loaded_entry cursor i entry)).
Proof.
  intros POINTER SCOPE PRIVATE ROW_RENAME STABLE_RENAME CURRENT FRAME; split.
  - cbn [word_store_loaded_entry entry_temps]; rewrite PTree.gso by (intro SAME; apply PRIVATE; congruence).
    apply FRAME; exact POINTER.
  - intros id MEMBER; destruct (SCOPE id MEMBER) as [ROW|STABLE].
    + subst id; rewrite ROW_RENAME; cbn [word_store_loaded_entry entry_temps]; rewrite PTree.gss; exact CURRENT.
    + rewrite STABLE_RENAME by exact STABLE; cbn [word_store_loaded_entry entry_temps].
      change (In id stable) in STABLE.
      rewrite PTree.gso by (intro SAME; apply PRIVATE; congruence); apply FRAME; exact STABLE.
Qed.

Section LOADED.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variables row cache pointer cursor : ident.
Variable delta : int.
Variable body : statement.
Variable checked : checked_word_store_body body.
Variable stable : list ident.
Variable rename : ident -> ident.
Hypotheses (POINTER_STABLE : In pointer stable) (ROW_PRIVATE : ~In row stable)
  (CURSOR_PRIVATE : ~In cursor stable) (RENAME_ROW : rename row = cursor).
Hypothesis RENAME_STABLE : forall id, In id stable -> rename id = id.
Hypothesis SITE_POINTERS : forall site, In site (wsbody_sites checked) -> In (wss_pointer site) stable.
Hypothesis SITE_INDICES : forall site, In site (wsbody_sites checked) ->
  expression_scope (row :: stable) (wss_index site).
Let sites := wsbody_sites checked.
Let ready := loaded_offset_cached_header pointer delta cache.
Let observations := loaded_offset_observations pointer.
Let count entry := Int.signed (temp_word cache (entry_temps entry)).

Lemma word_store_loaded_header entry i current memory :
  ready entry -> 0 <= i <= count entry -> current!row = Some (Vint (Int.repr i)) ->
  temp_agree stable (entry_temps entry) current -> header_observations_match (observations entry) memory ->
  eval_expr (entry_ge entry) (entry_env entry) current memory (signed_load_offset pointer delta)
    (Vint (temp_word cache (entry_temps entry))).
Proof.
  intros READY RANGE ROW FRAME OBSERVED; eapply loaded_offset_bound_from_observations;
    [exact POINTER_STABLE|exact READY| |exact FRAME|exact OBSERVED].
  destruct READY as [block [offset [raw [PTR [READ CACHE]]]]]; unfold temp_word; rewrite CACHE; reflexivity.
Qed.

Theorem word_store_loaded_prefix_initial entry after final :
  ready entry -> 0 <= count entry -> (entry_temps entry)!row = Some (Vint Int.zero) ->
  exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    (loaded_offset_loop row pointer delta body) E0 after final Out_normal ->
  word_store_loaded_prefix fe row cache pointer delta body stable 0 entry.
Proof.
  intros READY NONNEGATIVE ROW SOURCE; eapply expression_body_prefix_initial;
    [exact READY| |exact NONNEGATIVE|exact ROW| |exact SOURCE].
  - destruct READY as [block [offset [raw [PTR [READ CACHE]]]]]; eexists; exact CACHE.
  - eapply loaded_offset_initial_observations; exact READY.
Qed.

Theorem word_store_loaded_prefix_receipt i entry :
  word_store_loaded_prefix fe row cache pointer delta body stable i entry -> i < count entry ->
  exists current memory after final,
    current!row = Some (Vint (Int.repr i)) /\ temp_agree stable (entry_temps entry) current /\
    header_observations_match (observations entry) memory /\ memory_accesses_back (entry_memory entry) memory /\
    exec_stmt fe (entry_ge entry) (entry_env entry) current memory body E0 after final Out_normal.
Proof.
  intros PREFIX ACTIVE; eapply expression_body_prefix_receipt with
    (bound:=signed_load_offset pointer delta) (cache:=cache) (stable:=stable)
    (ready:=ready) (observations:=observations);
    [reflexivity|exact (wsbody_normal checked)|exact (wsbody_quiet checked)|exact word_store_loaded_header|exact PREFIX|exact ACTIVE].
Qed.

Theorem word_store_loaded_point_domain i entry :
  word_store_loaded_prefix fe row cache pointer delta body stable i entry -> i < count entry ->
  word_store_sequence_domain fe rename sites (word_store_loaded_observers pointer entry)
    (word_store_loaded_entry cursor i entry).
Proof.
  intros PREFIX ACTIVE.
  pose proof PREFIX as READY; destruct READY as [READY REST].
  destruct (@word_store_loaded_prefix_receipt i entry PREFIX ACTIVE)
    as [current [memory [after [final [ROW [FRAME [OBSERVED [BACK SOURCE]]]]]]]].
  eapply word_store_sequence_domain_from_body with (body:=body) (current:=current) (memory:=memory);
    [exact (wsbody_flatten checked)| | |exact BACK|exact SOURCE].
  - destruct READY as [block [offset [raw [PTR [READ CACHE]]]]].
    unfold word_store_loaded_observers; rewrite PTR,READ.
    constructor; [|constructor].
    split; [reflexivity|split; [|exact READ]].
    constructor; cbn [word_store_loaded_entry entry_temps]; rewrite PTree.gso by
      (intro SAME; apply CURSOR_PRIVATE; congruence); exact PTR.
  - apply Forall_forall; intros site MEMBER; eapply word_store_loaded_site_frame;
      [apply SITE_POINTERS; exact MEMBER|apply SITE_INDICES; exact MEMBER|exact CURSOR_PRIVATE|
       exact RENAME_ROW|exact RENAME_STABLE|exact ROW|exact FRAME].
Qed.

Theorem word_store_loaded_point_execution i entry :
  word_store_loaded_prefix fe row cache pointer delta body stable i entry -> i < count entry ->
  decision_run (word_store_loaded_entry cursor i entry) (word_store_loaded_probe rename sites pointer)
    (word_store_sequence_flag rename sites (word_store_loaded_observers pointer entry)
      (word_store_loaded_entry cursor i entry)).
Proof.
  intros PREFIX ACTIVE; pose proof PREFIX as READY; destruct READY as [READY REST].
  rewrite <- (word_store_loaded_probe_static rename sites READY).
  eapply word_store_sequence_tree_execution; [exact (wsbody_words checked)|apply word_store_loaded_point_domain; assumption].
Qed.

Theorem word_store_loaded_prefix_advance i entry :
  word_store_loaded_prefix fe row cache pointer delta body stable i entry -> i < count entry ->
  word_store_sequence_flag rename sites (word_store_loaded_observers pointer entry)
    (word_store_loaded_entry cursor i entry) = true ->
  word_store_loaded_prefix fe row cache pointer delta body stable (i+1) entry.
Proof.
  intros PREFIX ACTIVE ACCEPT; pose proof PREFIX as READY; destruct READY as [READY REST].
  pose proof (@word_store_sequence_sound fe rename sites (word_store_loaded_observers pointer entry)
    (word_store_loaded_entry cursor i entry) (wsbody_words checked)
    (word_store_loaded_point_domain PREFIX ACTIVE) ACCEPT) as PRESERVE.
  destruct (word_store_loaded_observers_receipt READY) as [READS SNAPSHOTS].
  eapply expression_body_prefix_advance with (written:=[]) (bound:=signed_load_offset pointer delta)
    (cache:=cache) (stable:=stable) (ready:=ready) (observations:=observations);
    try exact PREFIX; try exact ACTIVE; try reflexivity;
    try exact ROW_PRIVATE; try exact (wsbody_normal checked); try exact (wsbody_quiet checked);
    try exact (wsbody_writes checked); try solve [cbn; tauto].
  - intros ge locals current memory after final RUN; exact (proj2 (word_store_loaded_source_permissions checked RUN)).
  - exact word_store_loaded_header.
  - intros current memory after final ROW FRAME OBSERVED SOURCE.
    unfold observations in OBSERVED |- *.
    rewrite <- SNAPSHOTS in OBSERVED |- *; eapply PRESERVE.
    + apply Forall_forall; intros site MEMBER; eapply word_store_loaded_site_frame;
        [apply SITE_POINTERS; exact MEMBER|apply SITE_INDICES; exact MEMBER|exact CURSOR_PRIVATE|
         exact RENAME_ROW|exact RENAME_STABLE|exact ROW|exact FRAME].
    + exact OBSERVED.
    + apply flatten_region_execution in SOURCE; rewrite (wsbody_flatten checked) in SOURCE; exact SOURCE.
Qed.
End LOADED.

Print Assumptions word_store_sequence_observer_addresses.
Print Assumptions word_store_loaded_observers_receipt.
Print Assumptions word_store_loaded_probe_static.
Print Assumptions word_store_loaded_source_permissions.
Print Assumptions word_store_loaded_site_frame.
Print Assumptions word_store_loaded_header.
Print Assumptions word_store_loaded_prefix_initial.
Print Assumptions word_store_loaded_prefix_receipt.
Print Assumptions word_store_loaded_point_domain.
Print Assumptions word_store_loaded_point_execution.
Print Assumptions word_store_loaded_prefix_advance.
