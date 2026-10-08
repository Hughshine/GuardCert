(** Fixed Clight cursor scanning, licensed by the original loaded source.
    Only complete acceptance constructs the cached-source execution. *)
From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightTempFootprint
  ClightNoWrap ClightPureExpr ClightStraightLine ClightLoopSyntax ClightFrontendLoopProtocol
  ClightProjectedExecution.
From GuardMemory Require Import GuardMemoryBooleanScan.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightLoadedOffsetHeader
  ClightExpressionBodyPrefix ClightObservedHeaderPrefix ClightAffineJointObservation
  ClightWordArithmeticTransport ClightWordCoordinateRename ClightDirectWordObservation
  ClightWordStoreSequence ClightWordStoreSequenceFactory ClightWordStoreSequenceLoaded
  ClightWordStoreSequenceRuntime ClightShortCircuitPrefixLoop.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition word_store_loaded_point_code rename sites pointer flag :=
  tree_statement (word_store_loaded_probe rename sites pointer)
    (Sset flag (Econst_int Int.one type_int32s)) (Sset flag (Econst_int Int.zero type_int32s)).
Definition word_store_loaded_scan_code cache cursor bound flag rename sites pointer :=
  Ssequence (Sset bound (Etempvar cache type_int32s))
    (Ssequence (Sset flag (Econst_int Int.one type_int32s))
      (Ssequence (Sset cursor (Econst_int Int.zero type_int32s))
        (short_circuit_prefix_loop cursor bound flag (word_store_loaded_point_code rename sites pointer flag)))).
Definition word_store_loaded_point_result cursor rename sites pointer index entry :=
  word_store_sequence_flag rename sites (word_store_loaded_observers pointer entry)
    (word_store_loaded_entry cursor index entry).
Definition word_store_loaded_scan_result cache cursor rename sites pointer entry :=
  memory_boolean_scan_result (fun index=>word_store_loaded_point_result cursor rename sites pointer index entry)
    0 (Z.to_nat (Int.signed (temp_word cache (entry_temps entry)))).

Section SCAN.
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
Let prefix index entry := word_store_loaded_prefix fe row cache pointer delta body stable index entry.
Let count entry := Int.signed (temp_word cache (entry_temps entry)).
Let point index entry := word_store_loaded_point_result cursor rename sites pointer index entry.

Lemma word_store_loaded_scan_read_scope entry :
  loaded_offset_cached_header pointer delta cache entry ->
  incl (word_store_sequence_probe_reads rename sites (word_store_loaded_observers pointer entry))
    (cursor :: stable).
Proof.
  intros READY identifier MEMBER; unfold word_store_sequence_probe_reads in MEMBER;
    apply in_app_or in MEMBER; destruct MEMBER as [SITE|OBSERVER].
  - unfold word_store_sequence_address_reads in SITE; apply in_flat_map in SITE as [site [SITE READ]].
    destruct READ as [SAME|INDEX].
    + subst identifier; right; apply SITE_POINTERS; exact SITE.
    + assert (WORD : word_arithmetic (wss_index site)).
      { pose proof (wsbody_words checked) as WORDS; rewrite Forall_forall in WORDS; apply WORDS; exact SITE. }
      rewrite word_rename_temps in INDEX by exact WORD.
      apply in_map_iff in INDEX as [original [SAME READ]]; subst identifier.
      destruct (SITE_INDICES site SITE original READ) as [ROW|STABLE].
      * subst original; rewrite RENAME_ROW; left; reflexivity.
      * rewrite RENAME_STABLE by exact STABLE; right; exact STABLE.
  - destruct READY as [block [offset [raw [POINTER [LOAD CACHE]]]]].
    unfold word_store_loaded_observers in OBSERVER; rewrite POINTER,LOAD in OBSERVER.
    cbn [flat_map word_observer_address signed_pointer_temp expression_temps] in OBSERVER.
    destruct OBSERVER as [SAME|BAD]; [subst identifier; right; exact POINTER_STABLE|contradiction].
Qed.

Theorem word_store_loaded_point_preserved index entry :
  prefix index entry -> index < count entry -> point index entry = true ->
  expression_body_preserved fe row body stable (loaded_offset_observations pointer) index entry.
Proof.
  intros PREFIX ACTIVE ACCEPT; pose proof PREFIX as READY; destruct READY as [READY REST].
  pose proof (@word_store_sequence_sound fe rename sites (word_store_loaded_observers pointer entry)
    (word_store_loaded_entry cursor index entry) (wsbody_words checked)
    (@word_store_loaded_point_domain fe row cache pointer cursor delta body checked stable rename
      POINTER_STABLE CURSOR_PRIVATE RENAME_ROW RENAME_STABLE SITE_POINTERS SITE_INDICES
      index entry PREFIX ACTIVE) ACCEPT) as PRESERVE.
  destruct (word_store_loaded_observers_receipt READY) as [READS SNAPSHOTS].
  intros current memory after final ROW FRAME OBSERVED SOURCE.
  rewrite <- SNAPSHOTS in OBSERVED |- *; eapply PRESERVE.
  - apply Forall_forall; intros site MEMBER; eapply word_store_loaded_site_frame;
      [apply SITE_POINTERS; exact MEMBER|apply SITE_INDICES; exact MEMBER|exact CURSOR_PRIVATE|
       exact RENAME_ROW|exact RENAME_STABLE|exact ROW|exact FRAME].
  - exact OBSERVED.
  - apply flatten_region_execution in SOURCE; rewrite (wsbody_flatten checked) in SOURCE; exact SOURCE.
Qed.

Theorem word_store_loaded_point_runtime index entry current flag :
  prefix index entry -> index < count entry ->
  current!cursor = Some (Vint (Int.repr index)) -> temp_agree stable (entry_temps entry) current ->
  exec_stmt fe (entry_ge entry) (entry_env entry) current (entry_memory entry)
    (word_store_loaded_point_code rename sites pointer flag) E0
    (PTree.set flag (memory_boolean_word (point index entry)) current) (entry_memory entry) Out_normal.
Proof.
  intros PREFIX ACTIVE CURSOR FRAME; pose proof PREFIX as READY; destruct READY as [READY REST].
  assert (POINT_FRAME : temp_agree
    (word_store_sequence_probe_reads rename sites (word_store_loaded_observers pointer entry))
    (entry_temps (word_store_loaded_entry cursor index entry)) current).
  { intros identifier MEMBER; destruct (word_store_loaded_scan_read_scope READY identifier MEMBER) as [SAME|STABLE].
    - subst identifier; cbn [word_store_loaded_entry entry_temps]; rewrite PTree.gss; exact CURSOR.
    - change (In identifier stable) in STABLE.
      cbn [word_store_loaded_entry entry_temps]; rewrite PTree.gso by
        (intro SAME; apply CURSOR_PRIVATE; congruence); apply FRAME; exact STABLE. }
  pose proof (@word_store_sequence_runtime_check fe rename sites (word_store_loaded_observers pointer entry)
    (entry_ge entry) (entry_env entry) (entry_temps (word_store_loaded_entry cursor index entry))
    current (entry_memory entry) flag (wsbody_words checked)
    (@word_store_loaded_point_domain fe row cache pointer cursor delta body checked stable rename
      POINTER_STABLE CURSOR_PRIVATE RENAME_ROW RENAME_STABLE SITE_POINTERS SITE_INDICES
      index entry PREFIX ACTIVE) POINT_FRAME) as RUN.
  unfold word_store_sequence_check_code in RUN; rewrite (word_store_loaded_probe_static rename sites READY) in RUN.
  exact RUN.
Qed.

Theorem word_store_loaded_scan_execution entry bound flag live current :
  cursor <> bound -> cursor <> flag -> bound <> flag ->
  ~In cursor live -> ~In bound live -> ~In flag live ->
  incl stable live -> In cache live -> prefix 0 entry -> temp_agree live (entry_temps entry) current ->
  exists after,
    exec_stmt fe (entry_ge entry) (entry_env entry) current (entry_memory entry)
      (word_store_loaded_scan_code cache cursor bound flag rename sites pointer) E0 after (entry_memory entry) Out_normal /\
    temp_agree live current after /\
    after!flag = Some (memory_boolean_word (word_store_loaded_scan_result cache cursor rename sites pointer entry)) /\
    (word_store_loaded_scan_result cache cursor rename sites pointer entry = true ->
      forall index, 0 <= index < count entry ->
      expression_body_preserved fe row body stable (loaded_offset_observations pointer) index entry).
Proof.
  intros DISTINCT CURSOR_FLAG BOUND_FLAG CURSOR_LIVE BOUND_LIVE FLAG_LIVE STABLE_LIVE CACHE_LIVE PREFIX FRAME.
  pose proof PREFIX as [READY [CACHE [RANGE REST]]].
  change (0 <= 0 <= count entry) in RANGE.
  assert (NONNEGATIVE : 0 <= count entry) by lia.
  assert (UPPER : signed_range (count entry)) by apply Int.signed_range.
  set (cached := PTree.set bound (Vint (temp_word cache (entry_temps entry))) current).
  set (flagged := PTree.set flag (Vint Int.one) cached).
  set (initialized := PTree.set cursor (Vint Int.zero) flagged).
  assert (INIT_FRAME : temp_agree live current initialized).
  { eapply temp_agree_trans with (le1:=cached); [apply temp_agree_set; exact BOUND_LIVE|].
    eapply temp_agree_trans with (le1:=flagged); apply temp_agree_set; assumption. }
  assert (INIT_CURSOR : initialized!cursor = Some (Vint (Int.repr 0))) by apply PTree.gss.
  assert (INIT_BOUND : initialized!bound = Some (Vint (Int.repr (count entry)))).
  { unfold initialized,flagged,cached; rewrite PTree.gso by congruence.
    rewrite PTree.gso by exact BOUND_FLAG; rewrite PTree.gss; unfold count; rewrite Int.repr_signed; reflexivity. }
  assert (INIT_FLAG : initialized!flag = Some (memory_boolean_word true)).
  { unfold initialized,flagged; rewrite PTree.gso by congruence; apply PTree.gss. }
  assert (ADVANCE : forall index, 0 <= index < count entry -> prefix index entry ->
    point index entry = true -> prefix (index+1) entry).
  { intros index ACTIVE INV ACCEPT; exact (@word_store_loaded_prefix_advance fe row cache pointer cursor delta
      body checked stable rename POINTER_STABLE ROW_PRIVATE CURSOR_PRIVATE RENAME_ROW RENAME_STABLE
      SITE_POINTERS SITE_INDICES index entry INV (proj2 ACTIVE) ACCEPT). }
  assert (BODY : forall index checked_temps, signed_range index -> 0 <= index < count entry -> prefix index entry ->
    checked_temps!cursor = Some (Vint (Int.repr index)) ->
    checked_temps!bound = Some (Vint (Int.repr (count entry))) ->
    checked_temps!flag = Some (memory_boolean_word true) -> temp_agree live (entry_temps entry) checked_temps ->
    exists after,
      exec_stmt fe (entry_ge entry) (entry_env entry) checked_temps (entry_memory entry)
        (word_store_loaded_point_code rename sites pointer flag) E0 after (entry_memory entry) Out_normal /\
      temp_agree (cursor::bound::live) checked_temps after /\ after!flag = Some (memory_boolean_word (point index entry))).
  { intros index checked_temps INDEX ACTIVE INV CURSOR BOUND FLAG PUBLIC.
    exists (PTree.set flag (memory_boolean_word (point index entry)) checked_temps); split.
    - apply word_store_loaded_point_runtime; [exact INV|exact (proj2 ACTIVE)|exact CURSOR|].
      eapply temp_agree_weaken; eassumption.
    - split; [apply temp_agree_set; cbn; intros [SAME|[SAME|BAD]]; congruence|apply PTree.gss]. }
  destruct (@short_circuit_prefix_loop_execution fe (entry_ge entry) (entry_env entry) (entry_memory entry)
    cursor bound flag (word_store_loaded_point_code rename sites pointer flag) live (entry_temps entry)
    0 (count entry) (fun index=>prefix index entry) (fun index=>point index entry)
    DISTINCT CURSOR_FLAG BOUND_FLAG CURSOR_LIVE UPPER ADVANCE BODY (Z.to_nat (count entry)) 0 initialized)
    as [after [RUN [AFTER [RESULT ACCEPTED]]]].
  - rewrite Z2Nat.id by exact NONNEGATIVE; lia.
  - lia.
  - unfold signed_range; change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia.
  - exact PREFIX.
  - exact INIT_CURSOR.
  - exact INIT_BOUND.
  - exact INIT_FLAG.
  - eapply temp_agree_trans; eassumption.
  - exists after; split.
    + unfold word_store_loaded_scan_code; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0)
        (le1:=cached) (m1:=entry_memory entry).
      * constructor; constructor; destruct CACHE as [word WORD]; rewrite FRAME by exact CACHE_LIVE.
        unfold temp_word; rewrite WORD; reflexivity.
      * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=flagged) (m1:=entry_memory entry); [constructor; constructor|].
        eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=initialized) (m1:=entry_memory entry); [constructor; constructor|exact RUN].
    + split; [eapply temp_agree_trans; [exact INIT_FRAME|exact AFTER]|split; [exact RESULT|]].
      intros ACCEPT index ACTIVE; destruct (ACCEPTED ACCEPT index ACTIVE) as [INV CHECK].
      apply word_store_loaded_point_preserved; [exact INV|exact (proj2 ACTIVE)|exact CHECK].
Qed.

Theorem word_store_loaded_scan_from_source entry bound flag live current source_after final :
  In cache stable -> cursor <> bound -> cursor <> flag -> bound <> flag ->
  ~In cursor live -> ~In bound live -> ~In flag live -> incl stable live -> In cache live ->
  loaded_offset_cached_header pointer delta cache entry -> 0 <= count entry ->
  (entry_temps entry)!row = Some (Vint Int.zero) ->
  exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    (loaded_offset_loop row pointer delta body) E0 source_after final Out_normal ->
  temp_agree live (entry_temps entry) current ->
  exists after,
    exec_stmt fe (entry_ge entry) (entry_env entry) current (entry_memory entry)
      (word_store_loaded_scan_code cache cursor bound flag rename sites pointer) E0 after (entry_memory entry) Out_normal /\
    temp_agree live current after /\
    after!flag = Some (memory_boolean_word (word_store_loaded_scan_result cache cursor rename sites pointer entry)) /\
    (word_store_loaded_scan_result cache cursor rename sites pointer entry = true ->
      exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
        (frontend_counted_loop row cache body) E0 source_after final Out_normal).
Proof.
  intros CACHE_STABLE DISTINCT CURSOR_FLAG BOUND_FLAG CURSOR_LIVE BOUND_LIVE FLAG_LIVE STABLE_LIVE CACHE_LIVE
    READY NONNEGATIVE ROW SOURCE FRAME.
  pose proof (@word_store_loaded_prefix_initial fe row cache pointer delta body stable entry source_after final
    READY NONNEGATIVE ROW SOURCE) as PREFIX.
  destruct (word_store_loaded_scan_execution DISTINCT CURSOR_FLAG BOUND_FLAG CURSOR_LIVE BOUND_LIVE FLAG_LIVE
    STABLE_LIVE CACHE_LIVE PREFIX FRAME) as [after [RUN [PUBLIC [RESULT PRESERVE]]]].
  exists after; split; [exact RUN|split; [exact PUBLIC|split; [exact RESULT|]]].
  intro ACCEPT; eapply loaded_offset_body_initial_cached with (stable:=stable) (written:=[]);
    try exact POINTER_STABLE; try exact CACHE_STABLE; try exact ROW_PRIVATE;
    try exact (wsbody_normal checked); try exact (wsbody_quiet checked); try exact (wsbody_writes checked);
    try exact READY; try exact NONNEGATIVE; try exact ROW; try exact SOURCE; try solve [cbn; tauto].
  intros index current_temps memory exit last ACTIVE CURRENT FRAME' OBSERVED BODY.
  exact (PRESERVE ACCEPT index ACTIVE current_temps memory exit last CURRENT FRAME' OBSERVED BODY).
Qed.

Lemma word_store_loaded_cached_writes : writes_only [row] (frontend_counted_loop row cache body).
Proof.
  unfold frontend_counted_loop,counter_increment; apply writes_loop; apply writes_sequence.
  - apply writes_sequence; [constructor|apply writes_if; constructor].
  - eapply writes_only_weaken; [|exact (wsbody_writes checked)]; cbn; tauto.
  - constructor.
  - constructor; cbn; tauto.
Qed.

Theorem word_store_loaded_scan_cached_exit entry bound flag live current source_after final :
  In cache stable -> cursor <> bound -> cursor <> flag -> bound <> flag ->
  ~In cursor live -> ~In bound live -> ~In flag live -> incl stable live -> In cache live ->
  statement_scope live (frontend_counted_loop row cache body) ->
  loaded_offset_cached_header pointer delta cache entry -> 0 <= count entry ->
  (entry_temps entry)!row = Some (Vint Int.zero) ->
  exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    (loaded_offset_loop row pointer delta body) E0 source_after final Out_normal ->
  temp_agree live (entry_temps entry) current ->
  exists after,
    exec_stmt fe (entry_ge entry) (entry_env entry) current (entry_memory entry)
      (word_store_loaded_scan_code cache cursor bound flag rename sites pointer) E0 after (entry_memory entry) Out_normal /\
    temp_agree live current after /\
    after!flag = Some (memory_boolean_word (word_store_loaded_scan_result cache cursor rename sites pointer entry)) /\
    (word_store_loaded_scan_result cache cursor rename sites pointer entry = true ->
      exists cached_after,
        exec_stmt fe (entry_ge entry) (entry_env entry) after (entry_memory entry)
          (frontend_counted_loop row cache body) E0 cached_after final Out_normal /\
        temp_agree live source_after cached_after).
Proof.
  intros CACHE_STABLE DISTINCT CURSOR_FLAG BOUND_FLAG CURSOR_LIVE BOUND_LIVE FLAG_LIVE STABLE_LIVE CACHE_LIVE
    SCOPE READY NONNEGATIVE ROW SOURCE FRAME.
  destruct (word_store_loaded_scan_from_source CACHE_STABLE DISTINCT CURSOR_FLAG BOUND_FLAG CURSOR_LIVE
    BOUND_LIVE FLAG_LIVE STABLE_LIVE CACHE_LIVE READY NONNEGATIVE ROW SOURCE FRAME)
    as [after [RUN [PUBLIC [RESULT CACHED]]]].
  exists after; split; [exact RUN|split; [exact PUBLIC|split; [exact RESULT|]]].
  intro ACCEPT; eapply structured_execution_temp_transport;
    [exact (CACHED ACCEPT)|exact word_store_loaded_cached_writes|exact SCOPE|].
  eapply temp_agree_trans; eassumption.
Qed.
End SCAN.

Print Assumptions word_store_loaded_scan_read_scope.
Print Assumptions word_store_loaded_point_preserved.
Print Assumptions word_store_loaded_point_runtime.
Print Assumptions word_store_loaded_scan_execution.
Print Assumptions word_store_loaded_scan_from_source.
Print Assumptions word_store_loaded_cached_writes.
Print Assumptions word_store_loaded_scan_cached_exit.
