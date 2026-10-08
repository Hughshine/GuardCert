(** A fixed two-dimensional short-circuit Clight scan. The original loaded
    nest supplies each reached leaf, before cached-source execution is proved. *)
From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightNoWrap
  ClightPureExpr ClightLoopSyntax ClightCountedLoop ClightFrontendLoopProtocol ClightProjectedExecution.
From GuardMemory Require Import GuardMemoryBooleanScan.
From GuardInterface Require Import ClightLoadedOffsetHeader ClightNestedLoadedOffset ClightNestedExpressionCapture
  ClightNestedExpressionTransport ClightWordStoreSequence ClightWordStoreSequenceFactory
  ClightWordStoreNestedPrefix ClightWordStoreNestedRuntime ClightShortCircuitPrefixLoop.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition word_store_nested_inner_scan_code child_cache column_cursor column_limit flag rename sites pointer child_pointer :=
  Ssequence (Sset column_limit (Etempvar child_cache type_int32s))
    (Ssequence (Sset column_cursor (Econst_int Int.zero type_int32s))
      (short_circuit_prefix_loop column_cursor column_limit flag
        (word_store_nested_point_code rename sites pointer child_pointer flag))).
Definition word_store_nested_scan_code cache child_cache row_cursor row_limit column_cursor column_limit flag
  rename sites pointer child_pointer :=
  Ssequence (Sset row_limit (Etempvar cache type_int32s))
    (Ssequence (Sset flag (Econst_int Int.one type_int32s))
      (Ssequence (Sset row_cursor (Econst_int Int.zero type_int32s))
        (short_circuit_prefix_loop row_cursor row_limit flag
          (word_store_nested_inner_scan_code child_cache column_cursor column_limit flag rename sites pointer child_pointer)))).
Definition word_store_nested_inner_scan_result child_cache row_cursor column_cursor rename sites pointer child_pointer i entry :=
  memory_boolean_scan_result (fun j=>word_store_nested_point_result row_cursor column_cursor rename sites pointer child_pointer i j entry)
    0 (Z.to_nat(Int.signed(temp_word child_cache(entry_temps entry)))).
Definition word_store_nested_scan_result cache child_cache row_cursor column_cursor rename sites pointer child_pointer entry :=
  memory_boolean_scan_result
    (fun i=>word_store_nested_inner_scan_result child_cache row_cursor column_cursor rename sites pointer child_pointer i entry)
    0 (Z.to_nat(Int.signed(temp_word cache(entry_temps entry)))).

Lemma word_store_nested_controls_pairwise (row_cursor row_limit column_cursor column_limit flag : ident) :
  NoDup [row_cursor;row_limit;column_cursor;column_limit;flag] ->
  row_cursor<>row_limit /\ row_cursor<>column_cursor /\ row_cursor<>column_limit /\ row_cursor<>flag /\
  row_limit<>column_cursor /\ row_limit<>column_limit /\ row_limit<>flag /\
  column_cursor<>column_limit /\ column_cursor<>flag /\ column_limit<>flag.
Proof. intro UNIQUE; repeat rewrite NoDup_cons_iff in UNIQUE; cbn in UNIQUE; intuition congruence. Qed.

Section SCAN.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variables row cache pointer column child_cache child_pointer row_cursor row_limit column_cursor column_limit flag : ident.
Variables delta child_delta : int.
Variable body : statement.
Variable checked : checked_word_store_body body.
Variables stable live : list ident.
Variable rename : ident -> ident.
Hypotheses (POINTER_STABLE : In pointer stable) (CHILD_POINTER_STABLE : In child_pointer stable)
  (CACHE_STABLE : In cache stable) (CHILD_CACHE_STABLE : In child_cache stable)
  (ROW_PRIVATE : ~In row stable) (COLUMN_PRIVATE : ~In column stable) (ROW_COLUMN : row<>column)
  (STABLE_LIVE : incl stable live)
  (UNIQUE : NoDup [row_cursor;row_limit;column_cursor;column_limit;flag])
  (PRIVATE : forall id, In id [row_cursor;row_limit;column_cursor;column_limit;flag] -> ~In id live)
  (RENAME_ROW : rename row=row_cursor) (RENAME_COLUMN : rename column=column_cursor).
Hypothesis RENAME_STABLE : forall id, In id stable -> rename id=id.
Hypothesis SITE_POINTERS : forall site, In site (wsbody_sites checked) -> In (wss_pointer site) stable.
Hypothesis SITE_INDICES : forall site, In site (wsbody_sites checked) ->
  expression_scope (row::column::stable) (wss_index site).
Let sites := wsbody_sites checked.
Let ready := word_store_nested_ready pointer delta cache child_pointer child_delta child_cache.
Let outer i entry := word_store_nested_outer_prefix fe row cache pointer delta column child_cache child_pointer child_delta body stable i entry.
Let inner i j entry := word_store_nested_inner_prefix fe row cache pointer delta column child_cache child_pointer child_delta body stable i j entry.
Let root_count entry := Int.signed(temp_word cache(entry_temps entry)).
Let child_count entry := Int.signed(temp_word child_cache(entry_temps entry)).
Let point i j entry := word_store_nested_point_result row_cursor column_cursor rename sites pointer child_pointer i j entry.
Let inner_result i entry := word_store_nested_inner_scan_result child_cache row_cursor column_cursor rename sites pointer child_pointer i entry.
Let result entry := word_store_nested_scan_result cache child_cache row_cursor column_cursor rename sites pointer child_pointer entry.
Let keep := row_cursor::row_limit::live.

Lemma word_store_nested_row_cursor_private : ~In row_cursor stable.
Proof. intro MEMBER; eapply PRIVATE with (id:=row_cursor); [left; reflexivity|apply STABLE_LIVE; exact MEMBER]. Qed.
Lemma word_store_nested_column_cursor_private : ~In column_cursor stable.
Proof. intro MEMBER; eapply PRIVATE with (id:=column_cursor); [cbn; auto|apply STABLE_LIVE; exact MEMBER]. Qed.
Lemma word_store_nested_scan_cursors_distinct : row_cursor<>column_cursor.
Proof. exact(proj1(proj2(word_store_nested_controls_pairwise UNIQUE))). Qed.

Lemma word_store_nested_scan_next_inner i j entry :
  inner i j entry -> j<child_count entry -> point i j entry=true -> inner i(j+1) entry.
Proof.
  intros INV ACTIVE ACCEPT; eapply word_store_nested_inner_advance with (checked:=checked) (rename:=rename)
    (row_cursor:=row_cursor) (column_cursor:=column_cursor); try eassumption;
    try exact word_store_nested_row_cursor_private; try exact word_store_nested_column_cursor_private;
    try exact word_store_nested_scan_cursors_distinct.
Qed.

Theorem word_store_nested_inner_acceptance i entry :
  inner i 0 entry -> 0<=child_count entry -> inner_result i entry=true ->
  forall j, 0<=j<child_count entry -> inner i j entry /\ point i j entry=true.
Proof.
  intros INITIAL NONNEGATIVE ACCEPT.
  assert (TESTS : forall j, 0<=j<child_count entry -> point i j entry=true).
  { pose proof (proj1(@memory_boolean_scan_member (fun j=>point i j entry) 0
      (Z.to_nat(child_count entry))) ACCEPT) as CHECKS.
    intros j RANGE; apply CHECKS; rewrite Z2Nat.id by exact NONNEGATIVE; lia. }
  assert (INVARIANTS : forall n, Z.of_nat n<=child_count entry -> inner i(Z.of_nat n) entry).
  { induction n as [|n IH]; intro RANGE; [exact INITIAL|].
    rewrite Nat2Z.inj_succ; apply word_store_nested_scan_next_inner;
      [apply IH; lia|lia|apply TESTS; lia]. }
  intros j RANGE; split; [|apply TESTS; exact RANGE].
  rewrite <-(Z2Nat.id j (proj1 RANGE)); apply INVARIANTS; rewrite Z2Nat.id by exact(proj1 RANGE); lia.
Qed.

Lemma word_store_nested_scan_next_outer i entry :
  outer i entry -> i<root_count entry -> 0<=child_count entry -> inner_result i entry=true -> outer(i+1) entry.
Proof.
  intros INV ACTIVE NONNEGATIVE ACCEPT.
  assert (INITIAL : inner i 0 entry).
  { eapply word_store_nested_inner_open; try eassumption. }
  eapply word_store_nested_outer_advance with (checked:=checked) (rename:=rename)
    (row_cursor:=row_cursor) (column_cursor:=column_cursor); try eassumption;
    try exact word_store_nested_row_cursor_private; try exact word_store_nested_column_cursor_private;
    try exact word_store_nested_scan_cursors_distinct.
  exact(word_store_nested_inner_acceptance INITIAL NONNEGATIVE ACCEPT).
Qed.

Theorem word_store_nested_inner_scan_execution i entry current :
  inner i 0 entry -> 0<=child_count entry ->
  current!row_cursor=Some(Vint(Int.repr i)) -> current!flag=Some(memory_boolean_word true) ->
  temp_agree live(entry_temps entry) current ->
  exists after,
    exec_stmt fe(entry_ge entry)(entry_env entry) current(entry_memory entry)
      (word_store_nested_inner_scan_code child_cache column_cursor column_limit flag rename sites pointer child_pointer)
      E0 after(entry_memory entry) Out_normal /\ temp_agree keep current after /\
    after!flag=Some(memory_boolean_word(inner_result i entry)).
Proof.
  intros PREFIX NONNEGATIVE ROW FLAG FRAME; pose proof PREFIX as [READY REST].
  destruct (word_store_nested_controls_pairwise UNIQUE)
    as [RC_RL [RC_CC [RC_CL [RC_FLAG [RL_CC [RL_CL [RL_FLAG [CC_CL [CC_FLAG CL_FLAG]]]]]]]]].
  assert (CC_KEEP : ~In column_cursor keep).
  { unfold keep; intros [SAME|[SAME|MEMBER]]; [congruence|congruence|eapply PRIVATE with (id:=column_cursor); [cbn; auto|exact MEMBER]]. }
  assert (CL_KEEP : ~In column_limit keep).
  { unfold keep; intros [SAME|[SAME|MEMBER]]; [congruence|congruence|eapply PRIVATE with (id:=column_limit); [cbn; auto|exact MEMBER]]. }
  assert (FLAG_KEEP : ~In flag keep).
  { unfold keep; intros [SAME|[SAME|MEMBER]]; [congruence|congruence|eapply PRIVATE with (id:=flag); [cbn; tauto|exact MEMBER]]. }
  assert (CACHE_LIVE : In child_cache live) by (apply STABLE_LIVE; exact CHILD_CACHE_STABLE).
  assert (CACHE : (entry_temps entry)!child_cache=Some(Vint(temp_word child_cache(entry_temps entry)))).
  { destruct READY as [ROOT [block [offset [raw [PTR [READ CACHE]]]]]]; unfold temp_word; rewrite CACHE; reflexivity. }
  set (cached:=PTree.set column_limit (Vint(temp_word child_cache(entry_temps entry))) current).
  set (initialized:=PTree.set column_cursor(Vint Int.zero) cached).
  assert (INIT_FRAME : temp_agree keep current initialized).
  { eapply temp_agree_trans; apply temp_agree_set; assumption. }
  assert (BASE_FRAME : temp_agree keep current initialized) by exact INIT_FRAME.
  assert (INIT_CURSOR : initialized!column_cursor=Some(Vint(Int.repr 0))) by apply PTree.gss.
  assert (INIT_LIMIT : initialized!column_limit=Some(Vint(Int.repr(child_count entry)))).
  { unfold initialized,cached; rewrite PTree.gso by congruence; rewrite PTree.gss; unfold child_count; rewrite Int.repr_signed; reflexivity. }
  assert (INIT_FLAG : initialized!flag=Some(memory_boolean_word true)).
  { unfold initialized,cached; rewrite !PTree.gso by congruence; exact FLAG. }
  assert (ADVANCE : forall j, 0<=j<child_count entry -> inner i j entry -> point i j entry=true -> inner i(j+1) entry).
  { intros j RANGE INV ACCEPT; apply word_store_nested_scan_next_inner; [exact INV|exact(proj2 RANGE)|exact ACCEPT]. }
  assert (BODY : forall j current_temps, signed_range j -> 0<=j<child_count entry -> inner i j entry ->
    current_temps!column_cursor=Some(Vint(Int.repr j)) -> current_temps!column_limit=Some(Vint(Int.repr(child_count entry))) ->
    current_temps!flag=Some(memory_boolean_word true) -> temp_agree keep current current_temps ->
    exists after,
      exec_stmt fe(entry_ge entry)(entry_env entry) current_temps(entry_memory entry)
        (word_store_nested_point_code rename sites pointer child_pointer flag) E0 after(entry_memory entry) Out_normal /\
      temp_agree(column_cursor::column_limit::keep) current_temps after /\ after!flag=Some(memory_boolean_word(point i j entry))).
  { intros j current_temps INDEX ACTIVE INV COLUMN LIMIT FLAG' CURRENT_FRAME.
    exists(PTree.set flag(memory_boolean_word(point i j entry)) current_temps); split.
    - eapply word_store_nested_point_runtime with (checked:=checked) (stable:=stable)
        (row:=row) (cache:=cache) (column:=column) (child_cache:=child_cache) (delta:=delta) (child_delta:=child_delta);
        try eassumption; try exact(proj2 ACTIVE); try exact word_store_nested_row_cursor_private;
        try exact word_store_nested_column_cursor_private; try exact word_store_nested_scan_cursors_distinct.
      + rewrite CURRENT_FRAME by exact(or_introl eq_refl); exact ROW.
      + eapply temp_agree_trans; [eapply temp_agree_weaken; [exact STABLE_LIVE|exact FRAME]|].
        eapply temp_agree_weaken with (big:=keep); [intros id MEMBER; right; right; apply STABLE_LIVE; exact MEMBER|exact CURRENT_FRAME].
    - split; [apply temp_agree_set; cbn; intros [SAME|[SAME|MEMBER]]; [congruence|congruence|apply FLAG_KEEP; exact MEMBER]|apply PTree.gss]. }
  destruct (@short_circuit_prefix_loop_execution fe(entry_ge entry)(entry_env entry)(entry_memory entry)
    column_cursor column_limit flag (word_store_nested_point_code rename sites pointer child_pointer flag)
    keep current 0(child_count entry) (fun j=>inner i j entry) (fun j=>point i j entry)
    CC_CL CC_FLAG CL_FLAG CC_KEEP (Int.signed_range _) ADVANCE BODY (Z.to_nat(child_count entry)) 0 initialized)
    as [after [RUN [PUBLIC [RESULT ACCEPTED]]]].
  - rewrite Z2Nat.id by exact NONNEGATIVE; lia.
  - lia.
  - unfold signed_range; change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia.
  - exact PREFIX.
  - exact INIT_CURSOR.
  - exact INIT_LIMIT.
  - exact INIT_FLAG.
  - exact BASE_FRAME.
  - exists after; split.
    + unfold word_store_nested_inner_scan_code; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=cached)(m1:=entry_memory entry).
      * constructor; constructor; rewrite FRAME by exact CACHE_LIVE; exact CACHE.
      * eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=initialized)(m1:=entry_memory entry); [constructor; constructor|exact RUN].
    + split; [eapply temp_agree_trans; [exact INIT_FRAME|exact PUBLIC]|exact RESULT].
Qed.

Theorem word_store_nested_scan_execution entry current :
  outer 0 entry -> 0<=child_count entry -> temp_agree live(entry_temps entry) current ->
  exists after,
    exec_stmt fe(entry_ge entry)(entry_env entry) current(entry_memory entry)
      (word_store_nested_scan_code cache child_cache row_cursor row_limit column_cursor column_limit flag rename sites pointer child_pointer)
      E0 after(entry_memory entry) Out_normal /\ temp_agree live current after /\
    after!flag=Some(memory_boolean_word(result entry)) /\
    (result entry=true -> forall i j, 0<=i<root_count entry -> 0<=j<child_count entry ->
      inner i j entry /\ point i j entry=true).
Proof.
  intros PREFIX CHILD_NONNEGATIVE FRAME; pose proof PREFIX as [READY [CACHE [RANGE REST]]].
  change (0<=0<=root_count entry) in RANGE.
  assert (NONNEGATIVE : 0<=root_count entry) by lia.
  destruct (word_store_nested_controls_pairwise UNIQUE)
    as [RC_RL [RC_CC [RC_CL [RC_FLAG [RL_CC [RL_CL [RL_FLAG [CC_CL [CC_FLAG CL_FLAG]]]]]]]]].
  assert (RC_LIVE : ~In row_cursor live) by (apply PRIVATE; cbn; auto).
  assert (RL_LIVE : ~In row_limit live) by (apply PRIVATE; cbn; auto).
  assert (FLAG_LIVE : ~In flag live) by (apply PRIVATE; cbn; tauto).
  assert (CACHE_LIVE : In cache live) by (apply STABLE_LIVE; exact CACHE_STABLE).
  set(cached:=PTree.set row_limit(Vint(temp_word cache(entry_temps entry))) current).
  set(flagged:=PTree.set flag(Vint Int.one) cached).
  set(initialized:=PTree.set row_cursor(Vint Int.zero) flagged).
  assert(INIT_FRAME : temp_agree live current initialized).
  { eapply temp_agree_trans with(le1:=cached); [apply temp_agree_set; exact RL_LIVE|].
    eapply temp_agree_trans with(le1:=flagged); apply temp_agree_set; assumption. }
  assert(INIT_CURSOR : initialized!row_cursor=Some(Vint(Int.repr 0))) by apply PTree.gss.
  assert(INIT_LIMIT : initialized!row_limit=Some(Vint(Int.repr(root_count entry)))).
  { unfold initialized,flagged,cached; rewrite PTree.gso by congruence; rewrite PTree.gso by exact RL_FLAG;
      rewrite PTree.gss; unfold root_count; rewrite Int.repr_signed; reflexivity. }
  assert(INIT_FLAG : initialized!flag=Some(memory_boolean_word true)).
  { unfold initialized,flagged; rewrite PTree.gso by congruence; apply PTree.gss. }
  assert(ADVANCE : forall i, 0<=i<root_count entry -> outer i entry -> inner_result i entry=true -> outer(i+1) entry).
  { intros i ACTIVE_RANGE INV ACCEPT; apply word_store_nested_scan_next_outer; [exact INV|exact(proj2 ACTIVE_RANGE)|exact CHILD_NONNEGATIVE|exact ACCEPT]. }
  assert(BODY : forall i current_temps, signed_range i -> 0<=i<root_count entry -> outer i entry ->
    current_temps!row_cursor=Some(Vint(Int.repr i)) -> current_temps!row_limit=Some(Vint(Int.repr(root_count entry))) ->
    current_temps!flag=Some(memory_boolean_word true) -> temp_agree live(entry_temps entry) current_temps ->
    exists after,
      exec_stmt fe(entry_ge entry)(entry_env entry) current_temps(entry_memory entry)
        (word_store_nested_inner_scan_code child_cache column_cursor column_limit flag rename sites pointer child_pointer)
        E0 after(entry_memory entry) Out_normal /\ temp_agree keep current_temps after /\
      after!flag=Some(memory_boolean_word(inner_result i entry))).
  { intros i current_temps INDEX ACTIVE INV ROW LIMIT FLAG' CURRENT_FRAME.
    apply word_store_nested_inner_scan_execution; [|exact CHILD_NONNEGATIVE|exact ROW|exact FLAG'|exact CURRENT_FRAME].
    eapply word_store_nested_inner_open; try eassumption; exact(proj2 ACTIVE). }
  destruct (@short_circuit_prefix_loop_execution fe(entry_ge entry)(entry_env entry)(entry_memory entry)
    row_cursor row_limit flag (word_store_nested_inner_scan_code child_cache column_cursor column_limit flag rename sites pointer child_pointer)
    live(entry_temps entry) 0(root_count entry) (fun i=>outer i entry) (fun i=>inner_result i entry)
    RC_RL RC_FLAG RL_FLAG RC_LIVE (Int.signed_range _) ADVANCE BODY (Z.to_nat(root_count entry)) 0 initialized)
    as [after [RUN [PUBLIC [RESULT ACCEPTED]]]].
  - rewrite Z2Nat.id by exact NONNEGATIVE; lia.
  - lia.
  - unfold signed_range; change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia.
  - exact PREFIX.
  - exact INIT_CURSOR.
  - exact INIT_LIMIT.
  - exact INIT_FLAG.
  - eapply temp_agree_trans; eassumption.
  - exists after; split.
    + unfold word_store_nested_scan_code; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=cached)(m1:=entry_memory entry).
      * constructor; constructor; destruct CACHE as [word WORD]; rewrite FRAME by exact CACHE_LIVE;
          unfold temp_word; rewrite WORD; reflexivity.
      * eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=flagged)(m1:=entry_memory entry); [constructor; constructor|].
        eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=initialized)(m1:=entry_memory entry); [constructor; constructor|exact RUN].
    + split; [eapply temp_agree_trans; [exact INIT_FRAME|exact PUBLIC]|split; [exact RESULT|]].
      intros ACCEPT i j IR JR; destruct(ACCEPTED ACCEPT i IR) as [INV INNER_ACCEPT].
      apply word_store_nested_inner_acceptance; [|exact CHILD_NONNEGATIVE|exact INNER_ACCEPT|exact JR].
      eapply word_store_nested_inner_open; try eassumption; exact(proj2 IR).
Qed.
End SCAN.

Print Assumptions word_store_nested_controls_pairwise.
Print Assumptions word_store_nested_scan_next_inner.
Print Assumptions word_store_nested_inner_acceptance.
Print Assumptions word_store_nested_scan_next_outer.
Print Assumptions word_store_nested_inner_scan_execution.
Print Assumptions word_store_nested_scan_execution.
