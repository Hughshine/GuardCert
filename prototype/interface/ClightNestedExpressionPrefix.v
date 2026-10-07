From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightNoWrap
  ClightRedundantSet ClightLoopSyntax ClightLoopExecution ClightRegionProgress
  ClightStraightLine ClightRectangularLoops CompCertMemoryActions.
From GuardInterface Require Import ClightExpressionHeaderCapture ClightExpressionBodyPrefix ClightExpressionReachedPrefix
  ClightNestedExpressionCapture ClightNestedExpressionTransport ClightObservedHeaderPrefix ClightStorePermissions ClightStructuredStorePermissions
  ClightSignedExpressionProgress ClightStrictLoopProgress ClightStrictIteration.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition nested_expression_inner_entry row column i entry :=
  Entry (entry_ge entry) (entry_env entry)
    (PTree.set column (Vint Int.zero) (PTree.set row (Vint(Int.repr i)) (entry_temps entry)))
    (entry_memory entry).

(** Open a child prefix from an actual outer body, without requiring a model
    execution of that body. All observations keep the same global anchor. *)
Theorem nested_expression_prefix_open fe row cache bound column child_cache child_bound body
  stable ready observations entry i :
  typeof bound=type_int32s -> quiet_statement body=true ->
  ~In row stable -> ~In column stable -> row<>column -> In child_cache stable ->
  register_domain child_cache entry -> 0<=Int.signed(temp_word child_cache (entry_temps entry)) ->
  (forall current memory,
    current!row=Some(Vint(Int.repr i)) -> temp_agree stable (entry_temps entry) current ->
    header_observations_match (observations entry) memory ->
    eval_expr (entry_ge entry) (entry_env entry) current memory bound
      (Vint(temp_word cache (entry_temps entry)))) ->
  expression_body_prefix fe row cache bound (nested_expression_body column child_bound body)
    stable ready observations i entry -> i<Int.signed(temp_word cache (entry_temps entry)) ->
  expression_body_prefix fe column child_cache child_bound body (row::stable)
    (fun _=>ready entry) (fun _=>observations entry) 0 (nested_expression_inner_entry row column i entry).
Proof.
  intros TYPE QUIET ROW_FRESH COLUMN_FRESH DISTINCT CHILD_MEMBER CHILD_DOMAIN NONNEGATIVE HEADER
    [READY [CACHE [RANGE [INITIAL [current [memory [after [final [ROW [FRAME [OBSERVED [BACK SOURCE]]]]]]]]]]]] ACTIVE.
  assert (TEST : expression_test (signed_expression_test row bound) (Entry (entry_ge entry) (entry_env entry) current memory) true).
  { assert (FLAG : Int.lt (Int.repr i) (temp_word cache (entry_temps entry))=true).
    { unfold Int.lt; rewrite Int.signed_repr by
        (pose proof (Int.signed_range (temp_word cache (entry_temps entry))); change Int.min_signed with (-2147483648) in *; lia).
      destruct (zlt i (Int.signed(temp_word cache (entry_temps entry)))); [reflexivity|lia]. }
    rewrite <-FLAG; apply signed_expression_test_eval; [exact TYPE|exact ROW|apply HEADER; assumption]. }
  destruct (@strict_active_iteration fe (entry_ge entry) (entry_env entry) row (signed_expression_test row bound)
    (nested_expression_body column child_bound body) current memory after final
    (@nested_expression_body_normal column child_bound body QUIET)
    (@nested_expression_body_quiet column child_bound body QUIET) TEST SOURCE)
    as [body_after [body_final [next [next_memory [BODY REST]]]]].
  destruct (sequence_normal_decode BODY) as [reset [reset_memory [RESET CHILD]]].
  destruct (rectangle_reset_decode RESET) as [_ [TEMPS [MEMORY _]]]; subst reset reset_memory.
  assert (CHILD_CACHE_FRAME : (entry_temps (nested_expression_inner_entry row column i entry))!child_cache=(entry_temps entry)!child_cache).
  { cbn [nested_expression_inner_entry entry_temps]; rewrite !PTree.gso;
      try reflexivity; intro SAME; subst child_cache; contradiction. }
  eapply expression_body_prefix_reached with (current:=PTree.set column (Vint Int.zero) current)
    (memory:=memory) (after:=body_after) (final:=body_final).
  - exact READY.
  - destruct CHILD_DOMAIN as [word WORD]; exists word; rewrite CHILD_CACHE_FRAME; exact WORD.
  - unfold temp_word; rewrite CHILD_CACHE_FRAME; fold (temp_word child_cache (entry_temps entry)); lia.
  - exact INITIAL.
  - apply PTree.gss.
  - intros id [SAME|MEMBER].
    + subst id; cbn [nested_expression_inner_entry entry_temps]; rewrite !PTree.gso by congruence; rewrite PTree.gss; exact ROW.
    + cbn [nested_expression_inner_entry entry_temps]; rewrite !PTree.gso;
        try (intro SAME; subst id; contradiction); apply FRAME; exact MEMBER.
  - exact OBSERVED.
  - exact BACK.
  - exact CHILD.
Qed.

(** Close just the currently checked row. Checking future rows is not a
    premise: the inner checks establish the joint-observation preservation
    consumed by the existing outer-prefix advance service. *)
Theorem nested_expression_prefix_advance fe row cache bound column child_cache child_bound body stable written ready observations entry i :
  typeof bound=type_int32s -> typeof child_bound=type_int32s ->
  ~In row stable -> ~In column stable -> row<>column -> In child_cache stable ->
  normal_statement body=true -> quiet_statement body=true -> writes_only written body ->
  ~In row written -> ~In column written -> (forall id,In id stable -> ~In id written) ->
  (forall entry k current memory, ready entry -> 0<=k<=Int.signed(temp_word cache (entry_temps entry)) ->
    current!row=Some(Vint(Int.repr k)) -> temp_agree stable (entry_temps entry) current ->
    header_observations_match (observations entry) memory ->
    eval_expr (entry_ge entry) (entry_env entry) current memory bound (Vint(temp_word cache (entry_temps entry)))) ->
  register_domain child_cache entry -> 0<=Int.signed(temp_word child_cache (entry_temps entry)) ->
  (forall j current memory, 0<=j<=Int.signed(temp_word child_cache (entry_temps entry)) ->
    current!row=Some(Vint(Int.repr i)) -> current!column=Some(Vint(Int.repr j)) ->
    temp_agree stable (entry_temps entry) current -> header_observations_match (observations entry) memory ->
    eval_expr (entry_ge entry) (entry_env entry) current memory child_bound (Vint(temp_word child_cache (entry_temps entry)))) ->
  (forall j current memory after final, 0<=j<Int.signed(temp_word child_cache (entry_temps entry)) ->
    current!row=Some(Vint(Int.repr i)) -> current!column=Some(Vint(Int.repr j)) ->
    temp_agree stable (entry_temps entry) current -> header_observations_match (observations entry) memory ->
    exec_stmt fe (entry_ge entry) (entry_env entry) current memory body E0 after final Out_normal ->
    header_observations_match (observations entry) final) ->
  expression_body_prefix fe row cache bound (nested_expression_body column child_bound body)
    stable ready observations i entry -> i<Int.signed(temp_word cache (entry_temps entry)) ->
  expression_body_prefix fe row cache bound (nested_expression_body column child_bound body)
    stable ready observations (i+1) entry.
Proof.
  intros TYPE CHILD_TYPE ROW_FRESH COLUMN_FRESH DISTINCT CHILD_MEMBER NORMAL QUIET WRITES ROW_UNWRITTEN
    COLUMN_UNWRITTEN STABLE_UNWRITTEN HEADER CHILD_DOMAIN NONNEGATIVE CHILD_HEADER PRESERVE PREFIX ACTIVE.
  assert (BODY_WRITES : writes_only (column::written) (nested_expression_body column child_bound body)).
  { unfold nested_expression_body,rectangle_reset,strict_frontend_loop,counter_increment.
    constructor; [constructor; left; reflexivity|constructor; [constructor; [repeat constructor|]|constructor; [constructor|constructor; left; reflexivity]]].
    eapply writes_only_weaken; [|exact WRITES]; intros id MEMBER; right; exact MEMBER. }
  eapply expression_body_prefix_advance with (written:=column::written);
    [exact TYPE|exact ROW_FRESH|apply nested_expression_body_normal; exact QUIET|
     apply nested_expression_body_quiet; exact QUIET|exact BODY_WRITES| | | |exact HEADER|exact PREFIX|exact ACTIVE|].
  - cbn; intros [SAME|BAD]; [apply DISTINCT; symmetry; exact SAME|apply ROW_UNWRITTEN; exact BAD].
  - intros id MEMBER; cbn; intros [SAME|BAD]; [subst id; contradiction|apply (STABLE_UNWRITTEN id MEMBER); exact BAD].
  - intros ge locals current memory after final RUN; eapply structured_memory_accesses_back; [exact RUN|exact BODY_WRITES].
  - intros current memory after final ROW FRAME OBSERVED SOURCE.
    assert (CHILD_CACHE : (entry_temps entry)!child_cache=Some(Vint(temp_word child_cache (entry_temps entry)))).
    { destruct CHILD_DOMAIN as [word WORD]; unfold temp_word; rewrite WORD; reflexivity. }
    exact (proj2 (@nested_expression_row_cached fe (entry_ge entry) (entry_env entry) row column child_cache child_bound
      body stable written (entry_temps entry) (observations entry) (temp_word child_cache (entry_temps entry)) i current memory after final
      CHILD_TYPE CHILD_CACHE CHILD_MEMBER ROW_FRESH COLUMN_FRESH DISTINCT NORMAL QUIET WRITES ROW_UNWRITTEN COLUMN_UNWRITTEN
      STABLE_UNWRITTEN NONNEGATIVE CHILD_HEADER PRESERVE ROW FRAME OBSERVED SOURCE)).
Qed.

Print Assumptions nested_expression_prefix_open.
Print Assumptions nested_expression_prefix_advance.
