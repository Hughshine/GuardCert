From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Coqlib Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCountedLoop ClightTempFrame ClightLoopSyntax ClightRegionProgress
  ClightNoWrap ClightCondition ClightPureExpr ClightCountedProtocol ClightFrontendLoopProtocol
  ClightFrontendRegion ClightLoopExecution ClightZeroTrip ClightStraightLine ClightFramedLoop.
From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryRecursiveFirstLeaf
  GuardMemoryTripleWords.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_frontend_active_body fe ge locals iterator bound body written temps memory after final :
  normal_statement body = true -> writes_only written body ->
  ~ In iterator written -> ~ In bound written ->
  Int.signed (temp_word iterator temps) < Int.signed (temp_word bound temps) ->
  exec_stmt fe ge locals temps memory (frontend_counted_loop iterator bound body) E0 after final Out_normal ->
  exists next target, exec_stmt fe ge locals temps memory body E0 next target Out_normal.
Proof.
  intros NORMAL WRITES ITERATOR BOUND ACTIVE SOURCE.
  destruct (frontend_entry_test SOURCE) as [flag TEST].
  destruct (counter_test_domain TEST) as [word [upper [WORD LOOKUP]]].
  cbn [entry_temps] in WORD,LOOKUP.
  unfold temp_word in ACTIVE; rewrite WORD,LOOKUP in ACTIVE.
  assert (TRUE : expression_test (counter_condition iterator bound) (Entry ge locals temps memory) true).
  { replace true with (Int.signed word <? Int.signed upper) by (apply Z.ltb_lt; exact ACTIVE).
    apply (@counter_condition_at ge locals temps memory iterator bound (Int.signed word) (Int.signed upper)).
    - intro SAME; subst bound; rewrite WORD in LOOKUP; inversion LOOKUP; subst; lia.
    - rewrite Int.repr_signed; exact WORD.
    - rewrite Int.repr_signed; exact LOOKUP.
    - apply Int.signed_range.
    - apply Int.signed_range. }
  destruct (@frontend_iteration_decode fe ge locals temps memory iterator bound body after final TRUE
    (@normal_statement_execution fe ge locals body NORMAL)
    ltac:(intros; eapply structured_temp_frame; [exact WRITES|cbn; intuition congruence|eassumption]) SOURCE)
    as [next [target [BODY REST]]].
  exists next,target; exact BODY.
Qed.

Theorem memory_started_first_leaf fe ge locals iterator bound body child :
  memory_nest_shapes (MemorySourceAxis iterator bound body child) ->
  memory_nest_fresh (MemorySourceAxis iterator bound body child) ->
  normal_statement (memory_nest_leaf child) = true -> quiet_statement (memory_nest_leaf child) = true ->
  writes_only [] (memory_nest_leaf child) ->
  forall protected temps memory after final,
    (forall identifier, In identifier (memory_nest_iterators (MemorySourceAxis iterator bound body child)) ->
      ~ In identifier protected) ->
    Forall (fun key => 0 < Int.signed (temp_word key temps)) (memory_nest_bounds child) ->
    Int.signed (temp_word iterator temps) < Int.signed (temp_word bound temps) ->
    exec_stmt fe ge locals temps memory (frontend_counted_loop iterator bound body) E0 after final Out_normal ->
    exists leaf_temps leaf_after leaf_final, temp_agree protected temps leaf_temps /\
      exec_stmt fe ge locals leaf_temps memory (memory_nest_leaf child) E0 leaf_after leaf_final Out_normal.
Proof.
  intros SHAPES FRESH NORMAL QUIET WRITES protected temps memory after final PROTECTED POSITIVE ACTIVE SOURCE.
  destruct (memory_nest_fresh_child FRESH) as [CHILD_FRESH [ITERATOR_FRESH [BOUND_FRESH DISTINCT]]].
  destruct (@memory_frontend_active_body fe ge locals iterator bound body (memory_nest_iterators child)
    temps memory after final (@memory_nest_body_normal iterator bound body child SHAPES NORMAL QUIET)
    (@memory_nest_body_writes iterator bound body child SHAPES WRITES)
    ITERATOR_FRESH BOUND_FRESH ACTIVE SOURCE) as [next [target BODY]].
  pose proof (@memory_nest_child_decode fe ge locals body child temps memory next target (proj1 SHAPES) BODY) as CHILD.
  assert (CHILD_PROTECTED : forall identifier, In identifier (memory_nest_iterators child) -> ~ In identifier protected).
  { intros identifier MEMBER; apply PROTECTED; cbn; auto. }
  assert (CHILD_POSITIVE : Forall (fun key => 0 < Int.signed (temp_word key (memory_nest_child_temps child temps)))
    (memory_nest_bounds child)).
  { rewrite Forall_forall in POSITIVE |- *; intros key MEMBER.
    pose proof (@memory_nest_child_frame child temps (memory_nest_bounds child) (proj2 CHILD_FRESH)) as FRAME.
    unfold temp_word; rewrite (FRAME key MEMBER); apply POSITIVE; exact MEMBER. }
  destruct (@memory_recursive_first_leaf fe ge locals child (proj2 SHAPES) CHILD_FRESH NORMAL QUIET WRITES protected
    (memory_nest_child_temps child temps) memory next target CHILD_PROTECTED CHILD_POSITIVE
    (memory_nest_child_initial child temps) CHILD) as [leaf_temps [leaf_after [leaf_final [FRAME RUN]]]].
  exists leaf_temps,leaf_after,leaf_final; split; [|exact RUN].
  eapply temp_agree_trans; [apply memory_nest_child_frame; exact CHILD_PROTECTED|exact FRAME].
Qed.
Print Assumptions memory_started_first_leaf.
