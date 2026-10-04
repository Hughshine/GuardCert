From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Coqlib Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightTempFrame ClightCountedLoop ClightLoopSyntax
  ClightRedundantSet ClightRectangularGuard ClightRegionProgress ClightFrontendLoopProtocol ClightFrontendRegion ClightZeroTrip.
From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryRecursiveGuard GuardMemoryRecursiveWords
  GuardMemoryVectorBounds GuardMemoryTripleWords.
From GuardMemory Require Import GuardMemoryStartedFirstLeaf.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem memory_started_source_bound_words fe ge locals iterator bound body child cap temps memory after final :
  signed_range cap ->
  memory_nest_shapes (MemorySourceAxis iterator bound body child) ->
  memory_nest_fresh (MemorySourceAxis iterator bound body child) ->
  normal_statement (memory_nest_leaf child) = true -> quiet_statement (memory_nest_leaf child) = true ->
  writes_only [] (memory_nest_leaf child) ->
  exec_stmt fe ge locals temps memory (frontend_counted_loop iterator bound body) E0 after final Out_normal ->
  register_domain iterator (Entry ge locals temps memory) /\
  register_domain bound (Entry ge locals temps memory) /\
  (Int.signed (temp_word iterator temps) < Int.signed (temp_word bound temps) ->
    memory_recursive_bounds_domain cap (bound::memory_nest_bounds child) (Entry ge locals temps memory)).
Proof.
  intros CAP SHAPES FRESH NORMAL QUIET WRITES SOURCE.
  destruct (frontend_entry_test SOURCE) as [flag TEST].
  destruct (counter_test_domain TEST) as [word [upper [WORD LOOKUP]]].
  split; [exists word; exact WORD|].
  assert (BOUND : register_domain bound (Entry ge locals temps memory)) by (exists upper; exact LOOKUP).
  split; [exact BOUND|]; intro ACTIVE.
  cbn [memory_recursive_bounds_domain]; split; [exact BOUND|]; intro ACCEPT.
  destruct (memory_nest_fresh_child FRESH) as [CHILD_FRESH [ITERATOR_FRESH [BOUND_FRESH DISTINCT]]].
  destruct (@memory_frontend_active_body fe ge locals iterator bound body (memory_nest_iterators child)
    temps memory after final (@memory_nest_body_normal iterator bound body child SHAPES NORMAL QUIET)
    (@memory_nest_body_writes iterator bound body child SHAPES WRITES)
    ITERATOR_FRESH BOUND_FRESH ACTIVE SOURCE) as [next [target BODY]].
  pose proof (@memory_nest_child_decode fe ge locals body child temps memory next target (proj1 SHAPES) BODY) as CHILD.
  eapply memory_recursive_bounds_domain_frame.
  - apply memory_nest_child_frame; exact (proj2 CHILD_FRESH).
  - eapply memory_recursive_source_bound_words; [exact CAP|exact (proj2 SHAPES)|exact CHILD_FRESH|
      exact NORMAL|exact QUIET|exact WRITES|apply memory_nest_child_initial|exact CHILD].
Qed.

Corollary memory_started_source_vector_bounds fe ge locals iterator bound body child caps temps memory after final :
  length caps = length (bound::memory_nest_bounds child) -> Forall signed_range caps ->
  memory_nest_shapes (MemorySourceAxis iterator bound body child) ->
  memory_nest_fresh (MemorySourceAxis iterator bound body child) ->
  normal_statement (memory_nest_leaf child) = true -> quiet_statement (memory_nest_leaf child) = true ->
  writes_only [] (memory_nest_leaf child) ->
  exec_stmt fe ge locals temps memory (frontend_counted_loop iterator bound body) E0 after final Out_normal ->
  register_domain iterator (Entry ge locals temps memory) /\
  register_domain bound (Entry ge locals temps memory) /\
  (Int.signed (temp_word iterator temps) < Int.signed (temp_word bound temps) ->
    memory_vector_bounds_domain caps (bound::memory_nest_bounds child) (Entry ge locals temps memory)).
Proof.
  intros LENGTH CAPS SHAPES FRESH NORMAL QUIET WRITES SOURCE.
  assert (MAX : signed_range Int.max_signed) by (unfold signed_range; split; [change (-2147483648 <= 2147483647); lia|lia]).
  destruct (@memory_started_source_bound_words fe ge locals iterator bound body child Int.max_signed temps memory after final
    MAX SHAPES FRESH NORMAL QUIET WRITES SOURCE) as [ITERATOR [BOUND DOMAIN]].
  split; [exact ITERATOR|]; split; [exact BOUND|]; intro ACTIVE.
  eapply memory_vector_bounds_domain_from_uniform with (upper := Int.max_signed).
  - exact LENGTH.
  - eapply Forall_impl; [|exact CAPS]; intros cap SIGNED; split; [exact SIGNED|exact (proj2 SIGNED)].
  - exact MAX.
  - apply DOMAIN; exact ACTIVE.
Qed.
Print Assumptions memory_started_source_vector_bounds.
