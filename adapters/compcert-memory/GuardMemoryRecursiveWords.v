From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightTempFrame ClightCountedLoop ClightLoopSyntax
  ClightRedundantSet ClightRectangularGuard ClightRegionProgress ClightFrontendLoopProtocol ClightFrontendRegion ClightZeroTrip.
From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryRecursiveGuard GuardMemoryTripleWords.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_recursive_bounds_domain_frame cap bounds ge locals first second memory :
  temp_agree bounds first second ->
  memory_recursive_bounds_domain cap bounds (Entry ge locals second memory) ->
  memory_recursive_bounds_domain cap bounds (Entry ge locals first memory).
Proof.
  induction bounds as [|bound bounds IH]; cbn [memory_recursive_bounds_domain]; intros FRAME DOMAIN; [exact I|].
  destruct DOMAIN as [[word WORD] REST]; split.
  - exists word; cbn [entry_temps] in *; rewrite <- (FRAME bound ltac:(cbn; auto)); exact WORD.
  - intro ACCEPT; apply IH.
    + intros identifier MEMBER; apply FRAME; cbn; auto.
    + apply REST; unfold register_range_flag,register_positive,register_at_most,temp_word in *; cbn [entry_temps] in *.
      rewrite (FRAME bound ltac:(cbn; auto)); exact ACCEPT.
Qed.
Theorem memory_recursive_source_bound_words fe ge locals nest cap : signed_range cap ->
  memory_nest_shapes nest -> memory_nest_fresh nest ->
  normal_statement (memory_nest_leaf nest) = true -> quiet_statement (memory_nest_leaf nest) = true ->
  writes_only [] (memory_nest_leaf nest) ->
  forall temps memory after final, memory_nest_initial nest temps ->
  exec_stmt fe ge locals temps memory (memory_nest_source nest) E0 after final Out_normal ->
  memory_recursive_bounds_domain cap (memory_nest_bounds nest) (Entry ge locals temps memory).
Proof.
  intro CAP; induction nest as [code|iterator bound body child IH];
    intros SHAPES FRESH NORMAL QUIET WRITES temps memory after final INITIAL SOURCE; [exact I|].
  destruct (memory_nest_fresh_child FRESH) as [CHILD_FRESH [ITERATOR_FRESH [BOUND_FRESH DISTINCT]]].
  destruct (frontend_entry_test SOURCE) as [flag TEST]; destruct (counter_test_domain TEST) as [word [upper [WORD LOOKUP]]].
  assert (BOUND : register_domain bound (Entry ge locals temps memory)) by (exists upper; exact LOOKUP).
  cbn [memory_recursive_bounds_domain memory_nest_bounds]; split; [exact BOUND|]; intro ACCEPT.
  pose proof (register_range_sound CAP BOUND ACCEPT) as [_ RANGE].
  destruct (@memory_frontend_positive_body fe ge locals iterator bound body (memory_nest_iterators child)
    temps memory after final (@memory_nest_body_normal iterator bound body child SHAPES NORMAL QUIET)
    (@memory_nest_body_writes iterator bound body child SHAPES WRITES)
    ITERATOR_FRESH BOUND_FRESH INITIAL (proj1 RANGE) SOURCE) as [next [target BODY]].
  pose proof (@memory_nest_child_decode fe ge locals body child temps memory next target (proj1 SHAPES) BODY) as CHILD.
  eapply memory_recursive_bounds_domain_frame.
  - apply memory_nest_child_frame; exact (proj2 CHILD_FRESH).
  - eapply IH; [exact (proj2 SHAPES)|exact CHILD_FRESH|exact NORMAL|exact QUIET|exact WRITES|
      apply memory_nest_child_initial|exact CHILD].
Qed.
Theorem memory_recursive_source_iterator_word fe ge locals iterator bound body child temps memory after final :
  exec_stmt fe ge locals temps memory (memory_nest_source (MemorySourceAxis iterator bound body child)) E0 after final Out_normal ->
  register_domain iterator (Entry ge locals temps memory).
Proof.
  intro SOURCE; destruct (frontend_entry_test SOURCE) as [flag TEST].
  destruct (counter_test_domain TEST) as [word [upper [WORD LOOKUP]]]; exists word; exact WORD.
Qed.
Print Assumptions memory_recursive_source_bound_words.
