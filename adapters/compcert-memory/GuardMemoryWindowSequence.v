From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightFiniteRegion ClightStraightLine ClightLoopSyntax ClightRegionProgress ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryNaryLoops GuardMemoryNarySequence
  GuardMemoryNaryCompute GuardMemoryNaryRanges GuardMemoryPointerCompute GuardMemoryPointerRegistry
  GuardMemoryPointerNaryAccess GuardMemoryPointerSourceAccess GuardMemoryNaryAffineAccess GuardMemoryAffineSourceExpressions GuardMemoryBufferOffsets.
From GuardMemory Require Import GuardMemoryMultiPointerCells GuardMemoryMultiPointerCompute GuardMemoryMultiPointerRegistry GuardMemorySourceParameters.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

From GuardMemory Require Import GuardMemoryMultiPointerSequence.
From GuardMemory Require Import GuardMemoryIntervalBox GuardMemoryWindowCompute GuardMemoryWindowRegistry GuardMemoryWindowCells.
Lemma window_sequence_tail_inverse bounds lower upper operations layout scalars fe ge locals valuation temps memory after final :
  Forall (window_compute_valid bounds lower upper layout scalars) operations ->
  interval_ranges bounds (map valuation layout) ->
  (forall identifier, In identifier (layout++scalars) -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  tail_execution fe ge locals (map memory_pointer_compute_statement operations) temps memory after final ->
  memory_multi_pointer_sequence_physical temps (map valuation (layout++scalars)) operations memory final /\ after = temps.
Proof.
  intros CERT RANGE; revert temps memory after final; induction CERT as [|operation operations HEAD CERT IH];
    intros temps memory after final WORDS RUN; cbn in RUN; inversion RUN; subst.
  - split; [constructor|reflexivity].
  - match goal with POINT : exec_stmt _ _ _ _ _ (memory_pointer_compute_statement _) _ _ _ _ |- _ =>
      destruct (@window_compute_inverse bounds lower upper layout scalars operation fe ge locals _ _ _ _ valuation
        HEAD RANGE WORDS POINT) as [ACT TEMPS]; subst end.
    match goal with TAIL : tail_execution _ _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ _ _ WORDS TAIL) as [REST EXIT] end.
    split; [econstructor; eauto|exact EXIT].
Qed.
Theorem window_sequence_point_execution bounds lower upper layout scalars temps coordinates values operations :
  Forall (window_compute_valid bounds lower upper layout scalars) operations -> interval_ranges bounds coordinates -> length coordinates = length layout ->
  forall before after,
    (memory_multi_pointer_sequence_physical temps (coordinates++values) operations before after <->
      memory_nary_sequence_point (map memory_nary_compute_instruction operations) (coordinates++values)
        (RuntimeState (window_multi_pointer_locations temps lower upper) before)
        (RuntimeState (window_multi_pointer_locations temps lower upper) after)).
Proof.
  intro CERT; induction CERT as [|operation operations HEAD CERT IH]; intros RANGE LENGTH before after;
    unfold memory_nary_sequence_point; cbn [map].
  - split; intro RUN; inversion RUN; subst; constructor.
  - split; intro RUN.
    + inversion RUN; subst.
      eapply Iter.IProgress with (st2 := RuntimeState (window_multi_pointer_locations temps lower upper) middle).
      * apply (proj1 (@window_compute_registry bounds lower upper layout scalars operation temps coordinates values before middle HEAD RANGE LENGTH)); assumption.
      * apply IH; assumption.
    + inversion RUN; subst.
      match goal with POINT : memory_nary_point _ _ _ ?middle |- _ =>
        destruct middle as [locations middle_memory];
        assert (LOCATIONS : locations = window_multi_pointer_locations temps lower upper)
          by (exact (@memory_nary_point_locations _ (coordinates++values) _ _ POINT)); subst locations end.
      eapply MultiPointerSequenceCons with (middle := middle_memory).
      * apply (proj2 (@window_compute_registry bounds lower upper layout scalars operation temps coordinates values before middle_memory HEAD RANGE LENGTH)); assumption.
      * apply IH; assumption.
Qed.
Theorem window_sequence_used_register bounds lower upper operations layout scalars fe ge locals identifier index :
  Forall (window_compute_valid bounds lower upper layout scalars) operations ->
  nth_error (layout++scalars) index = Some identifier ->
  forall temps memory after final,
  tail_execution fe ge locals (map memory_pointer_compute_statement operations) temps memory after final ->
  forall operation, In operation operations -> In index (memory_source_parameter_positions (memory_nary_compute_value operation)) ->
  exists word, temps ! identifier = Some (Vint word).
Proof.
  intros CERT LOOKUP; induction CERT as [|head operations HEAD CERT IH]; intros temps memory after final RUN operation MEMBER USED;
    [contradiction|].
  cbn in RUN; inversion RUN; subst.
  cbn in MEMBER; destruct MEMBER as [SAME|MEMBER].
  - subst operation; eapply window_compute_used_register; eassumption.
  - match goal with TAIL : tail_execution _ _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ _ _ TAIL operation MEMBER USED) as [word WORD] end.
    exists word.
    match goal with POINT : exec_stmt _ _ _ _ _ (memory_pointer_compute_statement head) _ _ _ _ |- _ =>
      pose proof (@writes_only_frame _ _ _ _ _ _ _ _ _ _ POINT [] ltac:(constructor) identifier ltac:(cbn; tauto)) as FRAME end.
    rewrite FRAME in WORD; exact WORD.
Qed.
Print Assumptions window_sequence_tail_inverse.
Print Assumptions window_sequence_point_execution.
Print Assumptions window_sequence_used_register.
