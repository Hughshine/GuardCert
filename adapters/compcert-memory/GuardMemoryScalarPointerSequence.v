From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightFiniteRegion ClightStraightLine ClightLoopSyntax ClightRegionProgress ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryNaryLoops GuardMemoryNarySequence
  GuardMemoryNaryCompute GuardMemoryNaryRanges GuardMemoryPointerCompute GuardMemoryPointerRegistry
  GuardMemoryPointerNaryAccess GuardMemoryPointerSourceAccess GuardMemoryNaryAffineAccess GuardMemoryAffineSourceExpressions GuardMemoryBufferOffsets.
From GuardMemory Require Import GuardMemoryPointerSequence GuardMemoryScalarPointerCompute GuardMemoryScalarPointerRegistry GuardMemorySourceParameters.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_scalar_pointer_sequence_tail_inverse limits operations layout scalars pointer extent fe ge locals valuation temps memory after final block base :
  Forall (memory_scalar_pointer_compute_valid limits layout scalars pointer extent) operations ->
  memory_nary_ranges limits (map valuation layout) ->
  (forall identifier, In identifier (layout++scalars) -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  temps ! pointer = Some (Vptr block base) ->
  tail_execution fe ge locals (map memory_pointer_compute_statement operations) temps memory after final ->
  memory_pointer_sequence_physical block base (map valuation (layout++scalars)) operations memory final /\ after = temps.
Proof.
  intros CERT RANGE; revert temps memory after final; induction CERT as [|operation operations HEAD CERT IH];
    intros temps memory after final WORDS POINTER RUN; cbn in RUN; inversion RUN; subst.
  - split; [constructor|reflexivity].
  - match goal with POINT : exec_stmt _ _ _ _ _ (memory_pointer_compute_statement _) _ _ _ _ |- _ =>
      destruct (@memory_scalar_pointer_compute_inverse limits layout scalars pointer extent operation fe ge locals _ _ _ _ valuation block base
        HEAD RANGE WORDS POINTER POINT) as [ACT TEMPS]; subst end.
    match goal with TAIL : tail_execution _ _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ _ _ WORDS POINTER TAIL) as [REST EXIT] end.
    split; [econstructor; eauto|exact EXIT].
Qed.
Theorem memory_scalar_pointer_sequence_point_execution limits layout scalars pointer extent block base coordinates values operations :
  Forall (memory_scalar_pointer_compute_valid limits layout scalars pointer extent) operations -> memory_nary_ranges limits coordinates -> length coordinates = length layout ->
  forall before after,
    (memory_pointer_sequence_physical block base (coordinates++values) operations before after <->
      memory_nary_sequence_point (map memory_nary_compute_instruction operations) (coordinates++values)
        (RuntimeState (memory_pointer_buffer_locations pointer block base extent) before)
        (RuntimeState (memory_pointer_buffer_locations pointer block base extent) after)).
Proof.
  intro CERT; induction CERT as [|operation operations HEAD CERT IH]; intros RANGE LENGTH before after;
    unfold memory_nary_sequence_point; cbn [map].
  - split; intro RUN; inversion RUN; subst; constructor.
  - split; intro RUN.
    + inversion RUN; subst.
      eapply Iter.IProgress with (st2 := RuntimeState (memory_pointer_buffer_locations pointer block base extent) middle).
      * apply (proj1 (@memory_scalar_pointer_compute_registry limits layout scalars pointer extent operation block base coordinates values before middle HEAD RANGE LENGTH)); assumption.
      * apply IH; assumption.
    + inversion RUN; subst.
      match goal with POINT : memory_nary_point _ _ _ ?middle |- _ =>
        destruct middle as [locations middle_memory];
        assert (LOCATIONS : locations = memory_pointer_buffer_locations pointer block base extent)
          by (exact (@memory_nary_point_locations _ (coordinates++values) _ _ POINT)); subst locations end.
      eapply PointerSequenceCons with (middle := middle_memory).
      * apply (proj2 (@memory_scalar_pointer_compute_registry limits layout scalars pointer extent operation block base coordinates values before middle_memory HEAD RANGE LENGTH)); assumption.
      * apply IH; assumption.
Qed.
Theorem memory_scalar_pointer_sequence_used_register limits operations layout scalars pointer extent fe ge locals identifier index :
  Forall (memory_scalar_pointer_compute_valid limits layout scalars pointer extent) operations ->
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
  - subst operation; eapply memory_scalar_pointer_used_register; eassumption.
  - match goal with TAIL : tail_execution _ _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ _ _ TAIL operation MEMBER USED) as [word WORD] end.
    exists word.
    match goal with POINT : exec_stmt _ _ _ _ _ (memory_pointer_compute_statement head) _ _ _ _ |- _ =>
      pose proof (@writes_only_frame _ _ _ _ _ _ _ _ _ _ POINT [] ltac:(constructor) identifier ltac:(cbn; tauto)) as FRAME end.
    rewrite FRAME in WORD; exact WORD.
Qed.
Print Assumptions memory_scalar_pointer_sequence_tail_inverse.
Print Assumptions memory_scalar_pointer_sequence_point_execution.
Print Assumptions memory_scalar_pointer_sequence_used_register.
