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

Inductive memory_multi_pointer_sequence_physical temps values : list memory_nary_compute -> Mem.mem -> Mem.mem -> Prop :=
| MultiPointerSequenceNil memory : memory_multi_pointer_sequence_physical temps values [] memory memory
| MultiPointerSequenceCons operation operations before middle after :
    memory_multi_pointer_compute_physical temps values operation before middle ->
    memory_multi_pointer_sequence_physical temps values operations middle after ->
    memory_multi_pointer_sequence_physical temps values (operation::operations) before after.


Lemma memory_multi_pointer_sequence_tail_inverse limits operations layout scalars extent fe ge locals valuation temps memory after final :
  Forall (memory_multi_pointer_compute_valid limits layout scalars extent) operations ->
  memory_nary_ranges limits (map valuation layout) ->
  (forall identifier, In identifier (layout++scalars) -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  tail_execution fe ge locals (map memory_pointer_compute_statement operations) temps memory after final ->
  memory_multi_pointer_sequence_physical temps (map valuation (layout++scalars)) operations memory final /\ after = temps.
Proof.
  intros CERT RANGE; revert temps memory after final; induction CERT as [|operation operations HEAD CERT IH];
    intros temps memory after final WORDS RUN; cbn in RUN; inversion RUN; subst.
  - split; [constructor|reflexivity].
  - match goal with POINT : exec_stmt _ _ _ _ _ (memory_pointer_compute_statement _) _ _ _ _ |- _ =>
      destruct (@memory_multi_pointer_compute_inverse limits layout scalars extent operation fe ge locals _ _ _ _ valuation
        HEAD RANGE WORDS POINT) as [ACT TEMPS]; subst end.
    match goal with TAIL : tail_execution _ _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ _ _ WORDS TAIL) as [REST EXIT] end.
    split; [econstructor; eauto|exact EXIT].
Qed.
Theorem memory_multi_pointer_sequence_point_execution limits layout scalars extent temps coordinates values operations :
  Forall (memory_multi_pointer_compute_valid limits layout scalars extent) operations -> memory_nary_ranges limits coordinates -> length coordinates = length layout ->
  forall before after,
    (memory_multi_pointer_sequence_physical temps (coordinates++values) operations before after <->
      memory_nary_sequence_point (map memory_nary_compute_instruction operations) (coordinates++values)
        (RuntimeState (memory_multi_pointer_locations temps extent) before)
        (RuntimeState (memory_multi_pointer_locations temps extent) after)).
Proof.
  intro CERT; induction CERT as [|operation operations HEAD CERT IH]; intros RANGE LENGTH before after;
    unfold memory_nary_sequence_point; cbn [map].
  - split; intro RUN; inversion RUN; subst; constructor.
  - split; intro RUN.
    + inversion RUN; subst.
      eapply Iter.IProgress with (st2 := RuntimeState (memory_multi_pointer_locations temps extent) middle).
      * apply (proj1 (@memory_multi_pointer_compute_registry limits layout scalars extent operation temps coordinates values before middle HEAD RANGE LENGTH)); assumption.
      * apply IH; assumption.
    + inversion RUN; subst.
      match goal with POINT : memory_nary_point _ _ _ ?middle |- _ =>
        destruct middle as [locations middle_memory];
        assert (LOCATIONS : locations = memory_multi_pointer_locations temps extent)
          by (exact (@memory_nary_point_locations _ (coordinates++values) _ _ POINT)); subst locations end.
      eapply MultiPointerSequenceCons with (middle := middle_memory).
      * apply (proj2 (@memory_multi_pointer_compute_registry limits layout scalars extent operation temps coordinates values before middle_memory HEAD RANGE LENGTH)); assumption.
      * apply IH; assumption.
Qed.
Theorem memory_multi_pointer_sequence_used_register limits operations layout scalars extent fe ge locals identifier index :
  Forall (memory_multi_pointer_compute_valid limits layout scalars extent) operations ->
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
  - subst operation; eapply memory_multi_pointer_used_register; eassumption.
  - match goal with TAIL : tail_execution _ _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ _ _ TAIL operation MEMBER USED) as [word WORD] end.
    exists word.
    match goal with POINT : exec_stmt _ _ _ _ _ (memory_pointer_compute_statement head) _ _ _ _ |- _ =>
      pose proof (@writes_only_frame _ _ _ _ _ _ _ _ _ _ POINT [] ltac:(constructor) identifier ltac:(cbn; tauto)) as FRAME end.
    rewrite FRAME in WORD; exact WORD.
Qed.
Print Assumptions memory_multi_pointer_sequence_tail_inverse.
Print Assumptions memory_multi_pointer_sequence_point_execution.
Print Assumptions memory_multi_pointer_sequence_used_register.
