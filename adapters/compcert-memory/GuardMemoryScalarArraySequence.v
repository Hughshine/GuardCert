From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightFiniteRegion ClightStraightLine ClightLoopSyntax ClightRegionProgress
  ClightRectangularStore ClightRectangularGuard ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemorySequenceLoops
  GuardMemoryMultipleArrays GuardMemoryRegistryBackend GuardMemoryNamedRegistrySource GuardMemoryLayoutRegistry
  GuardMemoryNaryAffineExpressions GuardMemoryNaryAffineAccess GuardMemoryNaryAccessCheck
  GuardMemoryNarySourceValues GuardMemoryNaryCompute GuardMemoryNaryAnchors GuardMemoryNaryLoops
  GuardMemoryAccessAnchors GuardMemoryNaryRanges GuardMemoryNarySequence GuardMemoryScalarArrayCompute
  GuardMemoryScalarAccess GuardMemorySourceParameters.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_scalar_array_sequence_tail_inverse limits operations layout scalars fe ge locals valuation temps memory after final :
  Forall (memory_scalar_array_compute_valid limits layout scalars) operations ->
  memory_nary_ranges limits (map valuation layout) ->
  (forall identifier, In identifier (layout++scalars) -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  tail_execution fe ge locals (map memory_nary_compute_statement operations) temps memory after final ->
  memory_nary_compute_sequence_physical ge locals (map valuation (layout++scalars)) operations memory final /\ after = temps.
Proof.
  intros CERT RANGE; revert temps memory after final; induction CERT as [|operation operations HEAD CERT IH];
    intros temps memory after final WORDS RUN; cbn in RUN; inversion RUN; subst.
  - split; [constructor|reflexivity].
  - match goal with POINT : exec_stmt _ _ _ _ _ (memory_nary_compute_statement _) _ _ _ _ |- _ =>
      destruct (@memory_scalar_array_compute_inverse limits layout scalars operation fe ge locals temps memory _ _ valuation
        HEAD RANGE WORDS POINT) as [ACT TEMPS]; subst end.
    match goal with TAIL : tail_execution _ _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ _ _ WORDS TAIL) as [REST EXIT] end.
    split; [econstructor; eauto|exact EXIT].
Qed.

Theorem memory_scalar_array_sequence_used_register limits operations layout scalars fe ge locals identifier index :
  Forall (memory_scalar_array_compute_valid limits layout scalars) operations ->
  nth_error (layout++scalars) index = Some identifier ->
  forall temps memory after final,
  tail_execution fe ge locals (map memory_nary_compute_statement operations) temps memory after final ->
  forall operation, In operation operations -> In index (memory_source_parameter_positions (memory_nary_compute_value operation)) ->
  exists word, temps ! identifier = Some (Vint word).
Proof.
  intros CERT LOOKUP; induction CERT as [|head operations HEAD CERT IH]; intros temps memory after final RUN operation MEMBER USED;
    [contradiction|].
  cbn in RUN; inversion RUN; subst.
  cbn in MEMBER; destruct MEMBER as [SAME|MEMBER].
  - subst operation; eapply memory_scalar_array_used_register; eassumption.
  - match goal with TAIL : tail_execution _ _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ _ _ TAIL operation MEMBER USED) as [word WORD] end.
    exists word.
    match goal with POINT : exec_stmt _ _ _ _ _ (memory_nary_compute_statement head) _ _ _ _ |- _ =>
      pose proof (@writes_only_frame _ _ _ _ _ _ _ _ _ _ POINT [] ltac:(constructor) identifier ltac:(cbn; tauto)) as FRAME end.
    rewrite FRAME in WORD; exact WORD.
Qed.

Theorem memory_scalar_array_sequence_point_execution limits layout scalars descriptors entries ge locals coordinates values operations :
  Forall2 (memory_descriptor_binding ge locals) descriptors entries -> NoDup (map memory_array_id entries) ->
  Forall (fun operation => memory_descriptors_cover descriptors (memory_nary_compute_requests operation)) operations ->
  Forall (memory_scalar_array_compute_valid limits layout scalars) operations ->
  memory_nary_ranges limits coordinates -> length coordinates = length layout -> forall before after,
    (memory_nary_compute_sequence_physical ge locals (coordinates++values) operations before after <->
      memory_nary_sequence_point (map memory_nary_compute_instruction operations) (coordinates++values)
        (RuntimeState (memory_array_registry entries) before) (RuntimeState (memory_array_registry entries) after)).
Proof.
  intros ARRAYS UNIQUE COVERS; induction COVERS as [|operation operations COVER COVERS IH];
    intros CERT RANGE LENGTH before after; unfold memory_nary_sequence_point; cbn [map].
  - split; intro RUN; inversion RUN; subst; constructor.
  - inversion CERT as [|head tail HEAD REST]; subst.
    assert (WBOUND : 0 <= memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation)) (coordinates++values) <
      rectangle_extent (memory_nary_access_shape (memory_nary_compute_write operation))).
    { destruct HEAD as [[_ [ENCODE BOUND]] _]; rewrite memory_scalar_index_value.
      - apply BOUND; exact RANGE.
      - rewrite (@memory_encode_nary_index_length layout _ _ ENCODE),LENGTH; reflexivity. }
    assert (RBOUNDS : Forall (fun access => 0 <= memory_nary_index_value (memory_nary_access_index access) (coordinates++values) <
      rectangle_extent (memory_nary_access_shape access)) (memory_nary_compute_reads operation)).
    { destruct HEAD as [_ [READS _]]; eapply Forall_impl; [|exact READS]; intros access [_ [ENCODE BOUND]].
      rewrite memory_scalar_index_value.
      - apply BOUND; exact RANGE.
      - rewrite (@memory_encode_nary_index_length layout _ _ ENCODE),LENGTH; reflexivity. }
    split; intro RUN.
    + inversion RUN; subst.
      eapply Iter.IProgress with (st2 := RuntimeState (memory_array_registry entries) middle).
      * apply (proj1 (@memory_nary_compute_registry descriptors entries ge locals (coordinates++values) operation before middle
          ARRAYS UNIQUE COVER WBOUND RBOUNDS)); assumption.
      * apply IH; assumption.
    + inversion RUN; subst.
      match goal with POINT : memory_nary_point _ _ _ ?middle |- _ =>
        destruct middle as [locations middle_memory];
        assert (LOCATIONS : locations = memory_array_registry entries)
          by (exact (@memory_nary_point_locations _ (coordinates++values) _ _ POINT)); subst locations end.
      eapply NaryComputeSequenceCons with (middle := middle_memory).
      * apply (proj2 (@memory_nary_compute_registry descriptors entries ge locals (coordinates++values) operation before middle_memory
          ARRAYS UNIQUE COVER WBOUND RBOUNDS)); assumption.
      * apply IH; assumption.
Qed.
Print Assumptions memory_scalar_array_sequence_tail_inverse.
Print Assumptions memory_scalar_array_sequence_used_register.
Print Assumptions memory_scalar_array_sequence_point_execution.
