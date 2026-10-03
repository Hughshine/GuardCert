From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightFiniteRegion ClightStraightLine ClightRectangularStore ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemorySequenceLoops GuardMemoryMultipleArrays
  GuardMemoryRegistryBackend GuardMemoryParametricBody GuardMemoryLayoutRegistry GuardMemoryGeneralLayoutOperations
  GuardMemoryGeneralLayoutSequence GuardMemoryAccessAnchors GuardMemoryOffsetAccessRanges.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Lemma memory_offset_sequence_tail_inverse base operations row column fe ge locals i j temps memory after final :
  rectangle_layout_valid base -> row <> column -> Forall (memory_offset_operation_valid base row column) operations ->
  0 <= i < rectangle_outer_limit base -> 0 <= j < rectangle_stride base ->
  temps ! row = Some (Vint (Int.repr i)) -> temps ! column = Some (Vint (Int.repr j)) ->
  tail_execution fe ge locals (map (memory_general_layout_statement row column) operations) temps memory after final ->
  memory_general_operations_physical ge locals i j operations memory final /\ after = temps.
Proof.
  intros VALID DISTINCT CERT I J; revert temps memory after final; induction CERT as [|operation operations HEAD CERT IH];
    intros temps memory after final ROW COLUMN RUN; cbn in RUN; inversion RUN; subst.
  - split; [constructor|reflexivity].
  - match goal with POINT : exec_stmt _ _ _ _ _ (memory_general_layout_statement _ _ _) _ _ _ _ |- _ =>
      destruct (@memory_offset_operation_inverse base row column operation fe ge locals temps memory _ _ i j
        VALID DISTINCT HEAD I J ROW COLUMN POINT) as [ACT TEMPS]; subst end.
    match goal with TAIL : tail_execution _ _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ _ _ ROW COLUMN TAIL) as [REST EXIT] end.
    split; [econstructor; eauto|exact EXIT].
Qed.
Theorem memory_offset_sequence_point_execution base row column descriptors entries ge locals i j operations :
  rectangle_layout_valid base -> Forall2 (memory_descriptor_binding ge locals) descriptors entries ->
  NoDup (map memory_array_id entries) ->
  Forall (fun operation => memory_descriptors_cover descriptors (memory_general_layout_requests operation)) operations ->
  Forall (memory_offset_operation_valid base row column) operations ->
  0 <= i < rectangle_outer_limit base -> 0 <= j < rectangle_stride base ->
  forall before after,
    (memory_general_operations_physical ge locals i j operations before after <->
      memory_sequence_point (map memory_general_layout_instruction operations) i j
        (RuntimeState (memory_array_registry entries) before) (RuntimeState (memory_array_registry entries) after)).
Proof.
  intros VALID ARRAYS UNIQUE COVERS; induction COVERS as [|operation operations COVER COVERS IH];
    intros CERT I J before after; unfold memory_sequence_point; cbn [map].
  - split; intro RUN; inversion RUN; subst; constructor.
  - inversion CERT as [|head tail HEAD REST]; subst.
    split; intro RUN.
    + inversion RUN; subst.
      eapply Iter.IProgress with (st2 := RuntimeState (memory_array_registry entries) middle).
      * apply (proj1 (@memory_offset_operation_registry_execution base row column descriptors entries ge locals operation i j before middle
          VALID ARRAYS COVER UNIQUE HEAD I J)); assumption.
      * apply IH; assumption.
    + inversion RUN; subst.
      match goal with POINT : memory_point _ _ _ _ ?middle |- _ =>
        destruct middle as [locations middle_memory];
        assert (LOCATIONS : locations = memory_array_registry entries)
          by (exact (@memory_point_locations _ i j _ _ POINT)); subst locations end.
      eapply GeneralOperationsCons with (middle := middle_memory).
      * apply (proj2 (@memory_offset_operation_registry_execution base row column descriptors entries ge locals operation i j before middle_memory
          VALID ARRAYS COVER UNIQUE HEAD I J)); assumption.
      * apply IH; assumption.
Qed.
Definition memory_offset_layout_body_model base operations row column body
  (VALID : rectangle_layout_valid base) (DISTINCT : row <> column)
  (CERT : Forall (memory_offset_operation_valid base row column) operations)
  (COVER : memory_descriptors_cover (memory_unique_descriptors (memory_general_sequence_anchors operations))
    (memory_general_sequence_requests operations))
  (BODY : flatten_region body = map (memory_general_layout_statement row column) operations) :
  memory_parametric_body_model base row column body.
Proof.
  refine {| parametric_body_descriptors := memory_unique_descriptors (memory_general_sequence_anchors operations);
    parametric_body_instructions := map memory_general_layout_instruction operations;
    parametric_body_point := fun ge locals i j => memory_general_operations_physical ge locals i j operations;
    parametric_body_normal := @memory_general_sequence_body_normal operations row column body BODY;
    parametric_body_quiet := @memory_general_sequence_body_quiet operations row column body BODY;
    parametric_body_writes := @memory_general_sequence_body_writes operations row column body BODY |}.
  - intros fe ge locals le before after final i j I J ROW COLUMN RUN.
    apply flatten_region_execution in RUN; rewrite BODY in RUN.
    eapply memory_offset_sequence_tail_inverse; eassumption.
  - intros ge locals before after RUN; eapply memory_general_anchors_registry; [|exact RUN].
    apply Forall_forall; intros descriptor MEMBER.
    apply in_flat_map in MEMBER as [operation [MEMBER REQUEST]].
    apply Forall_forall with (x := operation) in CERT; [|exact MEMBER].
    pose proof (@memory_offset_descriptor_valid base row column operation CERT) as VALID_REQUESTS.
    apply Forall_forall with (x := descriptor) in VALID_REQUESTS; assumption.
  - intros entries ge locals i j before after ARRAYS UNIQUE I J.
    apply memory_offset_sequence_point_execution with (base := base) (row := row) (column := column)
      (descriptors := memory_unique_descriptors (memory_general_sequence_anchors operations)); auto.
    apply memory_general_sequence_cover; exact COVER.
Defined.
Print Assumptions memory_offset_layout_body_model.
