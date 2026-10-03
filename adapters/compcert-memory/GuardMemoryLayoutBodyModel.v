From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightFiniteRegion ClightStraightLine ClightRectangularStore ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryMultipleArrays
  GuardMemoryRegistryBackend GuardMemoryParametricBody GuardMemoryLayoutRegistry GuardMemoryLayoutOperations
  GuardMemoryLayoutSequence GuardMemoryLayoutRanges.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Lemma memory_layout_sequence_indices base operations i j :
  rectangle_layout_valid base ->
  Forall (fun descriptor => rectangle_layout_valid (memory_descriptor_shape descriptor) /\
    memory_layout_range base (memory_descriptor_shape descriptor)) (memory_layout_sequence_requests operations) ->
  0 <= i < rectangle_outer_limit base -> 0 <= j < rectangle_stride base ->
  Forall (fun operation => memory_layout_indices (memory_layout_operation_requests operation) i j) operations.
Proof.
  intros VALID REQUESTS I J; apply Forall_forall; intros operation MEMBER.
  eapply memory_layout_request_indices; [exact VALID| |exact I|exact J].
  apply Forall_forall; intros descriptor REQUEST.
  apply Forall_forall with (x := descriptor) in REQUESTS; [exact REQUESTS|].
  apply in_flat_map; exists operation; split; assumption.
Qed.
Definition memory_layout_body_model base operations row column body
  (VALID : rectangle_layout_valid base)
  (REQUESTS : Forall (fun descriptor => rectangle_layout_valid (memory_descriptor_shape descriptor) /\
    memory_layout_range base (memory_descriptor_shape descriptor)) (memory_layout_sequence_requests operations))
  (COVER : memory_descriptors_cover (memory_unique_descriptors (memory_layout_sequence_requests operations))
    (memory_layout_sequence_requests operations))
  (BODY : flatten_region body = map (memory_layout_operation_statement row column) operations) :
  memory_parametric_body_model base row column body.
Proof.
  refine {| parametric_body_descriptors := memory_unique_descriptors (memory_layout_sequence_requests operations);
    parametric_body_instructions := map memory_layout_operation_instruction operations;
    parametric_body_point := fun ge locals i j => memory_layout_operations_physical ge locals i j operations;
    parametric_body_normal := @memory_layout_sequence_body_normal operations row column body BODY;
    parametric_body_quiet := @memory_layout_sequence_body_quiet operations row column body BODY;
    parametric_body_writes := @memory_layout_sequence_body_writes operations row column body BODY |}.
  - intros fe ge locals le before after final i j I J ROW COLUMN RUN.
    apply flatten_region_execution in RUN; rewrite BODY in RUN.
    eapply memory_layout_sequence_tail_inverse; [|exact ROW|exact COLUMN|exact RUN].
    eapply memory_layout_sequence_indices; eassumption.
  - intros ge locals before after RUN; eapply memory_layout_sequence_registry; [|exact RUN].
    apply Forall_forall; intros descriptor MEMBER.
    apply Forall_forall with (x := descriptor) in REQUESTS; [tauto|exact MEMBER].
  - intros entries ge locals i j before after ARRAYS UNIQUE I J.
    apply memory_layout_sequence_point_execution with
      (descriptors := memory_unique_descriptors (memory_layout_sequence_requests operations)); auto.
    + apply memory_layout_sequence_cover; exact COVER.
    + eapply memory_layout_sequence_indices; eassumption.
Defined.
Print Assumptions memory_layout_body_model.
