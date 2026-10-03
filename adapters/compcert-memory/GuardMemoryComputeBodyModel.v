From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightFiniteRegion ClightStraightLine ClightRectangularStore ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryMultipleArrays
  GuardMemoryRegistryBackend GuardMemoryParametricBody GuardMemoryLayoutRegistry
  GuardMemoryAffineCompute GuardMemoryComputeSequence.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition memory_compute_body_model base operations row column body
  (DISTINCT : row <> column)
  (CERT : Forall (memory_affine_compute_valid base row column) operations)
  (COVER : memory_descriptors_cover (memory_unique_descriptors (memory_compute_sequence_anchors operations))
    (memory_compute_sequence_requests operations))
  (BODY : flatten_region body = map memory_affine_compute_statement operations) :
  memory_parametric_body_model base row column body.
Proof.
  refine {| parametric_body_descriptors := memory_unique_descriptors (memory_compute_sequence_anchors operations);
    parametric_body_instructions := map memory_affine_compute_instruction operations;
    parametric_body_point := fun ge locals i j => memory_compute_sequence_physical ge locals i j operations;
    parametric_body_normal := @memory_compute_sequence_normal operations body BODY;
    parametric_body_quiet := @memory_compute_sequence_quiet operations body BODY;
    parametric_body_writes := @memory_compute_sequence_writes operations body BODY |}.
  - intros fe ge locals le before after final i j I J ROW COLUMN RUN.
    apply flatten_region_execution in RUN; rewrite BODY in RUN.
    eapply memory_compute_sequence_tail_inverse; eassumption.
  - intros ge locals before after RUN; eapply memory_compute_sequence_registry; eassumption.
  - intros entries ge locals i j before after ARRAYS UNIQUE I J.
    apply memory_compute_sequence_point_execution with (base := base) (row := row) (column := column)
      (descriptors := memory_unique_descriptors (memory_compute_sequence_anchors operations)); auto.
    apply memory_compute_sequence_cover; exact COVER.
Defined.
Print Assumptions memory_compute_body_model.
