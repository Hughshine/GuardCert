From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightFiniteRegion ClightStraightLine ClightRectangularStore ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryMultipleArrays
  GuardMemoryRegistryBackend GuardMemoryParametricBody GuardMemoryLayoutRegistry
  GuardMemoryGeneralLayoutOperations GuardMemoryGeneralLayoutSequence.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition memory_general_layout_body_model base operations row column body
  (VALID : rectangle_layout_valid base) (DISTINCT : row <> column)
  (CERT : Forall (memory_general_layout_valid base row column) operations)
  (COVER : memory_descriptors_cover (memory_unique_descriptors (memory_general_sequence_requests operations))
    (memory_general_sequence_requests operations))
  (BODY : flatten_region body = map (memory_general_layout_statement row column) operations) :
  memory_parametric_body_model base row column body.
Proof.
  refine {| parametric_body_descriptors := memory_unique_descriptors (memory_general_sequence_requests operations);
    parametric_body_instructions := map memory_general_layout_instruction operations;
    parametric_body_point := fun ge locals i j => memory_general_operations_physical ge locals i j operations;
    parametric_body_normal := @memory_general_sequence_body_normal operations row column body BODY;
    parametric_body_quiet := @memory_general_sequence_body_quiet operations row column body BODY;
    parametric_body_writes := @memory_general_sequence_body_writes operations row column body BODY |}.
  - intros fe ge locals le before after final i j I J ROW COLUMN RUN.
    apply flatten_region_execution in RUN; rewrite BODY in RUN.
    eapply memory_general_sequence_tail_inverse; eassumption.
  - intros ge locals before after RUN; eapply memory_general_sequence_registry; eassumption.
  - intros entries ge locals i j before after ARRAYS UNIQUE I J.
    apply memory_general_sequence_point_execution with
      (base := base) (row := row) (column := column)
      (descriptors := memory_unique_descriptors (memory_general_sequence_requests operations)); auto.
    apply memory_general_sequence_cover; exact COVER.
Defined.
Print Assumptions memory_general_layout_body_model.
