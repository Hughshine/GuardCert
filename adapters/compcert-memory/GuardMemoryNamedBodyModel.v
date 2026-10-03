From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightStraightLine ClightRectangularStore ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryRegistryBackend
  GuardMemoryNamedOperations GuardMemoryNamedRegistrySource GuardMemoryParametricBody.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition memory_named_body_model base operations row column body
  (VALID : rectangle_layout_valid base) (LAYOUTS : Forall (named_operation_layout base) operations)
  (BODY : flatten_region body = map (named_operation_statement row column) operations) :
  memory_parametric_body_model base row column body.
Proof.
  refine {| parametric_body_descriptors := named_array_descriptors base operations;
    parametric_body_instructions := map named_operation_instruction operations;
    parametric_body_point := fun ge locals i j => named_array_operations_physical ge locals i j operations;
    parametric_body_normal := @named_array_operations_body_normal operations row column body BODY;
    parametric_body_quiet := @named_array_operations_body_quiet operations row column body BODY;
    parametric_body_writes := @named_array_operations_body_writes operations row column body BODY |}.
  - intros fe ge locals le before after final i j I J ROW COLUMN RUN.
    apply flatten_region_execution in RUN; rewrite BODY in RUN.
    eapply named_array_operations_tail_inverse; eauto.
    + apply rectangle_point_bound with (N := rectangle_outer_limit base) (M := rectangle_stride base); auto;
        pose proof (rectangle_limits VALID) as [_ [_ [POSITIVE LIMIT]]]; lia.
    + replace (i*rectangle_stride base) with (i*rectangle_stride base+0) by ring.
      apply rectangle_point_bound with (N := rectangle_outer_limit base) (M := rectangle_stride base); auto;
        pose proof (rectangle_limits VALID) as [_ [_ [POSITIVE LIMIT]]]; lia.
  - intros; eapply named_array_operations_registry; eassumption.
  - intros entries ge locals i j before after ARRAYS UNIQUE I J.
    apply named_array_operations_point_execution with (base := base) (universe := operations); auto.
    + apply Forall_forall; auto.
    + apply rectangle_point_bound with (N := rectangle_outer_limit base) (M := rectangle_stride base); auto;
        pose proof (rectangle_limits VALID) as [_ [_ [POSITIVE LIMIT]]]; lia.
    + replace (i*rectangle_stride base) with (i*rectangle_stride base+0) by ring.
      apply rectangle_point_bound with (N := rectangle_outer_limit base) (M := rectangle_stride base); auto;
        pose proof (rectangle_limits VALID) as [_ [_ [POSITIVE LIMIT]]]; lia.
Defined.
Print Assumptions memory_named_body_model.
