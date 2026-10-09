From Stdlib Require Import List ZArith.
From compcert.lib Require Import Floats.
From compcert.common Require Import Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryDoubleValue GuardMemoryDoubleSource
  GuardMemoryDoubleAssignment GuardMemoryDoubleAssignmentLiteral.
Import ListNotations.
Set Implicit Arguments.

(** Ordinary data produced from the actual assignment. Read expressions remain
    explicit address obligations: decoding syntax does not license any load. *)
Record double_assignment_descriptor := DoubleAssignmentDescriptor {
  double_assignment_target : expr;
  double_assignment_reads : list expr;
  double_assignment_value : double_value_expression
}.
Definition decode_double_assignment source : option double_assignment_descriptor :=
  match source with
  | Sassign lhs rhs => if type_eq (typeof lhs) memory_double_type then
      match decode_double_assignment_literal rhs with
      | Some number => Some (DoubleAssignmentDescriptor lhs [] (double_assignment_literal_expression number))
      | None => match decode_double_expression (double_source_reads rhs) rhs with
          | Some expression => Some (DoubleAssignmentDescriptor lhs (double_source_reads rhs) expression)
          | None => None end end
    else None
  | _ => None end.
Definition double_assignment_descriptor_action descriptor locations write :=
  MemoryAction locations write
    (fun values => compute_double_assignment values (double_assignment_value descriptor)).

Lemma decoded_double_assignment_shape source descriptor :
  decode_double_assignment source=Some descriptor ->
  exists rhs, source=Sassign (double_assignment_target descriptor) rhs /\
    typeof (double_assignment_target descriptor)=memory_double_type.
Proof.
  destruct source; cbn [decode_double_assignment]; try discriminate; intro DECODE.
  destruct (type_eq (typeof e) memory_double_type) as [TYPE|]; try discriminate.
  destruct (decode_double_assignment_literal e0) as [number|] eqn:LITERAL.
  - inversion DECODE; subst; exists e0; auto.
  - destruct (decode_double_expression (double_source_reads e0) e0) as [expression|] eqn:EXPR;
      try discriminate; inversion DECODE; subst; exists e0; auto.
Qed.

Theorem decoded_double_assignment_source_execution fe ge locals temps memory source descriptor
  locations write trace after final outcome :
  decode_double_assignment source=Some descriptor ->
  Forall2 (double_memory_location_receipt ge locals temps memory)
    (double_assignment_reads descriptor) locations ->
  double_memory_location_receipt ge locals temps memory (double_assignment_target descriptor) write ->
  exec_stmt fe ge locals temps memory source trace after final outcome ->
  trace=E0 /\ after=temps /\ outcome=Out_normal /\
    memory_action_run (double_assignment_descriptor_action descriptor locations write) memory final.
Proof.
  destruct source; cbn [decode_double_assignment]; try discriminate; intro DECODE.
  destruct (type_eq (typeof e) memory_double_type); try discriminate.
  destruct (decode_double_assignment_literal e0) as [number|] eqn:LITERAL.
  - inversion DECODE; subst descriptor; cbn [double_assignment_reads double_assignment_target
      double_assignment_value double_assignment_descriptor_action].
    intros READS WRITE SOURCE; inversion READS; subst locations.
    eapply double_assignment_literal_source_decode; eauto.
  - destruct (decode_double_expression (double_source_reads e0) e0) as [expression|] eqn:EXPR; try discriminate.
    inversion DECODE; subst descriptor; cbn [double_assignment_reads double_assignment_target
      double_assignment_value double_assignment_descriptor_action].
    intros READS WRITE SOURCE; eapply double_assignment_source_decode;
      [exact READS|exact WRITE|eapply decode_double_expression_code; exact EXPR|exact SOURCE].
Qed.

Theorem decoded_double_assignment_model_execution fe ge locals temps memory source descriptor
  locations write final :
  decode_double_assignment source=Some descriptor ->
  Forall2 (double_memory_location_receipt ge locals temps memory)
    (double_assignment_reads descriptor) locations ->
  double_memory_location_receipt ge locals temps memory (double_assignment_target descriptor) write ->
  memory_action_run (double_assignment_descriptor_action descriptor locations write) memory final ->
  exec_stmt fe ge locals temps memory source E0 temps final Out_normal.
Proof.
  destruct source; cbn [decode_double_assignment]; try discriminate; intro DECODE.
  destruct (type_eq (typeof e) memory_double_type); try discriminate.
  destruct (decode_double_assignment_literal e0) as [number|] eqn:LITERAL.
  - inversion DECODE; subst descriptor; cbn [double_assignment_reads double_assignment_target
      double_assignment_value double_assignment_descriptor_action].
    intros READS WRITE MODEL; inversion READS; subst locations.
    eapply double_assignment_literal_lowered_execution; eauto.
  - destruct (decode_double_expression (double_source_reads e0) e0) as [expression|] eqn:EXPR; try discriminate.
    inversion DECODE; subst descriptor; cbn [double_assignment_reads double_assignment_target
      double_assignment_value double_assignment_descriptor_action].
    intros READS WRITE MODEL; eapply double_assignment_lowered_execution;
      [exact READS|exact WRITE|eapply decode_double_expression_code; exact EXPR|exact MODEL].
Qed.

Corollary decoded_double_assignment_execution_iff fe ge locals temps memory source descriptor locations write final :
  decode_double_assignment source=Some descriptor ->
  Forall2 (double_memory_location_receipt ge locals temps memory)
    (double_assignment_reads descriptor) locations ->
  double_memory_location_receipt ge locals temps memory (double_assignment_target descriptor) write ->
  (exec_stmt fe ge locals temps memory source E0 temps final Out_normal <->
    memory_action_run (double_assignment_descriptor_action descriptor locations write) memory final).
Proof.
  intros DECODE READS WRITE; split.
  - intro SOURCE; exact (proj2 (proj2 (proj2
      (@decoded_double_assignment_source_execution fe ge locals temps memory source descriptor locations write
        E0 temps final Out_normal DECODE READS WRITE SOURCE)))).
  - eapply decoded_double_assignment_model_execution; eauto.
Qed.

Print Assumptions decoded_double_assignment_shape.
Print Assumptions decoded_double_assignment_source_execution.
Print Assumptions decoded_double_assignment_model_execution.
Print Assumptions decoded_double_assignment_execution_iff.
