From Stdlib Require Import List ZArith.
From compcert.lib Require Import Integers Floats.
From compcert.common Require Import Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryDoubleValue GuardMemoryDoubleLocations
  GuardMemoryObservationDeterminism GuardMemoryDoubleAssignment GuardMemoryLongControl.
Import ListNotations.
Set Implicit Arguments.

(** Assignment converts an integer literal to the type of its destination.
    Decode this actual conversion, rather than asking the source user to write
    a floating literal. Signed I32, signed I64 and F64 literals are supported;
    this is not a decoder for arbitrary casts or mixed arithmetic trees. *)
Definition decode_double_assignment_literal code : option float :=
  match code with
  | Econst_int value ty => if type_eq ty memory_signed_int_type
      then Some (Float.of_int value) else None
  | Econst_long value ty => if type_eq ty memory_long_type
      then Some (Float.of_long value) else None
  | Econst_float value ty => if type_eq ty memory_double_type
      then Some value else None
  | _ => None end.

Theorem double_assignment_literal_evaluation ge locals temps memory code number :
  decode_double_assignment_literal code=Some number ->
  exists value, eval_expr ge locals temps memory code value /\
    sem_cast value (typeof code) memory_double_type memory=Some (Vfloat number).
Proof.
  destruct code; cbn [decode_double_assignment_literal]; try discriminate;
    intros DECODE.
  - destruct (type_eq t memory_signed_int_type); try discriminate; subst t.
    inversion DECODE; subst number; exists (Vint i); split; [constructor|reflexivity].
  - destruct (type_eq t memory_double_type); try discriminate; subst t.
    inversion DECODE; subst number; exists (Vfloat f); split; [constructor|reflexivity].
  - destruct (type_eq t memory_long_type); try discriminate; subst t.
    inversion DECODE; subst number; exists (Vlong i); split; [constructor|reflexivity].
Qed.

Lemma double_assignment_literal_cast ge locals temps memory code number value :
  decode_double_assignment_literal code=Some number ->
  eval_expr ge locals temps memory code value ->
  sem_cast value (typeof code) memory_double_type memory=Some (Vfloat number).
Proof.
  intros DECODE SOURCE.
  destruct (@double_assignment_literal_evaluation ge locals temps memory code number DECODE)
    as [actual [EVAL CAST]].
  pose proof (memory_expression_unique EVAL SOURCE) as SAME; subst value; exact CAST.
Qed.

(** This language law covers all finite traces, temporary exits and outcomes.
    It does not manufacture permissions for the destination. *)
Theorem double_assignment_literal_normalization fe ge locals temps memory lhs code number
  trace after final outcome :
  typeof lhs=memory_double_type ->
  decode_double_assignment_literal code=Some number ->
  (exec_stmt fe ge locals temps memory (Sassign lhs code) trace after final outcome <->
   exec_stmt fe ge locals temps memory
     (Sassign lhs (Econst_float number memory_double_type)) trace after final outcome).
Proof.
  intros TYPE DECODE; split; intro RUN; inversion RUN; subst.
  - match goal with
    SOURCE : eval_expr _ _ _ _ code ?value,
    CAST : sem_cast ?value (typeof code) (typeof lhs) _=Some ?converted |- _ =>
      rewrite TYPE in CAST;
      pose proof (@double_assignment_literal_cast ge locals after memory code number value DECODE SOURCE) as EXACT;
      rewrite EXACT in CAST; inversion CAST; subst converted
    end.
    eapply exec_Sassign; [eassumption|constructor|rewrite TYPE; reflexivity|eassumption].
  - match goal with SOURCE : eval_expr _ _ _ _ (Econst_float number memory_double_type) ?value |- _ =>
      assert (EXACT : eval_expr ge locals after memory (Econst_float number memory_double_type) (Vfloat number)) by constructor;
      pose proof (memory_expression_unique EXACT SOURCE) as SAME; subst value
    end.
    match goal with CAST : sem_cast (Vfloat number) _ (typeof lhs) _=Some ?converted |- _ =>
      rewrite TYPE in CAST; cbn in CAST; inversion CAST; subst converted
    end.
    destruct (@double_assignment_literal_evaluation ge locals after memory code number DECODE)
      as [value [EVAL CAST]].
    eapply exec_Sassign; [eassumption|exact EVAL|rewrite TYPE; exact CAST|eassumption].
Qed.

Definition double_assignment_literal_expression number :=
  DoubleBits (Int64.unsigned (Float.to_bits number)).
Lemma double_assignment_literal_code number :
  double_value_code [] (double_assignment_literal_expression number)=
    Some (Econst_float number memory_double_type).
Proof.
  unfold double_assignment_literal_expression; cbn [double_value_code].
  rewrite Int64.repr_unsigned,Float.of_to_bits; reflexivity.
Qed.

Theorem double_assignment_literal_source_decode fe ge locals temps memory lhs code number write
  trace after final outcome :
  decode_double_assignment_literal code=Some number ->
  double_memory_location_receipt ge locals temps memory lhs write ->
  exec_stmt fe ge locals temps memory (Sassign lhs code) trace after final outcome ->
  trace=E0 /\ after=temps /\ outcome=Out_normal /\
    memory_action_run (MemoryAction [] write
      (fun values => compute_double_assignment values (double_assignment_literal_expression number))) memory final.
Proof.
  intros DECODE WRITE SOURCE.
  apply (@double_assignment_literal_normalization fe ge locals temps memory lhs code number
    trace after final outcome (proj1 WRITE) DECODE) in SOURCE.
  eapply double_assignment_source_decode with (rhs:=Econst_float number memory_double_type);
    [constructor|exact WRITE|apply double_assignment_literal_code|exact SOURCE].
Qed.

Theorem double_assignment_literal_lowered_execution fe ge locals temps memory lhs code number write final :
  decode_double_assignment_literal code=Some number ->
  double_memory_location_receipt ge locals temps memory lhs write ->
  memory_action_run (MemoryAction [] write
    (fun values => compute_double_assignment values (double_assignment_literal_expression number))) memory final ->
  exec_stmt fe ge locals temps memory (Sassign lhs code) E0 temps final Out_normal.
Proof.
  intros DECODE WRITE MODEL.
  apply (@double_assignment_literal_normalization fe ge locals temps memory lhs code number
    E0 temps final Out_normal (proj1 WRITE) DECODE).
  eapply double_assignment_lowered_execution; [constructor|exact WRITE|apply double_assignment_literal_code|exact MODEL].
Qed.

Print Assumptions double_assignment_literal_evaluation.
Print Assumptions double_assignment_literal_cast.
Print Assumptions double_assignment_literal_normalization.
Print Assumptions double_assignment_literal_code.
Print Assumptions double_assignment_literal_source_decode.
Print Assumptions double_assignment_literal_lowered_execution.
