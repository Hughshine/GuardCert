From Stdlib Require Import List ZArith.
From compcert.lib Require Import Integers Floats.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From GuardMemory Require Import GuardMemoryValueInstr.
Import ListNotations.
Set Implicit Arguments.
Definition memory_double_type := Tfloat F64 noattr.

Inductive double_operation := DoubleAdd | DoubleSub | DoubleMul | DoubleDiv.
Definition double_c_operation operation := match operation with
  | DoubleAdd => Oadd | DoubleSub => Osub | DoubleMul => Omul | DoubleDiv => Odiv end.
Definition double_compute operation first second : option val :=
  match first, second with
  | Vfloat a, Vfloat b => Some (Vfloat (match operation with
      | DoubleAdd => Float.add a b | DoubleSub => Float.sub a b
      | DoubleMul => Float.mul a b | DoubleDiv => Float.div a b end))
  | _, _ => None end.

Inductive double_value_expression :=
| DoubleBits : Z -> double_value_expression
| DoubleRead : nat -> double_value_expression
| DoubleBinary : double_operation -> double_value_expression -> double_value_expression -> double_value_expression
| DoubleNegate : double_value_expression -> double_value_expression.

Fixpoint evaluate_double_value (loaded : list val) expression : option val :=
  match expression with
  | DoubleBits bits => Some (Vfloat (Float.of_bits (Int64.repr bits)))
  | DoubleRead index => nth_error loaded index
  | DoubleBinary operation first second =>
      match evaluate_double_value loaded first, evaluate_double_value loaded second with
      | Some a, Some b => double_compute operation a b | _, _ => None end
  | DoubleNegate child => match evaluate_double_value loaded child with
      | Some (Vfloat value) => Some (Vfloat (Float.neg value)) | _ => None end
  end.

Definition double_operation_eq_dec : forall first second : double_operation,
  {first = second} + {first <> second}.
Proof. decide equality. Defined.
Definition double_value_expression_eq_dec : forall first second : double_value_expression,
  {first = second} + {first <> second}.
Proof. decide equality; try apply double_operation_eq_dec; try apply Nat.eq_dec; apply Z.eq_dec. Defined.

Module DoubleMemoryValue <: MEMORY_VALUE_CODE.
  Definition t := double_value_expression.
  Definition eq_dec := double_value_expression_eq_dec.
  Definition dummy := DoubleBits 0.
  Definition evaluate (_ : list Z) := evaluate_double_value.
End DoubleMemoryValue.
Module GuardDoubleMemoryInstr := MakeMemoryValueInstr DoubleMemoryValue.

Fixpoint double_value_code (loads : list expr) expression : option expr :=
  match expression with
  | DoubleBits bits => Some (Econst_float (Float.of_bits (Int64.repr bits)) memory_double_type)
  | DoubleRead index => nth_error loads index
  | DoubleBinary operation first second =>
      match double_value_code loads first, double_value_code loads second with
      | Some a, Some b => Some (Ebinop (double_c_operation operation) a b memory_double_type)
      | _, _ => None end
  | DoubleNegate child => match double_value_code loads child with
      | Some code => Some (Eunop Oneg code memory_double_type) | _ => None end
  end.

Lemma double_binary_operation_correspondence cenv operation first second memory value :
  double_compute operation first second = Some value ->
  sem_binary_operation cenv (double_c_operation operation)
    first memory_double_type second memory_double_type memory = Some value.
Proof.
  destruct first,second; cbn [double_compute]; try discriminate.
  destruct operation; intro RESULT; inversion RESULT; subst; reflexivity.
Qed.

Lemma double_value_code_type loads expression code :
  Forall (fun input => typeof input = memory_double_type) loads ->
  double_value_code loads expression = Some code -> typeof code = memory_double_type.
Proof.
  intros TYPES; revert code; induction expression; intros code CODE; cbn [double_value_code] in CODE.
  - inversion CODE; reflexivity.
  - apply nth_error_In in CODE; rewrite Forall_forall in TYPES; apply TYPES; exact CODE.
  - destruct (double_value_code loads expression1); try discriminate.
    destruct (double_value_code loads expression2); inversion CODE; reflexivity.
  - destruct (double_value_code loads expression); inversion CODE; reflexivity.
Qed.

Lemma double_load_receipt_at ge locals temps memory loads values index code value :
  Forall2 (fun expression value => typeof expression = memory_double_type /\
    eval_expr ge locals temps memory expression value) loads values ->
  nth_error loads index = Some code -> nth_error values index = Some value ->
  eval_expr ge locals temps memory code value.
Proof.
  intro RECEIPTS; revert index code value; induction RECEIPTS; intros index code value CODE VALUE.
  - destruct index; discriminate CODE.
  - destruct index; cbn in CODE,VALUE.
    + inversion CODE; inversion VALUE; subst; exact (proj2 H).
    + eapply IHRECEIPTS; eauto.
Qed.

Theorem double_value_code_execution ge locals temps memory loads values expression code value :
  Forall2 (fun input value => typeof input = memory_double_type /\
    eval_expr ge locals temps memory input value) loads values ->
  double_value_code loads expression = Some code ->
  evaluate_double_value values expression = Some value ->
  eval_expr ge locals temps memory code value.
Proof.
  intro RECEIPTS.
  assert (TYPES : Forall (fun input => typeof input = memory_double_type) loads).
  { induction RECEIPTS; constructor; [exact (proj1 H)|exact IHRECEIPTS]. }
  revert code value; induction expression; intros code value CODE VALUE;
    cbn [double_value_code] in CODE; cbn [evaluate_double_value] in VALUE.
  - inversion CODE; inversion VALUE; subst; constructor.
  - eapply double_load_receipt_at; eauto.
  - destruct (double_value_code loads expression1) as [first|] eqn:FIRST; try discriminate.
    destruct (double_value_code loads expression2) as [second|] eqn:SECOND; try discriminate.
    destruct (evaluate_double_value values expression1) as [a|] eqn:AVALUE; try discriminate.
    destruct (evaluate_double_value values expression2) as [b|] eqn:BVALUE; try discriminate.
    inversion CODE; subst code; econstructor.
    + eapply IHexpression1; eauto.
    + eapply IHexpression2; eauto.
    + rewrite (@double_value_code_type loads expression1 first TYPES FIRST), (@double_value_code_type loads expression2 second TYPES SECOND).
      eapply double_binary_operation_correspondence; exact VALUE.
  - destruct (double_value_code loads expression) as [child|] eqn:CHILD; try discriminate.
    destruct (evaluate_double_value values expression) as [input|] eqn:INPUT; try discriminate.
    destruct input; try discriminate.
    inversion CODE; inversion VALUE; subst code value; econstructor.
    + eapply IHexpression; eauto.
    + rewrite (@double_value_code_type loads expression child TYPES CHILD); reflexivity.
Qed.

Print Assumptions double_binary_operation_correspondence.
Print Assumptions double_value_code_type.
Print Assumptions double_value_code_execution.
Print Assumptions GuardDoubleMemoryInstr.access_function_checker_correct.
Print Assumptions GuardDoubleMemoryInstr.bc_condition_implie_permutbility.
