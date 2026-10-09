From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Integers.
From compcert.common Require Import Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From polcert.lib Require Import Linalg.
From Guard Require Import ClightCountedLoop.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryLongControl.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Model operands come from the checked I32 affine compiler. Cast before
    address arithmetic; I64 operations preserve repr of the mathematical
    affine value, including modular intermediates. Physical address bounds
    remain a separate tensor-layout obligation. *)
Definition double_ranged_operand ge locals temps memory code value :=
  (typeof code=memory_signed_int_type /\ eval_expr ge locals temps memory code (Vint (Int.repr value))) /\
  signed_range value.
Definition double_long_operand code := Ecast code memory_long_type.
Definition double_long_constant value := Econst_long (Int64.repr value) memory_long_type.
Definition double_long_add first second := Ebinop Oadd first second memory_long_type.
Definition double_long_mul first second := Ebinop Omul first second memory_long_type.

Lemma double_long_operand_exact ge locals temps memory code value :
  double_ranged_operand ge locals temps memory code value ->
  eval_expr ge locals temps memory (double_long_operand code) (Vlong (Int64.repr value)).
Proof.
  intros [[TYPE RUN] RANGE]; unfold double_long_operand.
  eapply eval_Ecast; [exact RUN|].
  rewrite TYPE; change (Some (Vlong (Int64.repr (Int.signed (Int.repr value))))=
    Some (Vlong (Int64.repr value))).
  rewrite Int.signed_repr by exact RANGE; reflexivity.
Qed.
Lemma double_long_repr_mul first second :
  Int64.mul (Int64.repr first) (Int64.repr second)=Int64.repr (first*second).
Proof.
  unfold Int64.mul; apply Int64.eqm_samerepr; apply Int64.eqm_mult;
    apply Int64.eqm_sym,Int64.eqm_unsigned_repr.
Qed.
Lemma double_long_add_execution ge locals temps memory first second a b :
  typeof first=memory_long_type -> typeof second=memory_long_type ->
  eval_expr ge locals temps memory first (Vlong (Int64.repr a)) ->
  eval_expr ge locals temps memory second (Vlong (Int64.repr b)) ->
  eval_expr ge locals temps memory (double_long_add first second) (Vlong (Int64.repr (a+b))).
Proof.
  intros FIRST SECOND A B; unfold double_long_add; eapply eval_Ebinop; [exact A|exact B|].
  rewrite FIRST,SECOND; change (Some (Vlong (Int64.add (Int64.repr a) (Int64.repr b)))=
    Some (Vlong (Int64.repr (a+b)))); rewrite memory_long_repr_add; reflexivity.
Qed.
Lemma double_long_mul_execution ge locals temps memory first second a b :
  typeof first=memory_long_type -> typeof second=memory_long_type ->
  eval_expr ge locals temps memory first (Vlong (Int64.repr a)) ->
  eval_expr ge locals temps memory second (Vlong (Int64.repr b)) ->
  eval_expr ge locals temps memory (double_long_mul first second) (Vlong (Int64.repr (a*b))).
Proof.
  intros FIRST SECOND A B; unfold double_long_mul; eapply eval_Ebinop; [exact A|exact B|].
  rewrite FIRST,SECOND; change (Some (Vlong (Int64.mul (Int64.repr a) (Int64.repr b)))=
    Some (Vlong (Int64.repr (a*b)))); rewrite double_long_repr_mul; reflexivity.
Qed.

Fixpoint double_long_dot codes coefficients :=
  match codes,coefficients with
  | code::rest,coefficient::tail => double_long_add
    (double_long_mul (double_long_constant coefficient) (double_long_operand code)) (double_long_dot rest tail)
  | _,_ => double_long_constant 0 end.
Definition double_long_affine codes (row : list Z * Z) :=
  double_long_add (double_long_dot codes (fst row)) (double_long_constant (snd row)).
Lemma double_long_dot_type codes coefficients : typeof (double_long_dot codes coefficients)=memory_long_type.
Proof. destruct codes,coefficients; reflexivity. Qed.
Lemma double_long_dot_execution ge locals temps memory codes values :
  Forall2 (double_ranged_operand ge locals temps memory) codes values ->
  forall coefficients, eval_expr ge locals temps memory (double_long_dot codes coefficients)
    (Vlong (Int64.repr (dot_product coefficients values))).
Proof.
  intro OPERANDS; induction OPERANDS; intros coefficients; destruct coefficients; cbn [double_long_dot dot_product];
    try constructor.
  apply double_long_add_execution; [reflexivity|apply double_long_dot_type| |apply IHOPERANDS].
  apply double_long_mul_execution; [reflexivity|reflexivity|constructor|].
  apply double_long_operand_exact; exact H.
Qed.
Theorem double_long_affine_execution ge locals temps memory codes values row :
  Forall2 (double_ranged_operand ge locals temps memory) codes values ->
  eval_expr ge locals temps memory (double_long_affine codes row)
    (Vlong (Int64.repr (dot_product (fst row) values+snd row))).
Proof.
  intro OPERANDS; unfold double_long_affine; apply double_long_add_execution;
    [apply double_long_dot_type|reflexivity|apply double_long_dot_execution; exact OPERANDS|constructor].
Qed.
Theorem double_long_affines_execution ge locals temps memory codes values rows :
  Forall2 (double_ranged_operand ge locals temps memory) codes values ->
  Forall2 (fun code value => typeof code=memory_long_type /\
    eval_expr ge locals temps memory code (Vlong (Int64.repr value)))
    (map (double_long_affine codes) rows) (affine_product rows values).
Proof.
  intro OPERANDS; induction rows as [|[coefficients bias] rows IH]; cbn [map affine_product]; constructor; [|exact IH].
  split; [reflexivity|apply double_long_affine_execution; exact OPERANDS].
Qed.

Print Assumptions double_long_operand_exact.
Print Assumptions double_long_affine_execution.
Print Assumptions double_long_affines_execution.
