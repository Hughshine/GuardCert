From Stdlib Require Import Bool.
From compcert.common Require Import Values Memory.
From compcert.cfrontend Require Import Clight Ctypes.
From Guard Require Import ClightCondition ClightNoWrap.
Set Implicit Arguments.

(** Eager conjunction is legal only when both operands are defined Boolean
    words. This is not a lowering of arbitrary short-circuit checks. *)
Definition initialized_boolean_and left right :=
  Ebinop Cop.Oand left right type_int32s.

Theorem initialized_boolean_and_evaluation ge locals temps memory left right first second :
  typeof left = type_int32s -> typeof right = type_int32s ->
  eval_expr ge locals temps memory left (Val.of_bool first) ->
  eval_expr ge locals temps memory right (Val.of_bool second) ->
  eval_expr ge locals temps memory (initialized_boolean_and left right)
    (Val.of_bool (andb first second)).
Proof.
  intros LEFT_TYPE RIGHT_TYPE LEFT RIGHT; unfold initialized_boolean_and.
  eapply eval_Ebinop; [exact LEFT|exact RIGHT|].
  rewrite LEFT_TYPE, RIGHT_TYPE; destruct first, second; reflexivity.
Qed.

Print Assumptions initialized_boolean_and_evaluation.
