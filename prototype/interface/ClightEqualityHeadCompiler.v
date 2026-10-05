From compcert.common Require Import Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Cop Clight Csem.
From compcert.x86 Require Import Asm.
From Guard Require Import ClightSyntaxEquality ClightCondition.
From GuardInterface Require Import ClightReadonlyExpression ClightReadonlyTestCompiler ClightCircularCounter ClightEqualityHead ClightOrderedInequality.
Set Implicit Arguments.

Definition propose_signed_inequality source :=
  match source with
  | Ebinop One first second _ => Some (first,second)
  | _ => None end.
Definition choose_equality_head source : option (readonly_expression_rule source).
Proof.
  destruct (propose_signed_inequality source) as [[left right]|]; [|exact None].
  destruct (type_eq (typeof left) type_int32s) as [LEFT|]; [|exact None].
  destruct (type_eq (typeof right) type_int32s) as [RIGHT|]; [|exact None].
  destruct (expression_eq source (comparison_source left right)) as [SAME|]; [|exact None].
  rewrite SAME; exact (Some (@ordered_inequality_rule left right LEFT RIGHT)).
Defined.
Definition compile_equality_heads := compile_readonly_tests choose_equality_head.
Theorem compile_equality_heads_correct p target : compile_equality_heads p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof. apply compile_readonly_tests_correct. Qed.
Print Assumptions choose_equality_head.
Print Assumptions compile_equality_heads_correct.
