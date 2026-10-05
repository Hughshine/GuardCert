From compcert.common Require Import Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Cop Clight Csem.
From compcert.x86 Require Import Asm.
From Guard Require Import ClightSyntaxEquality.
From GuardInterface Require Import ClightReadonlyExpression ClightReadonlyTestCompiler ClightCircularCounter ClightEqualityHead.
Set Implicit Arguments.

Definition propose_equality_head source :=
  match source with
  | Ebinop One (Ecast (Etempvar iterator _) _) (Ecast (Etempvar bound _) _) _ => Some (iterator,bound)
  | _ => None end.
Definition choose_equality_head source : option (readonly_expression_rule source).
Proof.
  destruct (propose_equality_head source) as [[iterator bound]|]; [|exact None].
  destruct (expression_eq source (unsigned_equality_test iterator bound)) as [SAME|]; [|exact None].
  rewrite SAME; exact (Some (equality_head_rule iterator bound)).
Defined.
Definition compile_equality_heads := compile_readonly_tests choose_equality_head.
Theorem compile_equality_heads_correct p target : compile_equality_heads p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof. apply compile_readonly_tests_correct. Qed.
Print Assumptions choose_equality_head.
Print Assumptions compile_equality_heads_correct.
