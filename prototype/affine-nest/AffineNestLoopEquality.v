From Stdlib Require Import List Bool ZArith.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryLoops.
Set Implicit Arguments.

Definition affine_loop_expression_eq_dec : forall first second:L.expr,
  {first=second}+{first<>second}.
Proof. decide equality; try apply Nat.eq_dec; apply Z.eq_dec. Defined.

Definition affine_loop_test_eq_dec : forall first second:L.test,
  {first=second}+{first<>second}.
Proof. decide equality; try apply Bool.bool_dec; apply affine_loop_expression_eq_dec. Defined.

Fixpoint affine_loop_statement_eq_dec(first second:L.stmt){struct first} :
  {first=second}+{first<>second}
with affine_loop_sequence_eq_dec(first second:L.stmt_list){struct first} :
  {first=second}+{first<>second}.
Proof.
  - decide equality; try apply affine_loop_expression_eq_dec;
      try apply affine_loop_test_eq_dec; try apply memory_instruction_eq_dec;
      try apply affine_loop_sequence_eq_dec;
      apply List.list_eq_dec; apply affine_loop_expression_eq_dec.
  - decide equality.
Defined.
Print Assumptions affine_loop_statement_eq_dec.
