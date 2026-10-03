From Stdlib Require Import List Bool Arith.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryScalarLoops.
Import ListNotations.
Set Implicit Arguments.

(** Convenience preparation of an untrusted proposal.  Every resulting loop is
    independently checked against the actual scalar source before lowering.
    Context count parameters precede scalar parameters at every candidate depth. *)
Fixpoint memory_carry_scalar_arguments depth dimensions scalars (loop : L.stmt) : L.stmt :=
  match loop with
  | L.Instr instruction arguments => L.Instr instruction
      (if Nat.eqb (length arguments) dimensions then
        arguments++memory_variables_from (depth+dimensions)%nat scalars else arguments)
  | L.Seq statements => L.Seq (memory_carry_scalar_arguments_list depth dimensions scalars statements)
  | L.Guard test body => L.Guard test (memory_carry_scalar_arguments depth dimensions scalars body)
  | L.Loop lower upper body => L.Loop lower upper (memory_carry_scalar_arguments (S depth) dimensions scalars body)
  end
with memory_carry_scalar_arguments_list depth dimensions scalars (statements : L.stmt_list) : L.stmt_list :=
  match statements with
  | L.SNil => L.SNil
  | L.SCons first rest => L.SCons (memory_carry_scalar_arguments depth dimensions scalars first)
      (memory_carry_scalar_arguments_list depth dimensions scalars rest)
  end.
Print Assumptions memory_carry_scalar_arguments.
