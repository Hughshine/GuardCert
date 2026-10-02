From Stdlib Require Import ZArith.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Csem.
From Guard Require Import PolCertArrayExamples PolCertStoreSwap.
Open Scope Z_scope.

Module NativeStoreSwap := PolCertStoreSwap DecimalNames.

(** The frontend supplies the array identifier as ordinary input data.
    Correctness holds for every identifier; a missing syntax match simply
    keeps the original fragment. *)
Definition compile (array_id : ident) :=
  NativeStoreSwap.compile_store_pair array_id 2 0 1 (Int.repr 7) (Int.repr 8).

Theorem compile_correct array_id p target :
  compile array_id p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof.
  exact (@NativeStoreSwap.compile_store_pair_correct array_id 2 0 1 (Int.repr 7) (Int.repr 8) p target).
Qed.

Print Assumptions compile_correct.
