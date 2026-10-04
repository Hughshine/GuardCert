From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import Values.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight Ctypes.
From Guard Require Import ClightCountedLoop.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions GuardMemoryAffineRenaming.
From GuardAffineNest Require Import AffineNestSyntax.
Set Implicit Arguments.

(** Control names and value names are separate: the root upper-bound parameter
    remains public when the scan stores its private loop boundary. *)
Fixpoint affine_scan_statement nest (controls values:ident->ident) lower leaf := match nest with
  | AffineSourceLeaf _=>leaf
  | AffineSourceAxis iterator bound expression _ child=>
    Ssequence(Sset(controls iterator) lower)
      (Ssequence(Sset(controls bound)(memory_source_affine_code(memory_source_affine_rename values expression)))
        (counted_loop(controls iterator)(controls bound)
          (affine_scan_statement child controls values(Econst_int Int.zero type_int32s) leaf))) end.

Definition affine_scan_word_view (registers:list ident) values valuation temps :=
  forall identifier, In identifier registers ->
    temps!(values identifier)=Some(Vint(Int.repr(valuation identifier))).

Print Assumptions affine_scan_statement.
