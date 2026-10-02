From Stdlib Require Import ZArith.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Csem Clight.
From Guard Require Import PolCertArrayExamples PolCertStoreSwap PolCertDynamicStore
  ClightRegionRewrite RegionCompiler ClightNoWrap ClightSignedCancel.
Open Scope Z_scope.

Module NativeDynamicStore := PolCertDynamicStore DecimalNames.

(** The frontend supplies the array identifier as ordinary input data.
    Correctness holds for every identifier; a missing syntax match simply
    keeps the original fragment. *)
Definition select (array_id first_id second_id : ident) (source : statement) :=
  match NativeDynamicStore.Stores.select_store_pair array_id 2 0 1 (Int.repr 7) (Int.repr 8) source with
  | Some target => Some target
  | None => NativeDynamicStore.select_dynamic_pair array_id 2 first_id second_id
      (Int.repr 7) (Int.repr 8) source end.

Lemma select_sound array_id first_id second_id source target :
  select array_id first_id second_id source = Some target -> region_contract source target.
Proof.
  unfold select.
  destruct (NativeDynamicStore.Stores.select_store_pair array_id 2 0 1 (Int.repr 7) (Int.repr 8) source)
    as [selected|] eqn:STATIC.
  - intro SELECT; inversion SELECT; subst selected.
    eapply NativeDynamicStore.Stores.select_store_pair_sound; exact STATIC.
  - exact (@NativeDynamicStore.select_dynamic_pair_sound array_id 2 first_id second_id
      (Int.repr 7) (Int.repr 8) source target).
Qed.

Definition compile (array_id first_id second_id : ident) :=
  compile_with_regions select_no_wrap select_signed_memory_rewrites (select array_id first_id second_id).

Theorem compile_correct array_id first_id second_id p target :
  compile array_id first_id second_id p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof.
  unfold compile; apply compile_with_regions_correct.
  - exact select_no_wrap_sound.
  - exact (select_sound array_id first_id second_id).
  - exact select_signed_memory_rewrites_sound.
Qed.

Print Assumptions compile_correct.
