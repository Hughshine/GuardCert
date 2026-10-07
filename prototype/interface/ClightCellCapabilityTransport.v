From Stdlib Require Import ZArith Lia.
From compcert.common Require Import AST Values Memory.
From Guard Require Import CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryFootprintCapabilities.
From GuardInterface Require Import ClightStorePermissions.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A byte access exposes exactly the permission needed by pointer equality.
    Transporting that access does not assume values or allocation bounds. *)
Lemma valid_pointer_accesses_back before after block offset :
  memory_accesses_back before after -> Mem.valid_pointer after block offset=true ->
  Mem.valid_pointer before block offset=true.
Proof.
  intros BACK VALID; apply Mem.valid_pointer_nonempty_perm in VALID.
  assert (BYTE : Mem.valid_access after Mint8unsigned block offset Nonempty).
  { split.
    - intros address RANGE; change (offset<=address<offset+1) in RANGE.
      replace address with offset by lia; exact VALID.
    - change (1|offset); exists offset; lia. }
  destruct (BACK _ _ _ _ BYTE) as [PERMISSION ALIGN].
  apply Mem.valid_pointer_nonempty_perm,PERMISSION; change (offset<=offset<offset+1); lia.
Qed.

Theorem cell_capability_accesses_back locations before after cell :
  memory_accesses_back before after -> memory_cell_capable locations after cell ->
  memory_cell_capable locations before cell.
Proof.
  intros BACK [location [RESOLVE [CHUNK [VALID ALIGN]]]].
  exists location; split; [exact RESOLVE|split; [exact CHUNK|split; [|exact ALIGN]]].
  eapply valid_pointer_accesses_back; eassumption.
Qed.

Print Assumptions valid_pointer_accesses_back.
Print Assumptions cell_capability_accesses_back.
