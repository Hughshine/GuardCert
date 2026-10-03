From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST Values Memory.
From polcert.src Require Import PolyBase.
From Guard Require Import CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Record memory_array_entry := MemoryArrayEntry {
  memory_array_id : ident;
  memory_array_block : Values.block;
  memory_array_extent : Z
}.
Fixpoint memory_array_registry entries cell : option memory_location :=
  match entries with
  | [] => None
  | entry::rest =>
    if Pos.eqb (arr_id cell) (memory_array_id entry)
    then flat_array_locations (memory_array_id entry) (memory_array_block entry) (memory_array_extent entry) cell
    else memory_array_registry rest cell end.
Lemma memory_array_registry_location_block entries cell location :
  memory_array_registry entries cell = Some location ->
  In (location_block location) (map memory_array_block entries).
Proof.
  induction entries; cbn; [discriminate|].
  destruct (Pos.eqb (arr_id cell) (memory_array_id a)) eqn:SAME.
  - unfold flat_array_locations; rewrite SAME.
    destruct (arr_index cell) as [|index [|next tail]]; try discriminate.
    destruct ((0 <=? index) && (index <? memory_array_extent a)); try discriminate.
    intro LOOKUP; inversion LOOKUP; left; reflexivity.
  - intro LOOKUP; right; apply IHentries; exact LOOKUP.
Qed.
Theorem memory_array_registry_nonalias entries :
  NoDup (map memory_array_block entries) -> locations_nonalias (memory_array_registry entries).
Proof.
  induction entries as [|entry rest IH]; intro UNIQUE;
    intros first second first_location second_location FIRST SECOND DISTINCT; cbn in FIRST,SECOND; [discriminate|].
  inversion UNIQUE as [|block blocks FRESH TAIL]; subst.
  destruct (Pos.eqb (arr_id first) (memory_array_id entry)) eqn:FIRST_ID;
    destruct (Pos.eqb (arr_id second) (memory_array_id entry)) eqn:SECOND_ID.
  - eapply flat_array_locations_nonalias; eassumption.
  - assert (FIRST_BLOCK : location_block first_location = memory_array_block entry).
    { pose proof (@memory_array_registry_location_block [entry] first first_location) as BLOCK.
      cbn in BLOCK; rewrite FIRST_ID in BLOCK.
      specialize (BLOCK FIRST); cbn in BLOCK; intuition congruence. }
    unfold location_disjoint; left; rewrite FIRST_BLOCK.
    intro SAME; apply FRESH; rewrite SAME; eapply memory_array_registry_location_block; exact SECOND.
  - assert (SECOND_BLOCK : location_block second_location = memory_array_block entry).
    { pose proof (@memory_array_registry_location_block [entry] second second_location) as BLOCK.
      cbn in BLOCK; rewrite SECOND_ID in BLOCK.
      specialize (BLOCK SECOND); cbn in BLOCK; intuition congruence. }
    unfold location_disjoint; left; rewrite SECOND_BLOCK.
    intro SAME; apply FRESH; rewrite <- SAME; eapply memory_array_registry_location_block; exact FIRST.
  - eapply IH; eassumption.
Qed.
Print Assumptions memory_array_registry_nonalias.
