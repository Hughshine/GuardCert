From Stdlib Require Import List ZArith Lia Bool.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST Values.
From polcert.lib Require Import Linalg.
From polcert.src Require Import PolyBase.
From Guard Require Import CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryBufferOffsets.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Lemma interval_buffer_cell_separation modulus base lower upper first second :
  0 < modulus -> (4 | modulus) -> 4*(upper-lower) <= modulus ->
  lower <= first < upper -> lower <= second < upper -> first <> second ->
  memory_buffer_offset modulus base first+4 <= memory_buffer_offset modulus base second \/
    memory_buffer_offset modulus base second+4 <= memory_buffer_offset modulus base first.
Proof.
  intros MODULUS CELLS EXTENT FIRST SECOND DISTINCT.
  pose proof (@memory_buffer_cell_separation modulus (base+4*lower) (upper-lower)
    (first-lower) (second-lower) MODULUS CELLS EXTENT ltac:(lia) ltac:(lia) ltac:(lia)) as SEPARATE.
  unfold memory_buffer_offset in *.
  replace (base+4*lower+4*(first-lower)) with (base+4*first) in SEPARATE by ring.
  replace (base+4*lower+4*(second-lower)) with (base+4*second) in SEPARATE by ring.
  exact SEPARATE.
Qed.
Definition interval_pointer_locations array block base lower upper (cell : MemCell) : option memory_location :=
  if Pos.eqb (arr_id cell) array then match arr_index cell with
  | [index] => if (lower <=? index) && (index <? upper)
      then Some (MemoryLocation Mint32 block (memory_pointer_buffer_offset base index)) else None
  | _ => None end else None.
Theorem interval_pointer_locations_nonalias array block base lower upper :
  4*(upper-lower) <= Ptrofs.modulus -> locations_nonalias (interval_pointer_locations array block base lower upper).
Proof.
  intros EXTENT [first_id first_indices] [second_id second_indices] first_location second_location FIRST SECOND DIFFERENT.
  unfold interval_pointer_locations in FIRST,SECOND; cbn [arr_id arr_index] in FIRST,SECOND.
  destruct (Pos.eqb first_id array) eqn:FIRST_ID; try discriminate FIRST.
  destruct (Pos.eqb second_id array) eqn:SECOND_ID; try discriminate SECOND.
  apply Pos.eqb_eq in FIRST_ID,SECOND_ID; subst first_id second_id.
  destruct first_indices as [|first_index [|first_rest first_tail]]; try discriminate FIRST.
  destruct second_indices as [|second_index [|second_rest second_tail]]; try discriminate SECOND.
  destruct ((lower <=? first_index) && (first_index <? upper)) eqn:FIRST_RANGE; try discriminate FIRST.
  destruct ((lower <=? second_index) && (second_index <? upper)) eqn:SECOND_RANGE; try discriminate SECOND.
  rewrite andb_true_iff,Z.leb_le,Z.ltb_lt in FIRST_RANGE,SECOND_RANGE.
  inversion FIRST; inversion SECOND; subst first_location second_location.
  assert (DISTINCT : first_index <> second_index).
  { intro SAME; subst second_index; unfold cell_neq in DIFFERENT; cbn in DIFFERENT.
    destruct DIFFERENT as [BAD|BAD]; [congruence|apply BAD; apply veq_refl]. }
  right; change (memory_pointer_buffer_offset base first_index+4 <= memory_pointer_buffer_offset base second_index \/
    memory_pointer_buffer_offset base second_index+4 <= memory_pointer_buffer_offset base first_index).
  apply interval_buffer_cell_separation with (lower := lower) (upper := upper);
    [pose proof Ptrofs.modulus_pos; lia|apply memory_pointer_modulus_cells|exact EXTENT|exact FIRST_RANGE|exact SECOND_RANGE|exact DISTINCT].
Qed.
Print Assumptions interval_pointer_locations_nonalias.
