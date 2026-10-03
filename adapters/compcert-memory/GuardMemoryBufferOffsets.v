From Stdlib Require Import ZArith Lia List Bool.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST Values.
From polcert.lib Require Import Linalg.
From polcert.src Require Import PolyBase.
From Guard Require Import CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Pointer buffers may begin at a nonzero offset.  Addresses use CompCert's
    modular pointer arithmetic.  Distinct small logical indices still have
    disjoint four-byte footprints, including when address order wraps. *)
Definition memory_buffer_offset modulus base index := (base+4*index) mod modulus.
Lemma memory_buffer_offset_distinct modulus base extent first second :
  0 < modulus -> 4*extent <= modulus -> 0 <= first < extent -> 0 <= second < extent -> first <> second ->
  memory_buffer_offset modulus base first <> memory_buffer_offset modulus base second.
Proof.
  intros MODULUS EXTENT FIRST SECOND DISTINCT SAME.
  unfold memory_buffer_offset in SAME.
  assert (DIFF : (4*(second-first)) mod modulus = 0).
  { replace (4*(second-first)) with ((base+4*second)-(base+4*first)) by ring.
    rewrite Zminus_mod,SAME,Z.sub_diag,Z.mod_0_l by lia; reflexivity. }
  destruct (Z.lt_trichotomy first second) as [LESS|[EQUAL|MORE]]; [|contradiction|].
  - rewrite Z.mod_small in DIFF by lia; lia.
  - assert (OTHER : (4*(first-second)) mod modulus = 0).
    { replace (4*(first-second)) with ((base+4*first)-(base+4*second)) by ring.
      rewrite Zminus_mod,SAME,Z.sub_diag,Z.mod_0_l by lia; reflexivity. }
    rewrite Z.mod_small in OTHER by lia; lia.
Qed.
Lemma memory_buffer_offset_spacing modulus base first second :
  modulus <> 0 -> (4 | modulus) ->
  (4 | memory_buffer_offset modulus base first-memory_buffer_offset modulus base second).
Proof.
  intros NONZERO [size SIZE]; unfold memory_buffer_offset.
  rewrite !Z.mod_eq by exact NONZERO.
  exists (first-second-size*((base+4*first)/modulus-(base+4*second)/modulus)).
  rewrite SIZE; ring.
Qed.
Theorem memory_buffer_cell_separation modulus base extent first second :
  0 < modulus -> (4 | modulus) -> 4*extent <= modulus ->
  0 <= first < extent -> 0 <= second < extent -> first <> second ->
  memory_buffer_offset modulus base first+4 <= memory_buffer_offset modulus base second \/
    memory_buffer_offset modulus base second+4 <= memory_buffer_offset modulus base first.
Proof.
  intros MODULUS CELLS EXTENT FIRST SECOND DISTINCT.
  pose proof (@memory_buffer_offset_distinct modulus base extent first second MODULUS EXTENT FIRST SECOND DISTINCT) as DIFFERENT.
  destruct (@memory_buffer_offset_spacing modulus base first second ltac:(lia) CELLS) as [gap SPACING].
  destruct (Z.lt_trichotomy gap 0) as [NEGATIVE|[ZERO|POSITIVE]]; [left|exfalso|right]; nia.
Qed.
Lemma memory_pointer_modulus_cells : (4 | Ptrofs.modulus).
Proof.
  change (4 | two_p (Z.of_nat (if Archi.ptr64 then 64%nat else 32%nat))).
  destruct Archi.ptr64; [exists 4611686018427387904|exists 1073741824]; reflexivity.
Qed.
Definition memory_pointer_buffer_offset base index := memory_buffer_offset Ptrofs.modulus (Ptrofs.unsigned base) index.
Lemma memory_pointer_buffer_address base index :
  Ptrofs.unsigned (Ptrofs.add base (Ptrofs.repr (4*index))) = memory_pointer_buffer_offset base index.
Proof.
  unfold Ptrofs.add,memory_pointer_buffer_offset,memory_buffer_offset.
  rewrite !Ptrofs.unsigned_repr_eq,Zplus_mod_idemp_r; reflexivity.
Qed.
Definition memory_pointer_buffer_locations array block base extent (cell : MemCell) : option memory_location :=
  if Pos.eqb (arr_id cell) array then match arr_index cell with
    | [index] => if (0 <=? index) && (index <? extent)
        then Some (MemoryLocation Mint32 block (memory_pointer_buffer_offset base index)) else None
    | _ => None end else None.
Theorem memory_pointer_buffer_locations_nonalias array block base extent :
  4*extent <= Ptrofs.modulus -> locations_nonalias (memory_pointer_buffer_locations array block base extent).
Proof.
  intros EXTENT [first_id first_indices] [second_id second_indices] first_location second_location FIRST SECOND DIFFERENT.
  unfold memory_pointer_buffer_locations in FIRST,SECOND; cbn [arr_id arr_index] in FIRST,SECOND.
  destruct (Pos.eqb first_id array) eqn:FIRST_ID; try discriminate FIRST.
  destruct (Pos.eqb second_id array) eqn:SECOND_ID; try discriminate SECOND.
  apply Pos.eqb_eq in FIRST_ID,SECOND_ID; subst first_id second_id.
  destruct first_indices as [|first_index [|first_rest first_tail]]; try discriminate FIRST.
  destruct second_indices as [|second_index [|second_rest second_tail]]; try discriminate SECOND.
  destruct ((0 <=? first_index) && (first_index <? extent)) eqn:FIRST_RANGE; try discriminate FIRST.
  destruct ((0 <=? second_index) && (second_index <? extent)) eqn:SECOND_RANGE; try discriminate SECOND.
  rewrite andb_true_iff,Z.leb_le,Z.ltb_lt in FIRST_RANGE,SECOND_RANGE.
  inversion FIRST; inversion SECOND; subst first_location second_location.
  assert (DISTINCT : first_index <> second_index).
  { intro SAME; subst second_index; unfold cell_neq in DIFFERENT; cbn in DIFFERENT.
    destruct DIFFERENT as [BAD|BAD]; [congruence|apply BAD; apply veq_refl]. }
  right; change (memory_pointer_buffer_offset base first_index+4 <= memory_pointer_buffer_offset base second_index \/
    memory_pointer_buffer_offset base second_index+4 <= memory_pointer_buffer_offset base first_index).
  apply memory_buffer_cell_separation with (extent := extent);
    [pose proof Ptrofs.modulus_pos; lia|apply memory_pointer_modulus_cells|exact EXTENT|exact FIRST_RANGE|exact SECOND_RANGE|exact DISTINCT].
Qed.
Print Assumptions memory_pointer_buffer_locations_nonalias.
