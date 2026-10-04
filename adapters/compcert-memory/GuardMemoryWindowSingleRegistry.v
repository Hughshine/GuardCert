From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values.
From polcert.src Require Import PolyBase.
From Guard Require Import CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryFootprintRestriction.
From GuardMemory Require Import GuardMemorySignedWindow GuardMemoryWindowCells.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition window_single_locations pointer temps lower upper :=
  memory_restrict_locations (fun cell => Pos.eqb (arr_id cell) pointer)
    (window_multi_pointer_locations temps lower upper).
Lemma window_single_location_exact pointer temps lower upper block base cell :
  temps ! pointer = Some (Vptr block base) ->
  window_single_locations pointer temps lower upper cell =
  interval_pointer_locations pointer block base lower upper cell.
Proof.
  intro POINTER; unfold window_single_locations,memory_restrict_locations,window_multi_pointer_locations.
  destruct (Pos.eqb (arr_id cell) pointer) eqn:IDENTIFIER.
  - apply Pos.eqb_eq in IDENTIFIER; rewrite IDENTIFIER,POINTER; reflexivity.
  - unfold interval_pointer_locations; rewrite IDENTIFIER; reflexivity.
Qed.
Theorem window_single_locations_nonalias pointer temps lower upper :
  4*(upper-lower) <= Ptrofs.modulus -> locations_nonalias (window_single_locations pointer temps lower upper).
Proof.
  intros EXTENT first second left right FIRST SECOND DISTINCT.
  unfold window_single_locations in FIRST,SECOND.
  apply memory_restrict_location_inverse in FIRST as [FIRST_ID FIRST].
  apply memory_restrict_location_inverse in SECOND as [SECOND_ID SECOND].
  apply Pos.eqb_eq in FIRST_ID,SECOND_ID.
  destruct (@window_multi_pointer_location_inverse temps lower upper first left FIRST)
    as [block [base [index [POINTER [CELL [RANGE SAME]]]]]].
  rewrite FIRST_ID in POINTER.
  assert (LEFT : interval_pointer_locations pointer block base lower upper first = Some left).
  { rewrite <-(@window_single_location_exact pointer temps lower upper block base first POINTER).
    unfold window_single_locations,memory_restrict_locations; rewrite FIRST_ID,Pos.eqb_refl; exact FIRST. }
  assert (RIGHT : interval_pointer_locations pointer block base lower upper second = Some right).
  { rewrite <-(@window_single_location_exact pointer temps lower upper block base second POINTER).
    unfold window_single_locations,memory_restrict_locations; rewrite SECOND_ID,Pos.eqb_refl; exact SECOND. }
  exact (@interval_pointer_locations_nonalias pointer block base lower upper EXTENT first second left right LEFT RIGHT DISTINCT).
Qed.
Print Assumptions window_single_locations_nonalias.
