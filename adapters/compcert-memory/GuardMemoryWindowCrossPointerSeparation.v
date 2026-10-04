From Stdlib Require Import Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import Values.
From polcert.src Require Import PolyBase.
From Guard Require Import CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryFootprintRestriction GuardMemoryCrossPointerSeparation.
From GuardMemory Require Import GuardMemorySignedWindow GuardMemoryWindowCells.
Set Implicit Arguments.
Local Open Scope Z_scope.
Theorem window_same_identifier_nonalias temps lower upper first second first_location second_location :
  4*(upper-lower) <= Ptrofs.modulus ->
  arr_id first = arr_id second ->
  window_multi_pointer_locations temps lower upper first = Some first_location ->
  window_multi_pointer_locations temps lower upper second = Some second_location ->
  cell_neq first second -> location_disjoint first_location second_location.
Proof.
  intros WIDTH SAME FIRST SECOND DIFFERENT.
  unfold window_multi_pointer_locations in FIRST,SECOND; rewrite <-SAME in SECOND.
  destruct (temps ! (arr_id first)) as [pointer|]; [|discriminate FIRST].
  destruct pointer; try discriminate FIRST.
  eapply interval_pointer_locations_nonalias; eassumption.
Qed.
Theorem window_cross_pointer_separation_suffices allowed temps lower upper :
  4*(upper-lower) <= Ptrofs.modulus ->
  memory_cross_pointer_separated_on allowed (window_multi_pointer_locations temps lower upper) ->
  locations_nonalias (memory_restrict_locations allowed (window_multi_pointer_locations temps lower upper)).
Proof.
  intros WIDTH CROSS; apply memory_restricted_locations_nonalias.
  intros first second first_location second_location FIRST_ALLOWED SECOND_ALLOWED FIRST SECOND DIFFERENT.
  destruct (Pos.eq_dec (arr_id first) (arr_id second)) as [SAME|DISTINCT].
  - exact (@window_same_identifier_nonalias temps lower upper first second first_location second_location WIDTH SAME FIRST SECOND DIFFERENT).
  - exact (CROSS first second first_location second_location FIRST_ALLOWED SECOND_ALLOWED DISTINCT FIRST SECOND).
Qed.
Print Assumptions window_same_identifier_nonalias.
Print Assumptions window_cross_pointer_separation_suffices.
