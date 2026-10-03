From Stdlib Require Import Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import Values.
From polcert.src Require Import PolyBase.
From Guard Require Import CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryBufferOffsets
  GuardMemoryMultiPointerCells GuardMemoryFootprintRestriction.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem memory_multi_pointer_same_identifier_nonalias temps extent first second first_location second_location :
  4*extent <= Ptrofs.modulus ->
  arr_id first = arr_id second ->
  memory_multi_pointer_locations temps extent first = Some first_location ->
  memory_multi_pointer_locations temps extent second = Some second_location ->
  cell_neq first second -> location_disjoint first_location second_location.
Proof.
  intros EXTENT SAME FIRST SECOND DIFFERENT.
  unfold memory_multi_pointer_locations in FIRST,SECOND.
  rewrite <- SAME in SECOND.
  destruct (temps ! (arr_id first)) as [pointer|]; [|discriminate FIRST].
  destruct pointer; try discriminate FIRST.
  eapply memory_pointer_buffer_locations_nonalias; eassumption.
Qed.

Definition memory_cross_pointer_separated_on allowed locations :=
  forall first second first_location second_location,
    allowed first = true -> allowed second = true ->
    arr_id first <> arr_id second ->
    locations first = Some first_location -> locations second = Some second_location ->
    location_disjoint first_location second_location.

Theorem memory_cross_pointer_separation_suffices allowed temps extent :
  4*extent <= Ptrofs.modulus ->
  memory_cross_pointer_separated_on allowed (memory_multi_pointer_locations temps extent) ->
  locations_nonalias (memory_restrict_locations allowed (memory_multi_pointer_locations temps extent)).
Proof.
  intros EXTENT CROSS; apply memory_restricted_locations_nonalias.
  intros first second first_location second_location FIRST_ALLOWED SECOND_ALLOWED FIRST SECOND DIFFERENT.
  destruct (Pos.eq_dec (arr_id first) (arr_id second)) as [SAME|DISTINCT].
  - exact (@memory_multi_pointer_same_identifier_nonalias temps extent first second
      first_location second_location EXTENT SAME FIRST SECOND DIFFERENT).
  - exact (CROSS first second first_location second_location FIRST_ALLOWED SECOND_ALLOWED DISTINCT FIRST SECOND).
Qed.
Print Assumptions memory_cross_pointer_separation_suffices.
