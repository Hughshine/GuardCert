From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRuntimeReceipts
  GuardMemoryRegistryGuard GuardMemoryFootprintRestriction GuardMemoryFiniteFootprint
  GuardMemoryFiniteAliasCondition GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorBackend
  GuardMemoryMultiTensorBackend GuardMemoryMultiTensorAddressReceipts
  GuardMemoryBooleanPairRectangle GuardMemoryMultiTensorPairScan.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Within one logical array, layout injectivity suffices. Cross-array
    separation comes from runtime comparisons, not a global pointer premise. *)
Lemma multi_tensor_same_array_separation original sizes first second loc1 loc2 :
  4 * tensor_volume sizes <= Ptrofs.modulus -> arr_id first = arr_id second ->
  multi_tensor_locations original sizes first = Some loc1 ->
  multi_tensor_locations original sizes second = Some loc2 ->
  cell_neq first second -> location_disjoint loc1 loc2.
Proof.
  intros SPAN ID FIRST SECOND DIFFERENT.
  unfold multi_tensor_locations in FIRST,SECOND; rewrite <- ID in SECOND.
  destruct (original!(arr_id first)) as [value|] eqn:POINTER; [|discriminate].
  destruct value; try discriminate.
  eapply tensor_pointer_locations_nonalias;
    [exact SPAN|exact FIRST|exact SECOND|exact DIFFERENT].
Qed.

Definition multi_tensor_pair_cell_covered counts first second cell :=
  (arr_id cell = first \/ arr_id cell = second) /\
  Forall2 (fun coordinate count => 0 <= coordinate < count) (arr_index cell) counts.

Theorem multi_tensor_pair_footprint_separation dimensions sizes original memory
    counts first second cells (ge : genv) (locals : env) :
  first <> second -> tensor_layout_flag sizes = true ->
  tensor_dimension_view dimensions sizes original -> Forall (fun count => 0 <= count) counts ->
  Forall (multi_tensor_pair_cell_covered counts first second) cells ->
  Forall (fun cell => memory_cell_access (multi_tensor_locations original sizes) memory cell Readable) cells ->
  multi_tensor_pair_check (multi_tensor_locations original sizes) counts first second = true ->
  locations_nonalias (memory_restrict_locations (memory_footprint_allowed cells)
    (multi_tensor_locations original sizes)).
Proof.
  intros DISTINCT LAYOUT DIMENSIONS COUNTS COVERED RECEIPTS CHECK.
  assert (SPAN : 4 * tensor_volume sizes <= Ptrofs.modulus).
  { pose proof (@tensor_layout_flag_sound sizes LAYOUT); tauto. }
  assert (BINDINGS : Forall (memory_cell_address_binding (multi_tensor_cell_address dimensions)
    (multi_tensor_locations original sizes) (Entry ge locals original memory)) cells).
  { eapply Forall_impl; [|exact RECEIPTS]; intros cell RECEIPT.
    eapply multi_tensor_cell_address_receipt; eassumption. }
  unfold multi_tensor_pair_check in CHECK.
  rewrite memory_boolean_pair_rectangle_member in CHECK by exact COUNTS.
  apply memory_restricted_locations_nonalias.
  intros [id1 a] [id2 b] loc1 loc2 FIRST_ALLOWED SECOND_ALLOWED FIRST SECOND DIFFERENT.
  apply memory_footprint_allowed_exact in FIRST_ALLOWED,SECOND_ALLOWED.
  rewrite Forall_forall in COVERED,BINDINGS.
  pose proof (COVERED _ FIRST_ALLOWED) as [FIRST_ID FIRST_RANGE].
  pose proof (COVERED _ SECOND_ALLOWED) as [SECOND_ID SECOND_RANGE].
  pose proof (BINDINGS _ FIRST_ALLOWED) as FIRST_BINDING.
  pose proof (BINDINGS _ SECOND_ALLOWED) as SECOND_BINDING.
  cbn [arr_id arr_index] in FIRST_ID,SECOND_ID,FIRST_RANGE,SECOND_RANGE.
  destruct FIRST_ID as [ID1|ID1]; destruct SECOND_ID as [ID2|ID2]; subst id1 id2.
  - exact (@multi_tensor_same_array_separation original sizes
      {|arr_id:=first;arr_index:=a|} {|arr_id:=first;arr_index:=b|} loc1 loc2
      SPAN eq_refl FIRST SECOND DIFFERENT).
  - eapply memory_cell_pair_address_separated; [exact FIRST_BINDING|exact SECOND_BINDING|
      exact FIRST|exact SECOND|exact DIFFERENT|].
    exact (CHECK a b FIRST_RANGE SECOND_RANGE).
  - apply location_disjoint_symmetric.
    eapply memory_cell_pair_address_separated; [exact SECOND_BINDING|exact FIRST_BINDING|
      exact SECOND|exact FIRST| |].
    + exact (proj1 (cell_neq_symm _ _) DIFFERENT).
    + exact (CHECK b a SECOND_RANGE FIRST_RANGE).
  - exact (@multi_tensor_same_array_separation original sizes
      {|arr_id:=second;arr_index:=a|} {|arr_id:=second;arr_index:=b|} loc1 loc2
      SPAN eq_refl FIRST SECOND DIFFERENT).
Qed.

Print Assumptions multi_tensor_same_array_separation.
Print Assumptions multi_tensor_pair_footprint_separation.
