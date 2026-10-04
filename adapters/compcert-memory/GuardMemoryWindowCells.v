From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight Ctypes Cop.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightPureExpr CompCertMemoryActions ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryBufferOffsets GuardMemoryPointerAccess
  GuardMemoryPointerCellComparison GuardMemoryFiniteAliasCondition GuardMemoryFootprintCapabilities GuardMemoryMultiPointerCells.
From GuardMemory Require Import GuardMemorySignedWindow.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition window_multi_pointer_locations (temps : temp_env) lower upper cell :=
  match temps ! (arr_id cell) with
  | Some (Vptr block base) => interval_pointer_locations (arr_id cell) block base lower upper cell
  | _ => None end.
Lemma window_multi_pointer_location_inverse temps lower upper cell location :
  window_multi_pointer_locations temps lower upper cell = Some location ->
  exists block base index, temps ! (arr_id cell) = Some (Vptr block base) /\
    arr_index cell = [index] /\ lower <= index < upper /\
    location = MemoryLocation Mint32 block (memory_pointer_buffer_offset base index).
Proof.
  destruct cell as [identifier indices]; unfold window_multi_pointer_locations; cbn [arr_id arr_index].
  destruct (temps ! identifier) as [pointer|] eqn:POINTER; [|discriminate].
  destruct pointer; try discriminate.
  unfold interval_pointer_locations; cbn [arr_id arr_index]; rewrite Pos.eqb_refl.
  destruct indices as [|index [|other rest]]; try discriminate.
  destruct ((lower <=? index) && (index <? upper)) eqn:RANGE; [|discriminate].
  rewrite andb_true_iff,Z.leb_le,Z.ltb_lt in RANGE; intro RESOLVE; inversion RESOLVE; subst location.
  exists b,i,index; cbn; repeat split; try reflexivity; tauto.
Qed.
Theorem window_multi_pointer_locations_int32 temps lower upper :
  memory_locations_int32 (window_multi_pointer_locations temps lower upper).
Proof.
  intros cell location RESOLVE; apply window_multi_pointer_location_inverse in RESOLVE
    as [block [base [index [POINTER [CELL [RANGE SAME]]]]]]; subst location; reflexivity.
Qed.
Theorem window_multi_pointer_cell_encoding ge locals temps memory lower upper cell :
  signed_range lower -> signed_range (upper-1) ->
  memory_cell_capable (window_multi_pointer_locations temps lower upper) memory cell ->
  memory_cell_address_binding memory_multi_pointer_cell_code (window_multi_pointer_locations temps lower upper)
    (Entry ge locals temps memory) cell.
Proof.
  intros LOW HIGH [location [RESOLVE [CHUNK [VALID ALIGN]]]].
  destruct (@window_multi_pointer_location_inverse temps lower upper cell location RESOLVE)
    as [block [base [index [POINTER [CELL [RANGE SAME]]]]]].
  subst location; cbn [location_chunk location_block location_offset] in *.
  assert (INDEX : signed_range index) by (unfold signed_range in *; lia).
  exists (MemoryLocation Mint32 block (memory_pointer_buffer_offset base index)),
    (Ptrofs.add base (Ptrofs.repr (4*index))).
  split; [exact RESOLVE|]; split; [reflexivity|].
  split; [cbn; symmetry; apply memory_pointer_buffer_address|].
  unfold memory_multi_pointer_cell_code; rewrite CELL.
  split; [constructor; constructor|]; split; [reflexivity|].
  split.
  - eapply eval_Ebinop with (v1 := Vptr block base) (v2 := Vint (Int.repr index)).
    + constructor; exact POINTER.
    + constructor.
    + cbn [typeof]; apply memory_pointer_add; exact INDEX.
  - rewrite memory_pointer_buffer_address; split; [exact VALID|exact ALIGN].
Qed.
Theorem window_multi_pointer_footprint_encoding ge locals temps memory lower upper cells :
  signed_range lower -> signed_range (upper-1) ->
  Forall (memory_cell_capable (window_multi_pointer_locations temps lower upper) memory) cells ->
  Forall (memory_cell_address_binding memory_multi_pointer_cell_code (window_multi_pointer_locations temps lower upper)
    (Entry ge locals temps memory)) cells.
Proof.
  intros LOW HIGH CELLS; eapply Forall_impl; [|exact CELLS]; intros cell CAPABLE;
    apply window_multi_pointer_cell_encoding; assumption.
Qed.
Print Assumptions window_multi_pointer_location_inverse.
Print Assumptions window_multi_pointer_footprint_encoding.
