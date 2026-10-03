From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight Ctypes Cop.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightPureExpr CompCertMemoryActions ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryBufferOffsets GuardMemoryPointerAccess
  GuardMemoryPointerCellComparison GuardMemoryFiniteAliasCondition GuardMemoryFootprintCapabilities.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_multi_pointer_locations (temps : temp_env) extent cell :=
  match temps ! (arr_id cell) with
  | Some (Vptr block base) => memory_pointer_buffer_locations (arr_id cell) block base extent cell
  | _ => None end.
Definition memory_multi_pointer_cell_code cell :=
  match arr_index cell with
  | [index] => Ebinop Oadd (Etempvar (arr_id cell) (Tpointer type_int32s noattr))
      (Econst_int (Int.repr index) type_int32s) (Tpointer type_int32s noattr)
  | _ => Econst_int Int.zero type_int32s end.
Lemma memory_multi_pointer_location_inverse temps extent cell location :
  memory_multi_pointer_locations temps extent cell = Some location ->
  exists block base index, temps ! (arr_id cell) = Some (Vptr block base) /\
    arr_index cell = [index] /\ 0 <= index < extent /\
    location = MemoryLocation Mint32 block (memory_pointer_buffer_offset base index).
Proof.
  destruct cell as [identifier indices]; unfold memory_multi_pointer_locations; cbn [arr_id arr_index].
  destruct (temps ! identifier) as [pointer|] eqn:POINTER; [|discriminate].
  destruct pointer; try discriminate.
  unfold memory_pointer_buffer_locations; cbn [arr_id arr_index]; rewrite Pos.eqb_refl.
  destruct indices as [|index [|other rest]]; try discriminate.
  destruct ((0 <=? index) && (index <? extent)) eqn:RANGE; [|discriminate].
  rewrite andb_true_iff,Z.leb_le,Z.ltb_lt in RANGE; intro RESOLVE; inversion RESOLVE; subst location.
  exists b,i,index; cbn; repeat split; try reflexivity; tauto.
Qed.
Theorem memory_multi_pointer_locations_int32 temps extent :
  memory_locations_int32 (memory_multi_pointer_locations temps extent).
Proof.
  intros cell location RESOLVE; apply memory_multi_pointer_location_inverse in RESOLVE
    as [block [base [index [POINTER [CELL [RANGE SAME]]]]]]; subst location; reflexivity.
Qed.
Theorem memory_multi_pointer_cell_encoding ge locals temps memory extent cell :
  extent <= Int.max_signed+1 ->
  memory_cell_capable (memory_multi_pointer_locations temps extent) memory cell ->
  memory_cell_address_binding memory_multi_pointer_cell_code (memory_multi_pointer_locations temps extent)
    (Entry ge locals temps memory) cell.
Proof.
  intros EXTENT [location [RESOLVE [CHUNK [VALID ALIGN]]]].
  destruct (@memory_multi_pointer_location_inverse temps extent cell location RESOLVE)
    as [block [base [index [POINTER [CELL [RANGE SAME]]]]]].
  subst location; cbn [location_chunk location_block location_offset] in *.
  assert (INDEX : signed_range index).
  { unfold signed_range; change Int.min_signed with (-2147483648); lia. }
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
Theorem memory_multi_pointer_footprint_encoding ge locals temps memory extent cells :
  extent <= Int.max_signed+1 ->
  Forall (memory_cell_capable (memory_multi_pointer_locations temps extent) memory) cells ->
  Forall (memory_cell_address_binding memory_multi_pointer_cell_code (memory_multi_pointer_locations temps extent)
    (Entry ge locals temps memory)) cells.
Proof.
  intros EXTENT CELLS; eapply Forall_impl; [|exact CELLS]; intros cell CAPABLE;
    apply memory_multi_pointer_cell_encoding; assumption.
Qed.
Print Assumptions memory_multi_pointer_locations_int32.
Print Assumptions memory_multi_pointer_cell_encoding.
Print Assumptions memory_multi_pointer_footprint_encoding.
