From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight Ctypes Cop.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightPureExpr ClightCountedLoop CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryBufferOffsets GuardMemoryPointerAccess
  GuardMemoryMultiPointerCells GuardMemoryFiniteAliasCondition GuardMemoryFootprintCapabilities
  GuardMemoryAffineSourceExpressions GuardMemoryNaryAffineExpressions.
From GuardMemory Require Import GuardMemoryAffineRenaming.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_affine_range_address pointer counter expression :=
  Ebinop Oadd (Etempvar pointer (Tpointer type_int32s noattr))
    (memory_source_affine_code (memory_source_affine_rename (fun _ => counter) expression))
    (Tpointer type_int32s noattr).

Theorem memory_affine_range_address_binding expression term original_iterator ge locals original current memory
  extent pointer counter coordinate :
  memory_encode_nary_index [original_iterator] expression = Some term ->
  extent <= Int.max_signed+1 -> current ! pointer = original ! pointer ->
  current ! counter = Some (Vint (Int.repr coordinate)) ->
  memory_cell_capable (memory_multi_pointer_locations original extent) memory
    (point_cell pointer (memory_nary_index_value term [coordinate])) ->
  memory_cell_address_binding (fun _ => memory_affine_range_address pointer counter expression)
    (memory_multi_pointer_locations original extent) (Entry ge locals current memory)
    (point_cell pointer (memory_nary_index_value term [coordinate])).
Proof.
  intros ENCODE EXTENT FRAME COUNTER [location [RESOLVE [CHUNK [VALID ALIGN]]]].
  set (index := memory_nary_index_value term [coordinate]) in *.
  destruct (@memory_multi_pointer_location_inverse original extent (point_cell pointer index) location RESOLVE)
    as [block [base [position [POINTER [CELL [RANGE SAME]]]]]].
  cbn [arr_index point_cell] in CELL; inversion CELL; subst position location.
  cbn [arr_id point_cell] in POINTER.
  assert (INDEX : signed_range index) by (unfold signed_range; change Int.min_signed with (-2147483648); lia).
  assert (AFFINE : eval_expr ge locals current memory
    (memory_source_affine_code (memory_source_affine_rename (fun _ => counter) expression)) (Vint (Int.repr index))).
  { pose proof (@memory_encode_nary_index_value expression [original_iterator] term (fun _ => coordinate) ENCODE) as MATH.
    cbn [map] in MATH; unfold index; rewrite <- MATH.
    apply memory_source_affine_rename_evaluation with (valuation := fun _ => coordinate).
    intros; exact COUNTER. }
  exists (MemoryLocation Mint32 block (memory_pointer_buffer_offset base index)),
    (Ptrofs.add base (Ptrofs.repr (4*index))).
  split; [exact RESOLVE|]; split; [reflexivity|].
  split; [cbn; symmetry; apply memory_pointer_buffer_address|].
  split.
  - unfold memory_affine_range_address; constructor; [constructor|apply memory_source_affine_pure].
  - split.
    + unfold memory_affine_range_address; reflexivity.
    + split.
      * unfold memory_affine_range_address.
        eapply eval_Ebinop with (v1 := Vptr block base) (v2 := Vint (Int.repr index)).
        -- apply eval_Etempvar; cbn [entry_temps]; rewrite FRAME; exact POINTER.
        -- exact AFFINE.
        -- rewrite memory_source_affine_type; apply memory_pointer_add; exact INDEX.
      * rewrite memory_pointer_buffer_address; exact (conj VALID ALIGN).
Qed.
Print Assumptions memory_affine_range_address_binding.
