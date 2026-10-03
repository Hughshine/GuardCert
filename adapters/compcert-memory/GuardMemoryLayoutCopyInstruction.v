From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST Values Memory.
From polcert.src Require Import PolyBase.
From Guard Require Import CompCertMemoryActions ClightRectangularStore ClightRectangularUpdate.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles GuardMemoryLoops
  GuardMemoryMultipleArrays GuardMemoryRegistryTransfer GuardMemoryCrossArray GuardMemoryCopyArray GuardMemoryLayoutCopy.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_layout_copy_instruction write_shape read_shape write_array read_array :=
  MemoryInstruction (rect_write_access write_shape write_array) [rect_write_access read_shape read_array]
    (AddValue (LoadedValue 0) (ConstantValue 0)).
Theorem memory_layout_copy_registry_execution entries write_entry read_entry write_shape read_shape i j before after :
  NoDup (map memory_array_id entries) -> In write_entry entries -> In read_entry entries ->
  memory_array_extent write_entry = rectangle_extent write_shape ->
  memory_array_extent read_entry = rectangle_extent read_shape ->
  0 <= i*rectangle_stride write_shape+j < rectangle_extent write_shape ->
  0 <= i*rectangle_stride read_shape+j < rectangle_extent read_shape ->
  (memory_point (memory_layout_copy_instruction write_shape read_shape (memory_array_id write_entry) (memory_array_id read_entry)) i j
    (RuntimeState (memory_array_registry entries) before) (RuntimeState (memory_array_registry entries) after) <->
   memory_action_run (memory_layout_copy_action write_shape read_shape (memory_array_block write_entry) (memory_array_block read_entry) i j)
     before after).
Proof.
  intros UNIQUE WRITE READ WRITE_EXTENT READ_EXTENT WBOUND RBOUND; unfold memory_point.
  rewrite (@resolved_instruction_execution
    (memory_layout_copy_instruction write_shape read_shape (memory_array_id write_entry) (memory_array_id read_entry)) [i;j]
    (memory_array_registry entries)
    (MemoryLocation Mint32 (memory_array_block write_entry) (4*(i*rectangle_stride write_shape+j)))
    [MemoryLocation Mint32 (memory_array_block read_entry) (4*(i*rectangle_stride read_shape+j))] before after).
  - unfold memory_layout_copy_action.
    change (memory_action_run (MemoryAction
      [MemoryLocation Mint32 (memory_array_block read_entry) (4*(i*rectangle_stride read_shape+j))]
      (MemoryLocation Mint32 (memory_array_block write_entry) (4*(i*rectangle_stride write_shape+j)))
      (fun inputs => evaluate_value [i;j] inputs (AddValue (LoadedValue 0) (ConstantValue 0)))) before after <->
      memory_action_run (MemoryAction
      [MemoryLocation Mint32 (memory_array_block read_entry) (4*(i*rectangle_stride read_shape+j))]
      (MemoryLocation Mint32 (memory_array_block write_entry) (4*(i*rectangle_stride write_shape+j)))
      memory_copy_compute) before after).
    split; intros [inputs [value [LOAD [COMPUTE STORE]]]].
    + destruct (@singleton_load_inputs _ _ _ LOAD) as [old ->].
      exists [old],value; split; [exact LOAD|]; split; [|exact STORE].
      cbn [memory_compute] in COMPUTE.
      cbn [evaluate_value nth_error] in COMPUTE; destruct old; try discriminate COMPUTE.
      rewrite Int.add_zero in COMPUTE; exact COMPUTE.
    + destruct (@singleton_load_inputs _ _ _ LOAD) as [old ->].
      exists [old],value; split; [exact LOAD|]; split; [|exact STORE].
      unfold memory_copy_compute in COMPUTE; destruct old; try discriminate COMPUTE.
      cbn [memory_compute evaluate_value nth_error]; rewrite Int.add_zero; exact COMPUTE.
  - change (memory_array_registry entries (exact_cell (rect_write_access write_shape (memory_array_id write_entry)) [i;j]) =
      Some (MemoryLocation Mint32 (memory_array_block write_entry) (4*(i*rectangle_stride write_shape+j)))).
    rewrite rect_write_cell.
    rewrite (@memory_array_registry_member entries write_entry
      (point_cell (memory_array_id write_entry) (i*rectangle_stride write_shape+j)) UNIQUE WRITE eq_refl),WRITE_EXTENT.
    apply flat_array_location_at; exact WBOUND.
  - unfold memory_read_cells,memory_layout_copy_instruction; cbn [instruction_reads map resolve_cells].
    rewrite rect_write_cell.
    rewrite (@memory_array_registry_member entries read_entry
      (point_cell (memory_array_id read_entry) (i*rectangle_stride read_shape+j)) UNIQUE READ eq_refl),READ_EXTENT.
    rewrite flat_array_location_at by exact RBOUND; reflexivity.
Qed.
Print Assumptions memory_layout_copy_registry_execution.
