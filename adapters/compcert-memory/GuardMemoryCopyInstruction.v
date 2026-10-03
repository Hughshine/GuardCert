From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST Values Memory.
From polcert.src Require Import PolyBase.
From Guard Require Import CompCertMemoryActions ClightRectangularStore ClightRectangularUpdate.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles GuardMemoryLoops
  GuardMemoryMultipleArrays GuardMemoryRegistryTransfer GuardMemoryCrossArray GuardMemoryCopyArray.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_copy_instruction shape write_array read_array :=
  MemoryInstruction (rect_write_access shape write_array) [rect_write_access shape read_array]
    (AddValue (LoadedValue 0) (ConstantValue 0)).
Theorem memory_copy_registry_execution entries write_entry read_entry shape i j before after :
  NoDup (map memory_array_id entries) -> In write_entry entries -> In read_entry entries ->
  memory_array_extent write_entry = rectangle_extent shape ->
  memory_array_extent read_entry = rectangle_extent shape ->
  0 <= i*rectangle_stride shape+j < rectangle_extent shape ->
  (memory_point (memory_copy_instruction shape (memory_array_id write_entry) (memory_array_id read_entry)) i j
    (RuntimeState (memory_array_registry entries) before) (RuntimeState (memory_array_registry entries) after) <->
   memory_action_run (memory_copy_action shape (memory_array_block write_entry) (memory_array_block read_entry) i j)
     before after).
Proof.
  intros UNIQUE WRITE READ WRITE_EXTENT READ_EXTENT BOUND; unfold memory_point.
  rewrite (@resolved_instruction_execution
    (memory_copy_instruction shape (memory_array_id write_entry) (memory_array_id read_entry)) [i;j]
    (memory_array_registry entries)
    (MemoryLocation Mint32 (memory_array_block write_entry) (4*(i*rectangle_stride shape+j)))
    [MemoryLocation Mint32 (memory_array_block read_entry) (4*(i*rectangle_stride shape+j))] before after).
  - unfold memory_copy_action.
    change (memory_action_run (MemoryAction
      [MemoryLocation Mint32 (memory_array_block read_entry) (4*(i*rectangle_stride shape+j))]
      (MemoryLocation Mint32 (memory_array_block write_entry) (4*(i*rectangle_stride shape+j)))
      (fun inputs => evaluate_value [i;j] inputs (AddValue (LoadedValue 0) (ConstantValue 0)))) before after <->
      memory_action_run (MemoryAction
      [MemoryLocation Mint32 (memory_array_block read_entry) (4*(i*rectangle_stride shape+j))]
      (MemoryLocation Mint32 (memory_array_block write_entry) (4*(i*rectangle_stride shape+j)))
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
  - change (memory_array_registry entries (exact_cell (rect_write_access shape (memory_array_id write_entry)) [i;j]) =
      Some (MemoryLocation Mint32 (memory_array_block write_entry) (4*(i*rectangle_stride shape+j)))).
    rewrite rect_write_cell.
    rewrite (@memory_array_registry_member entries write_entry
      (point_cell (memory_array_id write_entry) (i*rectangle_stride shape+j)) UNIQUE WRITE eq_refl),WRITE_EXTENT.
    apply flat_array_location_at; exact BOUND.
  - unfold memory_read_cells,memory_copy_instruction; cbn [instruction_reads map resolve_cells].
    rewrite rect_write_cell.
    rewrite (@memory_array_registry_member entries read_entry
      (point_cell (memory_array_id read_entry) (i*rectangle_stride shape+j)) UNIQUE READ eq_refl),READ_EXTENT.
    rewrite flat_array_location_at by exact BOUND; reflexivity.
Qed.
Print Assumptions memory_copy_registry_execution.
