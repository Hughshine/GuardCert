From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST Values Memory.
From polcert.src Require Import PolyBase.
From Guard Require Import CompCertMemoryActions ClightRectangularStore ClightRectangularUpdate.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles GuardMemoryLoops
  GuardMemoryMultipleArrays GuardMemoryRegistryTransfer GuardMemoryCrossArray.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_cross_instruction shape write_array read_array :=
  MemoryInstruction (rect_write_access shape write_array) [rect_write_access shape read_array]
    (rect_read_payload_expression shape).
Theorem memory_cross_registry_execution entries write_entry read_entry shape i j before after :
  NoDup (map memory_array_id entries) -> In write_entry entries -> In read_entry entries ->
  memory_array_extent write_entry = rectangle_extent shape ->
  memory_array_extent read_entry = rectangle_extent shape ->
  0 <= i*rectangle_stride shape+j < rectangle_extent shape ->
  (memory_point (memory_cross_instruction shape (memory_array_id write_entry) (memory_array_id read_entry)) i j
    (RuntimeState (memory_array_registry entries) before) (RuntimeState (memory_array_registry entries) after) <->
   memory_action_run (memory_cross_action shape (memory_array_block write_entry) (memory_array_block read_entry) i j)
     before after).
Proof.
  intros UNIQUE WRITE READ WRITE_EXTENT READ_EXTENT BOUND; unfold memory_point.
  rewrite (@resolved_instruction_execution
    (memory_cross_instruction shape (memory_array_id write_entry) (memory_array_id read_entry)) [i;j]
    (memory_array_registry entries)
    (MemoryLocation Mint32 (memory_array_block write_entry) (4*(i*rectangle_stride shape+j)))
    [MemoryLocation Mint32 (memory_array_block read_entry) (4*(i*rectangle_stride shape+j))] before after).
  - unfold memory_cross_action.
    change (memory_action_run (MemoryAction
      [MemoryLocation Mint32 (memory_array_block read_entry) (4*(i*rectangle_stride shape+j))]
      (MemoryLocation Mint32 (memory_array_block write_entry) (4*(i*rectangle_stride shape+j)))
      (fun inputs => evaluate_value [i;j] inputs (rect_read_payload_expression shape))) before after <->
      memory_action_run (MemoryAction
      [MemoryLocation Mint32 (memory_array_block read_entry) (4*(i*rectangle_stride shape+j))]
      (MemoryLocation Mint32 (memory_array_block write_entry) (4*(i*rectangle_stride shape+j)))
      (rect_update_compute shape i j)) before after).
    split; intros [inputs [value [LOAD [COMPUTE STORE]]]].
    + destruct (@singleton_load_inputs _ _ _ LOAD) as [old ->].
      exists [old],value; split; [exact LOAD|]; split; [|exact STORE].
      cbn [memory_compute] in COMPUTE; rewrite rect_read_payload_expression_value in COMPUTE; exact COMPUTE.
    + destruct (@singleton_load_inputs _ _ _ LOAD) as [old ->].
      exists [old],value; split; [exact LOAD|]; split; [|exact STORE].
      cbn [memory_compute]; rewrite rect_read_payload_expression_value; exact COMPUTE.
  - change (memory_array_registry entries (exact_cell (rect_write_access shape (memory_array_id write_entry)) [i;j]) =
      Some (MemoryLocation Mint32 (memory_array_block write_entry) (4*(i*rectangle_stride shape+j)))).
    rewrite rect_write_cell.
    rewrite (@memory_array_registry_member entries write_entry
      (point_cell (memory_array_id write_entry) (i*rectangle_stride shape+j)) UNIQUE WRITE eq_refl),WRITE_EXTENT.
    apply flat_array_location_at; exact BOUND.
  - unfold memory_read_cells,memory_cross_instruction; cbn [instruction_reads map resolve_cells].
    rewrite rect_write_cell.
    rewrite (@memory_array_registry_member entries read_entry
      (point_cell (memory_array_id read_entry) (i*rectangle_stride shape+j)) UNIQUE READ eq_refl),READ_EXTENT.
    rewrite flat_array_location_at by exact BOUND; reflexivity.
Qed.
Print Assumptions memory_cross_registry_execution.
