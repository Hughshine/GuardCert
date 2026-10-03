From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightRectangularStore CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryArrayBackend
  GuardMemoryLoops GuardMemoryRectangles GuardMemoryNaryAffineAccess GuardMemoryNaryAffineExpressions GuardMemoryNaryAccessCheck GuardMemoryNaryRanges GuardMemoryNaryCompute
  GuardMemoryPointerAccess GuardMemoryPointerCompute GuardMemoryBufferOffsets.
From GuardMemory Require Import GuardMemoryPointerRegistry GuardMemoryScalarAccess GuardMemoryScalarPointerCompute.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_scalar_pointer_full_registry limits layout pointer extent access block base coordinates values :
  memory_pointer_access_valid limits layout pointer extent access -> memory_nary_ranges limits coordinates ->
  length coordinates = length layout ->
  memory_pointer_buffer_locations pointer block base extent (exact_cell (memory_nary_access_instruction access) (coordinates++values)) =
    Some (memory_pointer_read_location block base (coordinates++values) access).
Proof.
  intros VALID RANGES LENGTH.
  rewrite (@memory_scalar_pointer_access_registry limits layout pointer extent access block base coordinates values VALID RANGES LENGTH).
  unfold memory_pointer_read_location; rewrite memory_scalar_index_value; [reflexivity|].
  rewrite (@memory_encode_nary_index_length layout _ _ (proj1 (proj2 (proj1 VALID)))),LENGTH; reflexivity.
Qed.
Lemma memory_scalar_pointer_reads_resolve limits layout pointer extent accesses block base coordinates values :
  Forall (memory_pointer_access_valid limits layout pointer extent) accesses -> memory_nary_ranges limits coordinates ->
  length coordinates = length layout ->
  resolve_cells (map (fun access => exact_cell (memory_nary_access_instruction access) (coordinates++values)) accesses)
    (memory_pointer_buffer_locations pointer block base extent) =
    Some (map (memory_pointer_read_location block base (coordinates++values)) accesses).
Proof.
  intros CERT RANGES LENGTH; induction CERT; cbn [map resolve_cells]; [reflexivity|].
  rewrite (@memory_scalar_pointer_full_registry limits layout pointer extent x block base coordinates values H RANGES LENGTH),IHCERT; reflexivity.
Qed.
Theorem memory_scalar_pointer_compute_registry limits layout scalars pointer extent operation block base coordinates values before after :
  memory_scalar_pointer_compute_valid limits layout scalars pointer extent operation -> memory_nary_ranges limits coordinates ->
  length coordinates = length layout ->
  (memory_pointer_compute_physical block base (coordinates++values) operation before after <->
    memory_nary_point (memory_nary_compute_instruction operation) (coordinates++values)
      (RuntimeState (memory_pointer_buffer_locations pointer block base extent) before)
      (RuntimeState (memory_pointer_buffer_locations pointer block base extent) after)).
Proof.
  intros [WRITE [READS OTHER]] RANGE LENGTH.
  assert (WR : memory_pointer_buffer_locations pointer block base extent
    (exact_cell (instruction_write (memory_nary_compute_instruction operation)) (coordinates++values)) =
      Some (memory_pointer_read_location block base (coordinates++values) (memory_nary_compute_write operation)))
    by (eapply memory_scalar_pointer_full_registry; eassumption).
  assert (RD : resolve_cells (memory_read_cells (memory_nary_compute_instruction operation) (coordinates++values))
    (memory_pointer_buffer_locations pointer block base extent) =
      Some (map (memory_pointer_read_location block base (coordinates++values)) (memory_nary_compute_reads operation))).
  { unfold memory_read_cells; cbn [memory_nary_compute_instruction instruction_reads]; rewrite map_map;
    apply memory_scalar_pointer_reads_resolve with (limits := limits) (layout := layout); assumption. }
  unfold memory_nary_point.
  rewrite (@resolved_instruction_execution (memory_nary_compute_instruction operation) (coordinates++values)
    (memory_pointer_buffer_locations pointer block base extent)
    (memory_pointer_read_location block base (coordinates++values) (memory_nary_compute_write operation))
    (map (memory_pointer_read_location block base (coordinates++values)) (memory_nary_compute_reads operation)) before after WR RD).
  unfold memory_pointer_compute_physical; cbn [memory_pointer_read_location location_store location_chunk location_block location_offset].
  split; intros [loaded [value [LOAD [COMPUTE STORE]]]]; exists loaded,value; split; [|split; assumption| |split; assumption].
  - apply (proj1 (memory_pointer_reads_loads block base (coordinates++values) (memory_nary_compute_reads operation) before loaded)); exact LOAD.
  - apply (proj2 (memory_pointer_reads_loads block base (coordinates++values) (memory_nary_compute_reads operation) before loaded)); exact LOAD.
Qed.
Print Assumptions memory_scalar_pointer_compute_registry.
