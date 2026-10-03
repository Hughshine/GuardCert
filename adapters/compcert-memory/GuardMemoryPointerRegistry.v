From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightRectangularStore CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryArrayBackend
  GuardMemoryLoops GuardMemoryRectangles GuardMemoryNaryAffineAccess GuardMemoryNaryAffineExpressions GuardMemoryNaryAccessCheck GuardMemoryNaryRanges GuardMemoryNaryCompute
  GuardMemoryPointerAccess GuardMemoryPointerCompute GuardMemoryBufferOffsets.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_pointer_read_location block base values access := MemoryLocation Mint32 block
  (memory_pointer_buffer_offset base (memory_nary_index_value (memory_nary_access_index access) values)).
Lemma memory_pointer_access_registry limits layout pointer extent access block base values :
  memory_pointer_access_valid limits layout pointer extent access -> memory_nary_ranges limits values ->
  memory_pointer_buffer_locations pointer block base extent (exact_cell (memory_nary_access_instruction access) values) =
    Some (memory_pointer_read_location block base values access).
Proof.
  intros [[VALID [ENCODE BOUND]] [ID EXTENT]] RANGE.
  rewrite memory_nary_access_cell,ID; apply memory_pointer_buffer_location_at; rewrite <- EXTENT; apply BOUND; exact RANGE.
Qed.
Lemma memory_pointer_reads_resolve limits layout pointer extent accesses block base values :
  Forall (memory_pointer_access_valid limits layout pointer extent) accesses -> memory_nary_ranges limits values ->
  resolve_cells (map (fun access => exact_cell (memory_nary_access_instruction access) values) accesses)
    (memory_pointer_buffer_locations pointer block base extent) = Some (map (memory_pointer_read_location block base values) accesses).
Proof.
  intros CERT RANGE; induction CERT; cbn [map resolve_cells]; [reflexivity|].
  rewrite (@memory_pointer_access_registry limits layout pointer extent x block base values H RANGE),IHCERT; reflexivity.
Qed.
Lemma memory_pointer_reads_loads block base values accesses : forall memory loaded,
  Forall2 (memory_pointer_access_loaded block base values memory) accesses loaded <->
    load_locations (map (memory_pointer_read_location block base values) accesses) memory = Some loaded.
Proof.
  induction accesses as [|access accesses IH]; intros memory loaded.
  - split; intro LOAD; [inversion LOAD; reflexivity|cbn in LOAD; inversion LOAD; constructor].
  - cbn [map load_locations memory_pointer_read_location location_load location_chunk location_block location_offset].
    unfold location_load; cbn [memory_pointer_read_location location_chunk location_block location_offset].
    split; intro LOAD.
    + inversion LOAD; subst.
      match goal with
      | HEAD : memory_pointer_access_loaded _ _ _ _ _ _ |- _ => unfold memory_pointer_access_loaded in HEAD; rewrite HEAD
      | HEAD : Mem.load _ _ _ _ = Some _ |- _ => rewrite HEAD end.
      match goal with TAIL : Forall2 _ accesses _ |- _ => apply (proj1 (IH memory _)) in TAIL; rewrite TAIL end; reflexivity.
    + destruct (Mem.load Mint32 memory block (memory_pointer_buffer_offset base (memory_nary_index_value (memory_nary_access_index access) values)))
        as [value|] eqn:VALUE; [|discriminate].
      destruct (load_locations (map (memory_pointer_read_location block base values) accesses) memory) as [rest|] eqn:REST; [|discriminate].
      inversion LOAD; subst; constructor; [exact VALUE|apply (proj2 (IH memory _)); exact REST].
Qed.
Theorem memory_pointer_compute_registry limits layout pointer extent operation block base values before after :
  memory_pointer_compute_valid limits layout pointer extent operation -> memory_nary_ranges limits values ->
  (memory_pointer_compute_physical block base values operation before after <->
    memory_nary_point (memory_nary_compute_instruction operation) values
      (RuntimeState (memory_pointer_buffer_locations pointer block base extent) before)
      (RuntimeState (memory_pointer_buffer_locations pointer block base extent) after)).
Proof.
  intros [WRITE [READS OTHER]] RANGE.
  assert (WR : memory_pointer_buffer_locations pointer block base extent
    (exact_cell (instruction_write (memory_nary_compute_instruction operation)) values) =
      Some (memory_pointer_read_location block base values (memory_nary_compute_write operation)))
    by (eapply memory_pointer_access_registry; eassumption).
  assert (RD : resolve_cells (memory_read_cells (memory_nary_compute_instruction operation) values)
    (memory_pointer_buffer_locations pointer block base extent) =
      Some (map (memory_pointer_read_location block base values) (memory_nary_compute_reads operation))).
  { unfold memory_read_cells; cbn [memory_nary_compute_instruction instruction_reads]; rewrite map_map;
    apply memory_pointer_reads_resolve with (limits := limits) (layout := layout); assumption. }
  unfold memory_nary_point.
  rewrite (@resolved_instruction_execution (memory_nary_compute_instruction operation) values
    (memory_pointer_buffer_locations pointer block base extent)
    (memory_pointer_read_location block base values (memory_nary_compute_write operation))
    (map (memory_pointer_read_location block base values) (memory_nary_compute_reads operation)) before after WR RD).
  unfold memory_pointer_compute_physical; cbn [memory_pointer_read_location location_store location_chunk location_block location_offset].
  split; intros [loaded [value [LOAD [COMPUTE STORE]]]]; exists loaded,value; split; [|split; assumption| |split; assumption].
  - apply (proj1 (memory_pointer_reads_loads block base values (memory_nary_compute_reads operation) before loaded)); exact LOAD.
  - apply (proj2 (memory_pointer_reads_loads block base values (memory_nary_compute_reads operation) before loaded)); exact LOAD.
Qed.
Print Assumptions memory_pointer_compute_registry.
