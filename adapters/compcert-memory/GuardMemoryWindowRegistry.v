From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From polcert.src Require Import PolyBase.
From Guard Require Import CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryNaryAffineAccess
  GuardMemoryNaryAffineExpressions GuardMemoryScalarAccess GuardMemoryMultiPointerAccess GuardMemoryMultiPointerCompute
  GuardMemoryBufferOffsets GuardMemoryRectangles GuardMemoryNaryCompute.
From GuardMemory Require Import GuardMemoryIntervalBox GuardMemoryWindowAccess GuardMemoryWindowCompute GuardMemoryWindowCells.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Lemma window_multi_access_registry bounds lower upper layout temps access block base values :
  window_access_valid bounds lower upper layout access -> interval_ranges bounds values ->
  temps ! (memory_nary_access_array access) = Some (Vptr block base) ->
  window_multi_pointer_locations temps lower upper (exact_cell (memory_nary_access_instruction access) values) =
    Some (MemoryLocation Mint32 block (memory_pointer_buffer_offset base
      (memory_nary_index_value (memory_nary_access_index access) values))).
Proof.
  intros VALID RANGE POINTER.
  pose proof (@window_access_registry access bounds lower upper layout block base values VALID RANGE) as RESOLVE.
  unfold window_multi_pointer_locations; rewrite memory_nary_access_cell; cbn [arr_id point_cell]; rewrite POINTER.
  rewrite memory_nary_access_cell in RESOLVE; exact RESOLVE.
Qed.
Lemma window_scalar_access_registry bounds lower upper layout temps access block base coordinates values :
  window_access_valid bounds lower upper layout access -> interval_ranges bounds coordinates ->
  length coordinates = length layout ->
  temps ! (memory_nary_access_array access) = Some (Vptr block base) ->
  window_multi_pointer_locations temps lower upper
    (exact_cell (memory_nary_access_instruction access) (coordinates++values)) =
    Some (MemoryLocation Mint32 block (memory_pointer_buffer_offset base
      (memory_nary_index_value (memory_nary_access_index access) coordinates))).
Proof.
  intros VALID RANGE LENGTH POINTER.
  rewrite (@memory_scalar_access_cell layout access coordinates values (proj1 (proj2 (proj2 VALID))) LENGTH).
  eapply window_multi_access_registry; eassumption.
Qed.
Lemma window_access_resolution temps lower upper access values location :
  window_multi_pointer_locations temps lower upper (exact_cell (memory_nary_access_instruction access) values) = Some location ->
  exists block base, temps ! (memory_nary_access_array access) = Some (Vptr block base) /\
    location = MemoryLocation Mint32 block (memory_pointer_buffer_offset base
      (memory_nary_index_value (memory_nary_access_index access) values)).
Proof.
  intro RESOLVE; rewrite memory_nary_access_cell in RESOLVE.
  apply window_multi_pointer_location_inverse in RESOLVE as [block [base [index [POINTER [CELL [RANGE SAME]]]]]].
  cbn [arr_id arr_index] in POINTER,CELL; inversion CELL; subst index.
  exists block,base; auto.
Qed.
Lemma window_resolved_read_load temps lower upper access values location memory value :
  window_multi_pointer_locations temps lower upper (exact_cell (memory_nary_access_instruction access) values) = Some location ->
  location_load location memory = Some value ->
  memory_multi_pointer_access_loaded temps values memory access value.
Proof.
  intros RESOLVE LOAD; destruct (@window_access_resolution temps lower upper access values location RESOLVE) as [block [base [POINTER SAME]]].
  subst location; exists block,base; split; [exact POINTER|exact LOAD].
Qed.
Lemma window_reads_resolved_inverse temps lower upper accesses values cells memory loaded :
  resolve_cells (map (fun access => exact_cell (memory_nary_access_instruction access) values) accesses)
    (window_multi_pointer_locations temps lower upper) = Some cells ->
  load_locations cells memory = Some loaded ->
  Forall2 (memory_multi_pointer_access_loaded temps values memory) accesses loaded.
Proof.
  revert cells loaded; induction accesses as [|access accesses IH]; intros cells loaded RESOLVE LOAD.
  - cbn in RESOLVE; inversion RESOLVE; subst; cbn in LOAD; inversion LOAD; constructor.
  - cbn [map resolve_cells] in RESOLVE.
    destruct (window_multi_pointer_locations temps lower upper (exact_cell (memory_nary_access_instruction access) values))
      as [location|] eqn:LOCATION; [|discriminate].
    destruct (resolve_cells (map (fun access => exact_cell (memory_nary_access_instruction access) values) accesses)
      (window_multi_pointer_locations temps lower upper)) as [rest|] eqn:REST; [|discriminate].
    inversion RESOLVE; subst cells; cbn [load_locations] in LOAD.
    destruct (location_load location memory) as [value|] eqn:VALUE; [|discriminate].
    destruct (load_locations rest memory) as [values_loaded|] eqn:TAIL; [|discriminate].
    inversion LOAD; subst loaded; constructor.
    + eapply window_resolved_read_load; eassumption.
    + exact (IH rest values_loaded eq_refl TAIL).
Qed.
Lemma window_reads_resolved_forward bounds lower upper layout temps accesses coordinates scalars memory loaded :
  Forall (window_access_valid bounds lower upper layout) accesses ->
  interval_ranges bounds coordinates -> length coordinates = length layout ->
  Forall2 (memory_multi_pointer_access_loaded temps (coordinates++scalars) memory) accesses loaded ->
  exists cells, resolve_cells (map (fun access => exact_cell (memory_nary_access_instruction access) (coordinates++scalars)) accesses)
    (window_multi_pointer_locations temps lower upper) = Some cells /\ load_locations cells memory = Some loaded.
Proof.
  intros CERT RANGE LENGTH LOAD; induction LOAD as [|access value accesses loaded HEAD TAIL IH];
    [exists []; split; reflexivity|].
  inversion CERT; subst; destruct HEAD as [block [base [POINTER VALUE]]].
  destruct (IH ltac:(assumption)) as [rest [RESOLVE LOAD]].
  set (location := MemoryLocation Mint32 block (memory_pointer_buffer_offset base
    (memory_nary_index_value (memory_nary_access_index access) coordinates))).
  assert (HEAD_RESOLVE : window_multi_pointer_locations temps lower upper
    (exact_cell (memory_nary_access_instruction access) (coordinates++scalars)) = Some location)
    by (eapply window_scalar_access_registry; eassumption).
  assert (HEAD_LOAD : location_load location memory = Some value).
  { unfold location,location_load; cbn [location_chunk location_block location_offset].
    match goal with VALID : window_access_valid _ _ _ _ access |- _ =>
      destruct VALID as [LOW [HIGH [ENCODE BOUND]]];
      rewrite (@memory_scalar_index_value (memory_nary_access_index access) coordinates scalars
        ltac:(rewrite (@memory_encode_nary_index_length layout _ _ ENCODE),LENGTH; reflexivity)) in VALUE;
      exact VALUE end. }
  exists (location::rest); cbn [map resolve_cells load_locations]; rewrite HEAD_RESOLVE,RESOLVE,HEAD_LOAD,LOAD; split; reflexivity.
Qed.
Theorem window_compute_registry bounds lower upper layout scalars operation temps coordinates values before after :
  window_compute_valid bounds lower upper layout scalars operation ->
  interval_ranges bounds coordinates -> length coordinates = length layout ->
  (memory_multi_pointer_compute_physical temps (coordinates++values) operation before after <->
   memory_nary_point (memory_nary_compute_instruction operation) (coordinates++values)
    (RuntimeState (window_multi_pointer_locations temps lower upper) before)
    (RuntimeState (window_multi_pointer_locations temps lower upper) after)).
Proof.
  intros [WRITE [READS REST]] RANGE LENGTH.
  assert (INDEX : memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation))
    (coordinates++values) = memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation)) coordinates).
  { apply memory_scalar_index_value; destruct WRITE as [LOW [HIGH [ENCODE BOUND]]].
    rewrite (@memory_encode_nary_index_length layout _ _ ENCODE),LENGTH; reflexivity. }
  split.
  - intros [block [base [loaded [value [POINTER [LOADS [COMPUTE STORE]]]]]]].
    destruct (@window_reads_resolved_forward bounds lower upper layout temps
      (memory_nary_compute_reads operation) coordinates values before loaded READS RANGE LENGTH LOADS)
      as [read_locations [RESOLVE LOAD]].
    unfold memory_nary_point,GuardMemoryInstr.instr_semantics; split; [reflexivity|]; split; [reflexivity|].
    unfold footprint_run; cbn [runtime_locations runtime_memory].
    exists (MemoryLocation Mint32 block (memory_pointer_buffer_offset base
      (memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation)) coordinates))),read_locations.
    split.
    + cbn [memory_nary_compute_instruction instruction_write]; eapply window_scalar_access_registry; eassumption.
    + split.
      * unfold memory_read_cells; cbn [memory_nary_compute_instruction instruction_reads]; rewrite map_map; exact RESOLVE.
      * split; [reflexivity|].
        exists loaded,value; split; [exact LOAD|]; split; [exact COMPUTE|].
        change (Mem.store Mint32 before block (memory_pointer_buffer_offset base
          (memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation)) coordinates)) value = Some after).
        rewrite INDEX in STORE; exact STORE.
  - intros [WRITES [READ_CELLS [write [read_locations [RESOLVE [READ_RESOLVE [FRAME [loaded [value [LOAD [COMPUTE STORE]]]]]]]]]]].
    cbn [runtime_locations runtime_memory memory_nary_compute_instruction instruction_write instruction_reads] in RESOLVE,READ_RESOLVE.
    destruct (@window_access_resolution temps lower upper (memory_nary_compute_write operation)
      (coordinates++values) write RESOLVE) as [block [base [POINTER SAME]]].
    subst write; exists block,base,loaded,value; split; [exact POINTER|]; split.
    + eapply window_reads_resolved_inverse; [|exact LOAD].
      unfold memory_read_cells in READ_RESOLVE; cbn [memory_nary_compute_instruction instruction_reads] in READ_RESOLVE;
      rewrite map_map in READ_RESOLVE; exact READ_RESOLVE.
    + split; [exact COMPUTE|exact STORE].
Qed.
Print Assumptions window_access_resolution.
Print Assumptions window_reads_resolved_inverse.
Print Assumptions window_reads_resolved_forward.
Print Assumptions window_compute_registry.
