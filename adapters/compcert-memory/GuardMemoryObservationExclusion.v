From Stdlib Require Import List ZArith Lia Bool.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values.
From Guard Require Import CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryNaryCompute GuardMemoryNaryAffineAccess
  GuardMemoryNaryAffineExpressions GuardMemoryNaryRanges GuardMemoryBufferOffsets GuardMemoryScalarAccess
  GuardMemoryObservationStability.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A conservative, executable footprint certificate. Each write uses the
    named buffer; its affine index has a nonnegative-coefficient box bound
    that excludes the observed logical cell. Runtime code still establishes
    the bound pointer's relation to that cell. This is not a stability axiom. *)
Definition memory_write_excludes_cell limits extent parameter observed operation :=
  let access := memory_nary_compute_write operation in
  let term := memory_nary_access_index access in
  Pos.eqb (memory_nary_access_array access) parameter && memory_nary_box_check limits extent term &&
    ((observed <? snd term) || (memory_nary_index_value term (map (fun limit => limit-1) limits) <? observed)).
Definition memory_writes_exclude_cell limits extent parameter observed operations :=
  (0 <=? observed) && (observed <? extent) && (4*extent <=? Ptrofs.modulus) &&
    forallb (memory_write_excludes_cell limits extent parameter observed) operations.

Theorem memory_write_excludes_cell_sound limits extent parameter observed operation values :
  memory_write_excludes_cell limits extent parameter observed operation = true ->
  memory_nary_ranges limits values ->
  memory_nary_access_array (memory_nary_compute_write operation) = parameter /\
    0 <= memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation)) values < extent /\
    memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation)) values <> observed.
Proof.
  unfold memory_write_excludes_cell; rewrite !andb_true_iff,Pos.eqb_eq,orb_true_iff,!Z.ltb_lt.
  intros [[ARRAY BOX] EXCLUDED] RANGE; split; [exact ARRAY|split].
  - apply memory_nary_box_sound with (limits:=limits); assumption.
  - pose proof BOX as LOWER; unfold memory_nary_box_check in LOWER; rewrite !andb_true_iff in LOWER.
    destruct LOWER as [[COEFFICIENTS _] _]; apply memory_nary_range_check_sound in COEFFICIENTS.
    pose proof (memory_nary_dot_box COEFFICIENTS RANGE) as BOUNDS.
    unfold memory_nary_index_value in *; destruct EXCLUDED; lia.
Qed.

Theorem memory_writes_exclude_cell_sound limits extent parameter observed operations temps values block base :
  memory_writes_exclude_cell limits extent parameter observed operations = true ->
  memory_nary_ranges limits values -> temps ! parameter = Some (Vptr block base) ->
  memory_pointer_writes_apart_observation temps values operations
    (MemoryLocation Mint32 block (memory_pointer_buffer_offset base observed)).
Proof.
  unfold memory_writes_exclude_cell; rewrite !andb_true_iff,!Z.leb_le,Z.ltb_lt.
  intros [[[LOW HIGH] EXTENT] CHECK] RANGE POINTER operation MEMBER other offset WRITE.
  apply forallb_forall with (x:=operation) in CHECK; [|exact MEMBER].
  destruct (@memory_write_excludes_cell_sound limits extent parameter observed operation values CHECK RANGE)
    as [ARRAY [INDEX DIFFERENT]].
  rewrite ARRAY in WRITE; assert (SAME : Vptr other offset = Vptr block base) by congruence.
  injection SAME as BLOCK OFFSET; subst other offset.
  right; change (memory_pointer_buffer_offset base
      (memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation)) values)+4 <=
      memory_pointer_buffer_offset base observed \/
    memory_pointer_buffer_offset base observed+4 <= memory_pointer_buffer_offset base
      (memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation)) values)).
  apply memory_buffer_cell_separation with (extent:=extent);
    [pose proof Ptrofs.modulus_pos; lia|apply memory_pointer_modulus_cells|exact EXTENT|exact INDEX|lia|exact DIFFERENT].
Qed.

Corollary memory_writes_exclude_cell_with_scalars limits extent parameter observed operations temps coordinates scalars block base :
  memory_writes_exclude_cell limits extent parameter observed operations = true ->
  memory_nary_ranges limits coordinates -> temps ! parameter = Some (Vptr block base) ->
  memory_pointer_writes_apart_observation temps (coordinates++scalars) operations
    (MemoryLocation Mint32 block (memory_pointer_buffer_offset base observed)).
Proof.
  intros CHECK RANGE POINTER operation MEMBER other offset WRITE.
  pose proof (@memory_writes_exclude_cell_sound limits extent parameter observed operations temps coordinates block base
    CHECK RANGE POINTER operation MEMBER other offset WRITE) as APART.
  rewrite memory_scalar_index_value; [exact APART|].
  unfold memory_writes_exclude_cell in CHECK; rewrite !andb_true_iff in CHECK.
  destruct CHECK as [_ CHECK]; apply forallb_forall with (x:=operation) in CHECK; [|exact MEMBER].
  unfold memory_write_excludes_cell,memory_nary_box_check in CHECK; rewrite !andb_true_iff in CHECK.
  destruct CHECK as [[_ [[COEFFICIENTS _] _]] _]; apply memory_nary_range_check_sound in COEFFICIENTS.
  apply Forall2_length in COEFFICIENTS; apply Forall2_length in RANGE; lia.
Qed.

Print Assumptions memory_write_excludes_cell_sound.
Print Assumptions memory_writes_exclude_cell_sound.
Print Assumptions memory_writes_exclude_cell_with_scalars.
