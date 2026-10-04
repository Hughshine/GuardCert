From Stdlib Require Import List ZArith.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryNaryCompute GuardMemoryNaryAffineAccess
  GuardMemoryScalarAccess GuardMemoryInstructionPadding GuardMemoryFiniteFootprint GuardMemoryMultiPointerFootprint
  GuardMemoryRectangularFootprint GuardMemoryLoops.
From GuardMemory Require Import GuardMemoryWindowAccess GuardMemoryWindowCompute.
Import ListNotations.
Set Implicit Arguments.
Lemma window_operation_footprint_prefix bounds lower upper layout scalars operation coordinates values :
  window_compute_valid bounds lower upper layout scalars operation -> length coordinates = length layout ->
  memory_instruction_footprint (memory_nary_compute_instruction operation) (coordinates++values) =
    memory_instruction_footprint (memory_nary_compute_instruction operation) coordinates.
Proof.
  intros [WRITE [READS REST]] LENGTH.
  unfold memory_instruction_footprint; cbn [memory_nary_compute_instruction instruction_write instruction_reads].
  rewrite map_map,map_map.
  rewrite (@memory_scalar_access_cell layout (memory_nary_compute_write operation) coordinates values
    (proj1 (proj2 (proj2 WRITE))) LENGTH).
  f_equal; apply map_ext_in; intros access MEMBER.
  apply Forall_forall with (x := access) in READS; [|exact MEMBER].
  apply memory_scalar_access_cell with (layout := layout); [exact (proj1 (proj2 (proj2 READS)))|exact LENGTH].
Qed.
Lemma window_point_footprint_prefix bounds lower upper layout scalars operations coordinates values :
  Forall (window_compute_valid bounds lower upper layout scalars) operations -> length coordinates = length layout ->
  memory_point_footprint (memory_pad_instructions (length scalars) (map memory_nary_compute_instruction operations)) (coordinates++values) =
    memory_point_footprint (memory_pad_instructions (length scalars) (map memory_nary_compute_instruction operations)) coordinates.
Proof.
  intros CERT LENGTH; induction CERT as [|operation operations HEAD CERT IH];
    cbn [memory_point_footprint memory_pad_instructions map flat_map]; [reflexivity|].
  rewrite !memory_pad_instruction_footprint.
  rewrite (@window_operation_footprint_prefix bounds lower upper layout scalars operation coordinates values HEAD LENGTH).
  f_equal; exact IH.
Qed.
Print Assumptions window_operation_footprint_prefix.
Print Assumptions window_point_footprint_prefix.
