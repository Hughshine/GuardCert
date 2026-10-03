From Stdlib Require Import List ZArith Lia.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightRectangularStore ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryLoops GuardMemoryExtractedTiling
  GuardMemoryTiledRectangles GuardMemoryNamedOperations GuardMemoryRaggedLoops GuardMemoryRaggedTiling
  GuardMemoryNamedRaggedCandidate GuardMemoryNamedRaggedChecker.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition checked_named_ragged_tiling base operations bound parameter bi bj :=
  let instructions := map named_operation_instruction operations in
  let context := [bound;parameter] in
  let vars := map (fun array => (array,tt)) (context++flat_map named_operation_arrays operations) in
  checked_memory_extracted_tiling_loops
    (memory_ragged_assumed_loop base (memory_ragged_sequence instructions),context,vars)
    (memory_ragged_assumed_loop base (memory_ragged_tiled_loop instructions bi bj false),context,vars)
    (repeat (rectangle_tiling_witness bi bj) (length instructions)).
Theorem checked_named_ragged_tiling_correct base operations bound parameter bi bj :
  0 < bi -> 0 < bj ->
  mayReturn (checked_named_ragged_tiling base operations bound parameter bi bj) true ->
  memory_ragged_candidate_certificate base operations
    (memory_ragged_tiled_loop (map named_operation_instruction operations) bi bj true).
Proof.
  intros BI BJ CHECK N M before after NB MB WIDTH NONALIAS SOURCE.
  apply (proj1 (@memory_ragged_tile_trimming (map named_operation_instruction operations) bi bj N M before after
    ltac:(lia) ltac:(lia) BI BJ)).
  unfold checked_named_ragged_tiling in CHECK.
  apply memory_ragged_assumed_execution with (base := base); [exact NB|exact MB|exact WIDTH|].
  eapply validated_memory_extracted_tiling_loops_at with
    (source := memory_ragged_assumed_loop base (memory_ragged_sequence (map named_operation_instruction operations)))
    (context := [bound;parameter])
    (vars := map (fun array => (array,tt)) ([bound;parameter]++flat_map named_operation_arrays operations))
    (parameters := [M;N]); [reflexivity|exact NONALIAS|exact CHECK|].
  apply memory_ragged_assumed_execution; assumption.
Qed.
Print Assumptions checked_named_ragged_tiling_correct.
