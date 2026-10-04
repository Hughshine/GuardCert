From Stdlib Require Import List ZArith Lia.
From polcert.lib Require Import Misc ImpureAlarmConfig.
From polcert.src Require Import PointWitness TilingWitness.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend GuardMemoryLoopTrace
  GuardMemoryExtractedTiling GuardMemoryTileRangeTrimming GuardMemoryNaryLoops GuardMemoryRecursiveChecker GuardMemoryScalarChecker GuardMemoryScalarLoops GuardMemoryScalarCandidates GuardMemoryRecursiveTiling.
From GuardMemory Require Import GuardMemoryScalarTiling.
From GuardMemory Require Import GuardMemoryVectorChecker.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition checked_memory_bounded_tiling bounds dimensions scalars instructions context arrays bi bj :=
  let vars := map (fun array => (array,tt)) (context++arrays) in
  checked_memory_extracted_tiling_loops
    (memory_bounded_assumed_loop bounds (memory_scalar_rectangle 0 dimensions scalars instructions),context,vars)
    (memory_bounded_assumed_loop bounds (memory_scalar_tiled_loop dimensions scalars instructions bi bj false),context,vars)
    (repeat (memory_scalar_tiling_witness dimensions (length context) bi bj) (length instructions)).
Theorem checked_memory_bounded_tiling_correct bounds dimensions scalars instructions context arrays bi bj first_cap second_cap :
  nth_error bounds O = Some (MemoryNested.A.Interval 1 first_cap) ->
  nth_error bounds 1%nat = Some (MemoryNested.A.Interval 1 second_cap) ->
  length context = (dimensions+scalars)%nat -> (2 <= dimensions)%nat -> 0 < bi -> 0 < bj ->
  mayReturn (checked_memory_bounded_tiling bounds dimensions scalars instructions context arrays bi bj) true ->
  memory_bounded_candidate_certificate bounds dimensions scalars instructions context (memory_scalar_tiled_loop dimensions scalars instructions bi bj true).
Proof.
  intros FIRST SECOND CONTEXT DIMENSIONS BI BJ CHECK parameters before after LENGTH WITHIN NONALIAS SOURCE.
  destruct dimensions as [|[|remaining]]; try lia.
  assert (ARITY : length parameters = (S (S remaining)+scalars)%nat) by (rewrite LENGTH; exact CONTEXT).
  destruct parameters as [|N [|M parameters]]; cbn in ARITY; try discriminate.
  assert (NP : 0 < N) by (pose proof (WITHIN O _ FIRST) as RANGE; unfold MemoryNested.A.contains in RANGE; cbn in RANGE; lia).
  assert (MP : 0 < M) by (pose proof (WITHIN 1%nat _ SECOND) as RANGE; unfold MemoryNested.A.contains in RANGE; cbn in RANGE; lia).
  apply (proj1 (@memory_scalar_tile_trimming (S (S remaining)) scalars instructions bi bj N M parameters before after NP MP BI BJ)).
  unfold checked_memory_bounded_tiling in CHECK.
  apply memory_bounded_assumed_execution with (bounds := bounds); [exact WITHIN|].
  pose proof (@validated_memory_extracted_tiling_loops_at
    (memory_bounded_assumed_loop bounds (memory_scalar_rectangle 0 (S (S remaining)) scalars instructions))
    (memory_bounded_assumed_loop bounds (memory_scalar_tiled_loop (S (S remaining)) scalars instructions bi bj false)) context
    (map (fun array => (array,tt)) (context++arrays))
    (repeat (memory_scalar_tiling_witness (S (S remaining)) (length context) bi bj) (length instructions))
    (rev (N::M::parameters)) before after ltac:(rewrite length_rev; exact LENGTH) NONALIAS CHECK) as VALID.
  rewrite rev_involutive in VALID; apply VALID; apply memory_bounded_assumed_execution; assumption.
Qed.
Print Assumptions checked_memory_bounded_tiling_correct.
