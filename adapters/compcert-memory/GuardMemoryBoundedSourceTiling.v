From Stdlib Require Import List ZArith.
From compcert.common Require Import AST.
From polcert.lib Require Import ImpureAlarmConfig.
From polcert.src Require Import PointWitness TilingWitness.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryExtractedTiling GuardMemoryVectorChecker.
From GuardMemory Require Import GuardMemoryBoundedSourceChecker.
Import CoreAlarmed ListNotations.
Set Implicit Arguments.
Definition checked_memory_bounded_source_tiling bounds source_loop candidate context arrays witnesses :=
  let vars := map (fun array => (array,tt)) (context++arrays) in
  checked_memory_extracted_tiling_loops
    (memory_bounded_assumed_loop bounds source_loop,context,vars)
    (memory_bounded_assumed_loop bounds candidate,context,vars) witnesses.
Theorem checked_memory_bounded_source_tiling_correct bounds source_loop candidate context arrays witnesses :
  mayReturn (checked_memory_bounded_source_tiling bounds source_loop candidate context arrays witnesses) true ->
  memory_bounded_source_certificate bounds source_loop context candidate.
Proof.
  intros CHECK parameters before after LENGTH WITHIN NONALIAS SOURCE.
  apply memory_bounded_assumed_execution with (bounds := bounds); [exact WITHIN|].
  pose proof (@validated_memory_extracted_tiling_loops_at
    (memory_bounded_assumed_loop bounds source_loop) (memory_bounded_assumed_loop bounds candidate) context
    (map (fun array => (array,tt)) (context++arrays)) witnesses (rev parameters) before after
    ltac:(rewrite length_rev; exact LENGTH) NONALIAS CHECK) as VALID.
  rewrite rev_involutive in VALID; apply VALID; apply memory_bounded_assumed_execution; assumption.
Qed.
Print Assumptions checked_memory_bounded_source_tiling_correct.
