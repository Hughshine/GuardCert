From Stdlib Require Import List ZArith Lia.
From polcert.lib Require Import Misc ImpureAlarmConfig.
From polcert.src Require Import PointWitness TilingWitness.
From Vpl Require Import Impure.
From Guard Require Import ClightRectangularStore.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend GuardMemoryExtractedTiling
  GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceEndpoints GuardMemoryParametricLoops
  GuardMemoryParametricChecker GuardMemoryParametricTiling GuardMemoryParametricInstructionChecker.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition checked_parametric_instruction_tiling base instructions arrays row context bounds expression encoded bi bj :=
  let vars := map (fun array => (array,tt)) (context++arrays) in
  checked_memory_extracted_tiling_loops
    (memory_parametric_assumed_loop base row context bounds expression (memory_parametric_sequence encoded instructions),context,vars)
    (memory_parametric_assumed_loop base row context bounds expression
      (memory_parametric_tiled_loop instructions encoded (rectangle_stride base) bi bj false),context,vars)
    (repeat (memory_parametric_tiling_witness (length context) bi bj) (length instructions)).
Theorem checked_parametric_instruction_tiling_correct base instructions arrays row context bounds expression encoded bi bj :
  0 < rectangle_stride base -> 0 < bi -> 0 < bj ->
  (forall parameters, MemoryNested.A.env_within bounds parameters -> 0 < nth O parameters 0) ->
  mayReturn (checked_parametric_instruction_tiling base instructions arrays row context bounds expression encoded bi bj) true ->
  memory_parametric_instruction_candidate_certificate base instructions row context bounds expression encoded
    (memory_parametric_tiled_loop instructions encoded (rectangle_stride base) bi bj true).
Proof.
  intros STRIDE BI BJ POSITIVE CHECK parameters before after LENGTH WITHIN WIDTH NONALIAS SOURCE.
  destruct parameters as [|N parameters].
  - specialize (POSITIVE [] WITHIN); cbn in POSITIVE; lia.
  - apply (proj1 (@memory_parametric_tile_trimming instructions encoded
      (rectangle_stride base) bi bj N parameters before after (POSITIVE _ WITHIN) STRIDE BI BJ)).
    unfold checked_parametric_instruction_tiling in CHECK.
    apply memory_parametric_assumed_execution with (base := base) (row := row) (context := context)
      (bounds := bounds) (expression := expression); [exact WITHIN|exact WIDTH|].
    pose proof (@validated_memory_extracted_tiling_loops_at
      (memory_parametric_assumed_loop base row context bounds expression
        (memory_parametric_sequence encoded instructions))
      (memory_parametric_assumed_loop base row context bounds expression
        (memory_parametric_tiled_loop instructions encoded (rectangle_stride base) bi bj false))
      context (map (fun array => (array,tt)) (context++arrays))
      (repeat (memory_parametric_tiling_witness (length context) bi bj) (length instructions)) (rev (N::parameters)) before after
      ltac:(rewrite length_rev; exact LENGTH) NONALIAS CHECK) as VALID.
    rewrite rev_involutive in VALID; apply VALID.
    apply memory_parametric_assumed_execution; assumption.
Qed.
Print Assumptions checked_parametric_instruction_tiling_correct.
