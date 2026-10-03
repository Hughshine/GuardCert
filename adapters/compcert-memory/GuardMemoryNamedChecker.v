From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightRectangularStore ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryPolyhedral GuardMemoryLoops
  GuardMemoryTilingProgress GuardMemoryTiledRectangles
  GuardMemorySequenceLoops GuardMemorySequencePolyhedral GuardMemorySequenceExecution
  GuardMemoryEquivalentDomainsExtractor GuardMemoryProposedClight GuardMemoryNamedOperations GuardMemoryNamedCandidate.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition checked_named_affine_candidate base operations bound inner_bound candidate swaps :=
  let instructions := map named_operation_instruction operations in
  let context := [bound;inner_bound] in
  let vars := map (fun array => (array,tt)) (context++map named_operation_array operations) in
  checked_memory_equivalent_domain_loops
    (memory_array_assumed_loop base (memory_rectangle_sequence instructions),context,vars)
    (memory_array_assumed_loop base candidate,context,vars) swaps.
Theorem checked_named_affine_candidate_correct base operations bound inner_bound candidate swaps :
  mayReturn (checked_named_affine_candidate base operations bound inner_bound candidate swaps) true ->
  memory_named_candidate_certificate base operations candidate.
Proof.
  intros CHECK N M initial final NB MB NONALIAS SOURCE.
  unfold checked_named_affine_candidate in CHECK.
  apply memory_array_assumed_loop_execution with (base := base); [exact NB|exact MB|].
  apply (proj1 (@validated_memory_equivalent_domain_loops_at
    (memory_array_assumed_loop base (memory_rectangle_sequence (map named_operation_instruction operations)))
    (memory_array_assumed_loop base candidate) [bound;inner_bound]
    (map (fun array => (array,tt)) ([bound;inner_bound]++map named_operation_array operations))
    swaps [M;N] initial final eq_refl NONALIAS CHECK)).
  apply memory_array_assumed_loop_execution; assumption.
Qed.
Definition checked_named_tiled_candidate base operations rows columns :=
  let instructions := map named_operation_instruction operations in
  validate_memory_tiling_equivalence
    (memory_sequence_source_program instructions (rectangle_stride base))
    (memory_sequence_tiled_program instructions (rectangle_stride base) rows columns)
    (repeat (rectangle_tiling_witness rows columns) (length instructions)).
Theorem checked_named_tiled_candidate_correct base operations rows columns :
  0 < rows -> 0 < columns ->
  mayReturn (checked_named_tiled_candidate base operations rows columns) true ->
  memory_named_candidate_certificate base operations
    (memory_tiled_sequence (map named_operation_instruction operations) rows columns).
Proof.
  intros ROWS COLUMNS CHECK N M initial final NB MB NONALIAS SOURCE.
  eapply validated_memory_sequence_tiling with (stride := rectangle_stride base);
    [exact ROWS|exact COLUMNS|lia|exact NONALIAS|exact CHECK|exact SOURCE].
Qed.
Print Assumptions checked_named_affine_candidate_correct.
Print Assumptions checked_named_tiled_candidate_correct.
