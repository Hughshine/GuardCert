From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightRectangularStore ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryPolyhedral GuardMemoryLoops
  GuardMemoryTilingProgress GuardMemoryTiledRectangles
  GuardMemorySequenceLoops GuardMemorySequencePolyhedral GuardMemorySequenceExecution
  GuardMemoryEquivalentDomainsExtractor GuardMemoryAffineMappedExtractor GuardMemoryProposedClight GuardMemoryNamedOperations GuardMemoryNamedCandidate.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition checked_named_mapped_candidate base operations bound inner_bound candidate steps :=
  let instructions := map named_operation_instruction operations in
  let context := [bound;inner_bound] in
  let vars := map (fun array => (array,tt)) (context++flat_map named_operation_arrays operations) in
  checked_memory_affine_mapped_domain_loops
    (memory_array_assumed_loop base (memory_rectangle_sequence instructions),context,vars)
    (memory_array_assumed_loop base candidate,context,vars) steps.
Theorem checked_named_mapped_candidate_correct base operations bound inner_bound candidate steps :
  mayReturn (checked_named_mapped_candidate base operations bound inner_bound candidate steps) true ->
  memory_named_candidate_certificate base operations candidate.
Proof.
  intros CHECK N M initial final NB MB NONALIAS SOURCE.
  unfold checked_named_mapped_candidate in CHECK.
  apply memory_array_assumed_loop_execution with (base := base); [exact NB|exact MB|].
  apply (proj1 (@validated_memory_affine_mapped_domain_loops_at
    (memory_array_assumed_loop base (memory_rectangle_sequence (map named_operation_instruction operations)))
    (memory_array_assumed_loop base candidate) [bound;inner_bound]
    (map (fun array => (array,tt)) ([bound;inner_bound]++flat_map named_operation_arrays operations))
    steps [M;N] initial final eq_refl NONALIAS CHECK)).
  apply memory_array_assumed_loop_execution; assumption.
Qed.
Print Assumptions checked_named_mapped_candidate_correct.
