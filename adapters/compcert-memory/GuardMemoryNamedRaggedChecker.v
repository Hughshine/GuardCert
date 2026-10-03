From Stdlib Require Import List ZArith Lia.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightRectangularStore ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryLoops GuardMemoryAffineReindex GuardMemoryAffineMappedExtractor
  GuardMemoryProposedClight GuardMemoryNamedOperations GuardMemoryRaggedLoops GuardMemoryRaggedGuard
  GuardMemoryNamedRaggedCandidate.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition memory_ragged_assumed_loop base loop :=
  memory_array_assumed_loop base (L.Guard (memory_ragged_width_test base) loop).
Lemma memory_ragged_assumed_execution base loop N M before after :
  0 < N <= rectangle_outer_limit base -> 0 < M <= rectangle_stride base -> N+M-1 <= rectangle_stride base ->
  (L.loop_semantics (memory_ragged_assumed_loop base loop) [N;M] before after <->
   L.loop_semantics loop [N;M] before after).
Proof.
  intros NB MB WIDTH; unfold memory_ragged_assumed_loop.
  rewrite memory_array_assumed_loop_execution by assumption.
  assert (TRUE : L.eval_test [N;M] (memory_ragged_width_test base) = true).
  { unfold memory_ragged_width_test; cbn [L.eval_test L.eval_expr nth]; apply Z.leb_le; lia. }
  split; intro RUN.
  - inversion RUN; subst; [assumption|congruence].
  - apply L.LGuardTrue; assumption.
Qed.
Definition checked_named_ragged_candidate base operations bound parameter candidate steps :=
  let context := [bound;parameter] in
  let vars := map (fun array => (array,tt)) (context++flat_map named_operation_arrays operations) in
  checked_memory_affine_mapped_domain_loops
    (memory_ragged_assumed_loop base (memory_ragged_sequence (map named_operation_instruction operations)),context,vars)
    (memory_ragged_assumed_loop base candidate,context,vars) steps.
Theorem checked_named_ragged_candidate_correct base operations bound parameter candidate steps :
  mayReturn (checked_named_ragged_candidate base operations bound parameter candidate steps) true ->
  memory_ragged_candidate_certificate base operations candidate.
Proof.
  intros CHECK N M before after NB MB WIDTH NONALIAS SOURCE.
  unfold checked_named_ragged_candidate in CHECK.
  apply memory_ragged_assumed_execution with (base := base); [exact NB|exact MB|exact WIDTH|].
  apply (proj1 (@validated_memory_affine_mapped_domain_loops_at
    (memory_ragged_assumed_loop base (memory_ragged_sequence (map named_operation_instruction operations)))
    (memory_ragged_assumed_loop base candidate) [bound;parameter]
    (map (fun array => (array,tt)) ([bound;parameter]++flat_map named_operation_arrays operations))
    steps [M;N] before after eq_refl NONALIAS CHECK)).
  apply memory_ragged_assumed_execution; assumption.
Qed.
Print Assumptions checked_named_ragged_candidate_correct.
