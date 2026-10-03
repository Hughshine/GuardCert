From Stdlib Require Import List Bool ZArith Lia.
From compcert.common Require Import AST.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightRectangularStore.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryAffineMappedExtractor GuardMemoryAffineReindex GuardMemoryAffineSourceExpressions
  GuardMemoryAffineSourceEndpoints GuardMemoryParametricLoops GuardMemoryParametricChecker.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition memory_parametric_instruction_candidate_certificate base instructions row context bounds expression encoded candidate :=
  forall parameters initial final,
    length parameters = length context -> MemoryNested.A.env_within bounds parameters ->
    memory_source_width_model (rectangle_stride base) row context expression parameters = true ->
    GuardMemoryInstr.NonAlias initial ->
    L.loop_semantics (memory_parametric_sequence encoded instructions) parameters initial final ->
    L.loop_semantics candidate parameters initial final.
Definition checked_parametric_instruction_candidate base instructions arrays row context bounds expression encoded candidate steps :=
  let vars := map (fun array => (array,tt)) (context++arrays) in
  checked_memory_affine_mapped_domain_loops
    (memory_parametric_assumed_loop base row context bounds expression
      (memory_parametric_sequence encoded instructions),context,vars)
    (memory_parametric_assumed_loop base row context bounds expression candidate,context,vars) steps.
Theorem checked_parametric_instruction_candidate_correct base instructions arrays row context bounds expression encoded candidate steps :
  mayReturn (checked_parametric_instruction_candidate base instructions arrays row context bounds expression encoded candidate steps) true ->
  memory_parametric_instruction_candidate_certificate base instructions row context bounds expression encoded candidate.
Proof.
  intros CHECK parameters before after LENGTH WITHIN WIDTH NONALIAS SOURCE.
  unfold checked_parametric_instruction_candidate in CHECK.
  apply memory_parametric_assumed_execution with (base := base) (row := row) (context := context)
    (bounds := bounds) (expression := expression); [exact WITHIN|exact WIDTH|].
  pose proof (@validated_memory_affine_mapped_domain_loops_at
    (memory_parametric_assumed_loop base row context bounds expression
      (memory_parametric_sequence encoded instructions))
    (memory_parametric_assumed_loop base row context bounds expression candidate) context
    (map (fun array => (array,tt)) (context++arrays))
    steps (rev parameters) before after ltac:(rewrite rev_length; exact LENGTH) NONALIAS CHECK) as VALID.
  rewrite rev_involutive in VALID; apply (proj1 VALID).
  apply memory_parametric_assumed_execution; assumption.
Qed.
Print Assumptions checked_parametric_instruction_candidate_correct.
