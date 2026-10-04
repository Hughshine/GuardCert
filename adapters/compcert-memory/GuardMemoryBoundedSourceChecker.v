From Stdlib Require Import List ZArith.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops
  GuardMemoryArrayBackend GuardMemoryAffineReindex GuardMemoryAffineMappedExtractor
  GuardMemoryParametricChecker GuardMemoryScalarLoops GuardMemoryVectorChecker.
Import CoreAlarmed ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_bounded_source_certificate bounds source_loop (context : list ident) candidate :=
  forall parameters initial final, length parameters = length context ->
    MemoryNested.A.env_within bounds parameters -> GuardMemoryInstr.NonAlias initial ->
    L.loop_semantics (source_loop) parameters initial final ->
    L.loop_semantics candidate parameters initial final.
Definition checked_memory_bounded_source_candidate bounds source_loop context arrays candidate steps :=
  let vars := map (fun array => (array,tt)) (context++arrays) in
  checked_memory_affine_mapped_domain_loops
    (memory_bounded_assumed_loop bounds (source_loop),context,vars)
    (memory_bounded_assumed_loop bounds candidate,context,vars) steps.
Theorem checked_memory_bounded_source_candidate_correct bounds source_loop context arrays candidate steps :
  mayReturn (checked_memory_bounded_source_candidate bounds source_loop context arrays candidate steps) true ->
  memory_bounded_source_certificate bounds source_loop context candidate.
Proof.
  intros CHECK parameters before after LENGTH WITHIN NONALIAS SOURCE.
  apply memory_bounded_assumed_execution with (bounds := bounds); [exact WITHIN|].
  pose proof (@validated_memory_affine_mapped_domain_loops_at
    (memory_bounded_assumed_loop bounds (source_loop))
    (memory_bounded_assumed_loop bounds candidate) context
    (map (fun array => (array,tt)) (context++arrays)) steps (rev parameters) before after
    ltac:(rewrite rev_length; exact LENGTH) NONALIAS CHECK) as VALID.
  rewrite rev_involutive in VALID; apply (proj1 VALID).
  apply memory_bounded_assumed_execution; assumption.
Qed.
Print Assumptions checked_memory_bounded_source_candidate_correct.
