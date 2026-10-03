From Stdlib Require Import List Bool ZArith Lia.
From compcert.common Require Import AST.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryAffineReindex GuardMemoryAffineMappedExtractor GuardMemoryParametricChecker GuardMemoryNaryLoops.
Import CoreAlarmed ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_triple_bounds cap := [MemoryNested.A.Interval 1 cap;MemoryNested.A.Interval 1 cap;MemoryNested.A.Interval 1 cap].
Definition memory_triple_assumed_loop cap loop := L.Guard (memory_source_bounds_test_from O (memory_triple_bounds cap)) loop.
Lemma memory_triple_assumed_execution cap parameters before after loop :
  MemoryNested.A.env_within (memory_triple_bounds cap) parameters ->
  (L.loop_semantics (memory_triple_assumed_loop cap loop) parameters before after <-> L.loop_semantics loop parameters before after).
Proof.
  intro WITHIN; pose proof (memory_source_bounds_test_true WITHIN) as BOUNDS.
  unfold memory_triple_assumed_loop.
  split; intro RUN.
  - inversion RUN; subst.
    + assumption.
    + exfalso; assert (FALSE : L.eval_test parameters (memory_source_bounds_test_from O (memory_triple_bounds cap)) = false) by exact H4.
      rewrite BOUNDS in FALSE; discriminate.
  - apply L.LGuardTrue; assumption.
Qed.
Definition memory_triple_candidate_certificate cap instructions (context : list ident) candidate :=
  forall parameters initial final, length parameters = length context ->
    MemoryNested.A.env_within (memory_triple_bounds cap) parameters -> GuardMemoryInstr.NonAlias initial ->
    L.loop_semantics (memory_nary_rectangle 0 3 instructions) parameters initial final ->
    L.loop_semantics candidate parameters initial final.
Definition checked_memory_triple_candidate cap instructions context arrays candidate steps :=
  let vars := map (fun array => (array,tt)) (context++arrays) in
  checked_memory_affine_mapped_domain_loops
    (memory_triple_assumed_loop cap (memory_nary_rectangle 0 3 instructions),context,vars)
    (memory_triple_assumed_loop cap candidate,context,vars) steps.
Theorem checked_memory_triple_candidate_correct cap instructions context arrays candidate steps :
  mayReturn (checked_memory_triple_candidate cap instructions context arrays candidate steps) true ->
  memory_triple_candidate_certificate cap instructions context candidate.
Proof.
  intros CHECK parameters before after LENGTH WITHIN NONALIAS SOURCE.
  apply memory_triple_assumed_execution with (cap := cap); [exact WITHIN|].
  pose proof (@validated_memory_affine_mapped_domain_loops_at
    (memory_triple_assumed_loop cap (memory_nary_rectangle 0 3 instructions))
    (memory_triple_assumed_loop cap candidate) context
    (map (fun array => (array,tt)) (context++arrays)) steps (rev parameters) before after
    ltac:(rewrite rev_length; exact LENGTH) NONALIAS CHECK) as VALID.
  rewrite rev_involutive in VALID; apply (proj1 VALID).
  apply memory_triple_assumed_execution; assumption.
Qed.
Print Assumptions checked_memory_triple_candidate_correct.
