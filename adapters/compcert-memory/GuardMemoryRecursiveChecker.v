From Stdlib Require Import List Bool ZArith Lia.
From compcert.common Require Import AST.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryAffineReindex GuardMemoryAffineMappedExtractor GuardMemoryParametricChecker GuardMemoryNaryLoops.
Import CoreAlarmed ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_recursive_static_bounds dimensions cap := repeat (MemoryNested.A.Interval 1 cap) dimensions.
Definition memory_recursive_assumed_loop dimensions cap loop :=
  L.Guard (memory_source_bounds_test_from O (memory_recursive_static_bounds dimensions cap)) loop.
Lemma memory_recursive_assumed_execution dimensions cap parameters before after loop :
  MemoryNested.A.env_within (memory_recursive_static_bounds dimensions cap) parameters ->
  (L.loop_semantics (memory_recursive_assumed_loop dimensions cap loop) parameters before after <-> L.loop_semantics loop parameters before after).
Proof.
  intro WITHIN; pose proof (memory_source_bounds_test_true WITHIN) as BOUNDS.
  unfold memory_recursive_assumed_loop; split; intro RUN.
  - inversion RUN; subst.
    + assumption.
    + exfalso; assert (FALSE : L.eval_test parameters (memory_source_bounds_test_from O
        (memory_recursive_static_bounds dimensions cap)) = false) by exact H4.
      rewrite BOUNDS in FALSE; discriminate.
  - apply L.LGuardTrue; assumption.
Qed.
Definition memory_recursive_candidate_certificate dimensions cap instructions (context : list ident) candidate :=
  forall parameters initial final, length parameters = length context ->
    MemoryNested.A.env_within (memory_recursive_static_bounds dimensions cap) parameters -> GuardMemoryInstr.NonAlias initial ->
    L.loop_semantics (memory_nary_rectangle 0 dimensions instructions) parameters initial final ->
    L.loop_semantics candidate parameters initial final.
Definition checked_memory_recursive_candidate dimensions cap instructions context arrays candidate steps :=
  let vars := map (fun array => (array,tt)) (context++arrays) in
  checked_memory_affine_mapped_domain_loops
    (memory_recursive_assumed_loop dimensions cap (memory_nary_rectangle 0 dimensions instructions),context,vars)
    (memory_recursive_assumed_loop dimensions cap candidate,context,vars) steps.
Theorem checked_memory_recursive_candidate_correct dimensions cap instructions context arrays candidate steps :
  mayReturn (checked_memory_recursive_candidate dimensions cap instructions context arrays candidate steps) true ->
  memory_recursive_candidate_certificate dimensions cap instructions context candidate.
Proof.
  intros CHECK parameters before after LENGTH WITHIN NONALIAS SOURCE.
  apply memory_recursive_assumed_execution with (dimensions := dimensions) (cap := cap); [exact WITHIN|].
  pose proof (@validated_memory_affine_mapped_domain_loops_at
    (memory_recursive_assumed_loop dimensions cap (memory_nary_rectangle 0 dimensions instructions))
    (memory_recursive_assumed_loop dimensions cap candidate) context
    (map (fun array => (array,tt)) (context++arrays)) steps (rev parameters) before after
    ltac:(rewrite rev_length; exact LENGTH) NONALIAS CHECK) as VALID.
  rewrite rev_involutive in VALID; apply (proj1 VALID).
  apply memory_recursive_assumed_execution; assumption.
Qed.
Print Assumptions checked_memory_recursive_candidate_correct.
