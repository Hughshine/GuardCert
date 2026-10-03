From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryAffineReindex GuardMemoryAffineMappedExtractor GuardMemoryParametricChecker GuardMemoryScalarLoops.
Import CoreAlarmed ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_scalar_static_bounds dimensions cap scalars :=
  repeat (MemoryNested.A.Interval 1 cap) dimensions++
  repeat (MemoryNested.A.Interval Int.min_signed Int.max_signed) scalars.
Definition memory_scalar_assumed_loop dimensions cap scalars loop :=
  L.Guard (memory_source_bounds_test_from O (memory_scalar_static_bounds dimensions cap scalars)) loop.
Lemma memory_scalar_assumed_execution dimensions cap scalars parameters before after loop :
  MemoryNested.A.env_within (memory_scalar_static_bounds dimensions cap scalars) parameters ->
  (L.loop_semantics (memory_scalar_assumed_loop dimensions cap scalars loop) parameters before after <->
    L.loop_semantics loop parameters before after).
Proof.
  intro WITHIN; pose proof (memory_source_bounds_test_true WITHIN) as BOUNDS.
  unfold memory_scalar_assumed_loop; split; intro RUN.
  - inversion RUN; subst.
    + assumption.
    + exfalso; assert (FALSE : L.eval_test parameters (memory_source_bounds_test_from O
        (memory_scalar_static_bounds dimensions cap scalars)) = false) by exact H4.
      rewrite BOUNDS in FALSE; discriminate.
  - apply L.LGuardTrue; assumption.
Qed.
Definition memory_scalar_candidate_certificate dimensions cap scalars instructions (context : list ident) candidate :=
  forall parameters initial final, length parameters = length context ->
    MemoryNested.A.env_within (memory_scalar_static_bounds dimensions cap scalars) parameters -> GuardMemoryInstr.NonAlias initial ->
    L.loop_semantics (memory_scalar_rectangle 0 dimensions scalars instructions) parameters initial final ->
    L.loop_semantics candidate parameters initial final.
Definition checked_memory_scalar_candidate dimensions cap scalars instructions context arrays candidate steps :=
  let vars := map (fun array => (array,tt)) (context++arrays) in
  checked_memory_affine_mapped_domain_loops
    (memory_scalar_assumed_loop dimensions cap scalars (memory_scalar_rectangle 0 dimensions scalars instructions),context,vars)
    (memory_scalar_assumed_loop dimensions cap scalars candidate,context,vars) steps.
Theorem checked_memory_scalar_candidate_correct dimensions cap scalars instructions context arrays candidate steps :
  mayReturn (checked_memory_scalar_candidate dimensions cap scalars instructions context arrays candidate steps) true ->
  memory_scalar_candidate_certificate dimensions cap scalars instructions context candidate.
Proof.
  intros CHECK parameters before after LENGTH WITHIN NONALIAS SOURCE.
  apply memory_scalar_assumed_execution with (dimensions := dimensions) (cap := cap) (scalars := scalars); [exact WITHIN|].
  pose proof (@validated_memory_affine_mapped_domain_loops_at
    (memory_scalar_assumed_loop dimensions cap scalars (memory_scalar_rectangle 0 dimensions scalars instructions))
    (memory_scalar_assumed_loop dimensions cap scalars candidate) context
    (map (fun array => (array,tt)) (context++arrays)) steps (rev parameters) before after
    ltac:(rewrite rev_length; exact LENGTH) NONALIAS CHECK) as VALID.
  rewrite rev_involutive in VALID; apply (proj1 VALID).
  apply memory_scalar_assumed_execution; assumption.
Qed.
Print Assumptions checked_memory_scalar_candidate_correct.
