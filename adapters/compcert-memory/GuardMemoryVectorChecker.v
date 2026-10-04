From Stdlib Require Import List ZArith.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops
  GuardMemoryArrayBackend GuardMemoryAffineReindex GuardMemoryAffineMappedExtractor
  GuardMemoryParametricChecker GuardMemoryScalarLoops.
Import CoreAlarmed ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_vector_static_bounds caps scalars :=
  map (fun cap => MemoryNested.A.Interval 1 cap) caps ++
  repeat (MemoryNested.A.Interval Int.min_signed Int.max_signed) scalars.
Definition memory_bounded_assumed_loop bounds loop :=
  L.Guard (memory_source_bounds_test_from O bounds) loop.
Lemma memory_bounded_assumed_execution bounds parameters before after loop :
  MemoryNested.A.env_within bounds parameters ->
  (L.loop_semantics (memory_bounded_assumed_loop bounds loop) parameters before after <->
    L.loop_semantics loop parameters before after).
Proof.
  intro WITHIN; pose proof (memory_source_bounds_test_true WITHIN) as BOUNDS.
  unfold memory_bounded_assumed_loop; split; intro RUN.
  - inversion RUN; subst.
    + assumption.
    + exfalso; assert (FALSE : L.eval_test parameters (memory_source_bounds_test_from O bounds) = false) by exact H4.
      rewrite BOUNDS in FALSE; discriminate.
  - apply L.LGuardTrue; assumption.
Qed.
Definition memory_bounded_candidate_certificate bounds dimensions scalars instructions (context : list ident) candidate :=
  forall parameters initial final, length parameters = length context ->
    MemoryNested.A.env_within bounds parameters -> GuardMemoryInstr.NonAlias initial ->
    L.loop_semantics (memory_scalar_rectangle 0 dimensions scalars instructions) parameters initial final ->
    L.loop_semantics candidate parameters initial final.
Definition checked_memory_bounded_candidate bounds dimensions scalars instructions context arrays candidate steps :=
  let vars := map (fun array => (array,tt)) (context++arrays) in
  checked_memory_affine_mapped_domain_loops
    (memory_bounded_assumed_loop bounds (memory_scalar_rectangle 0 dimensions scalars instructions),context,vars)
    (memory_bounded_assumed_loop bounds candidate,context,vars) steps.
Theorem checked_memory_bounded_candidate_correct bounds dimensions scalars instructions context arrays candidate steps :
  mayReturn (checked_memory_bounded_candidate bounds dimensions scalars instructions context arrays candidate steps) true ->
  memory_bounded_candidate_certificate bounds dimensions scalars instructions context candidate.
Proof.
  intros CHECK parameters before after LENGTH WITHIN NONALIAS SOURCE.
  apply memory_bounded_assumed_execution with (bounds := bounds); [exact WITHIN|].
  pose proof (@validated_memory_affine_mapped_domain_loops_at
    (memory_bounded_assumed_loop bounds (memory_scalar_rectangle 0 dimensions scalars instructions))
    (memory_bounded_assumed_loop bounds candidate) context
    (map (fun array => (array,tt)) (context++arrays)) steps (rev parameters) before after
    ltac:(rewrite rev_length; exact LENGTH) NONALIAS CHECK) as VALID.
  rewrite rev_involutive in VALID; apply (proj1 VALID).
  apply memory_bounded_assumed_execution; assumption.
Qed.
Print Assumptions checked_memory_bounded_candidate_correct.
