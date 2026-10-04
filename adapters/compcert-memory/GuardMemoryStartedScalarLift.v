From Stdlib Require Import List ZArith Lia.
From compcert.common Require Import Memory.
From Guard Require Import ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops
  GuardMemoryNaryCompute GuardMemoryNaryLoops GuardMemoryNarySequence GuardMemoryNaryLift
  GuardMemoryScalarLoops GuardMemoryScalarLift.
From GuardMemory Require Import GuardMemoryStartedScalarLoop.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_started_domain upper counts start coordinates :=
  exists x, start <= x < Z.of_nat upper /\ memory_nary_domain counts [x] coordinates.
Lemma memory_started_domain_subset upper counts start coordinates :
  0 <= start -> memory_started_domain upper counts start coordinates ->
  memory_nary_domain (upper::counts) [] coordinates.
Proof. intros NONNEG [x [RANGE DOMAIN]]; exists x; split; [lia|exact DOMAIN]. Qed.

Theorem memory_started_scalar_loop_lift locations instructions physical upper counts values start count before after :
  Z.of_nat upper = start + Z.of_nat count ->
  (forall coordinates first final, memory_started_domain upper counts start coordinates ->
    (physical coordinates first final <-> memory_scalar_sequence_point instructions coordinates values
      (RuntimeState locations first) (RuntimeState locations final))) ->
  (counted_iterations (fun x => memory_nary_iterations physical counts [x]) count start before after <->
    L.loop_semantics (memory_started_scalar_loop (S (length counts)) (length values) instructions)
      (map Z.of_nat (upper::counts)++values++[start])
      (RuntimeState locations before) (RuntimeState locations after)).
Proof.
  intros SPAN POINT.
  rewrite memory_started_scalar_loop_iterations by exact SPAN.
  apply counted_memory_lift with (floor := start) (upper := Z.of_nat upper).
  - intros x first final RANGE; apply memory_scalar_iterations_lift.
    intros coordinates initial target DOMAIN; apply POINT; exists x; split; assumption.
  - intros; eapply memory_scalar_iterations_locations; eassumption.
  - lia.
  - exact SPAN.
Qed.
Print Assumptions memory_started_scalar_loop_lift.
