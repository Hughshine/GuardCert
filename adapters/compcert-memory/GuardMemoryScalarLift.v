From Stdlib Require Import List ZArith Lia.
From compcert.common Require Import Memory.
From Guard Require Import ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops
  GuardMemoryNaryCompute GuardMemoryNaryLoops GuardMemoryNarySequence GuardMemoryNaryLift GuardMemoryScalarLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_scalar_sequence_locations instructions coordinates values before after :
  memory_scalar_sequence_point instructions coordinates values before after -> runtime_locations after = runtime_locations before.
Proof. apply memory_nary_sequence_locations. Qed.
Lemma memory_scalar_iterations_locations instructions counts values : forall prefix before after,
  memory_nary_iterations (fun coordinates => memory_scalar_sequence_point instructions coordinates values)
    counts prefix before after -> runtime_locations after = runtime_locations before.
Proof.
  induction counts as [|count counts IH]; intros prefix before after RUN; cbn in RUN.
  - eapply memory_scalar_sequence_locations; exact RUN.
  - eapply counted_locations; [|exact RUN]; intros value first final STEP.
    exact (IH (prefix++[value]) first final STEP).
Qed.
Theorem memory_scalar_iterations_lift locations instructions (physical : list Z -> mem -> mem -> Prop) counts values :
  forall prefix before after,
  (forall coordinates first final, memory_nary_domain counts prefix coordinates ->
    (physical coordinates first final <-> memory_scalar_sequence_point instructions coordinates values
      (RuntimeState locations first) (RuntimeState locations final))) ->
  (memory_nary_iterations physical counts prefix before after <->
    memory_nary_iterations (fun coordinates => memory_scalar_sequence_point instructions coordinates values) counts prefix
      (RuntimeState locations before) (RuntimeState locations after)).
Proof.
  induction counts as [|count counts IH]; intros prefix before after POINT; cbn [memory_nary_iterations].
  - apply POINT; reflexivity.
  - apply counted_memory_lift with (floor := 0) (upper := Z.of_nat count).
    + intros value first final RANGE; apply IH; intros coordinates initial target DOMAIN.
      apply POINT; exists value; split; assumption.
    + intros; eapply memory_scalar_iterations_locations; eassumption.
    + lia.
    + lia.
Qed.
Theorem memory_scalar_rectangle_lift locations instructions physical counts values before after :
  (forall coordinates first final, memory_nary_domain counts [] coordinates ->
    (physical coordinates first final <-> memory_scalar_sequence_point instructions coordinates values
      (RuntimeState locations first) (RuntimeState locations final))) ->
  (memory_nary_iterations physical counts [] before after <->
    L.loop_semantics (memory_scalar_rectangle 0 (length counts) (length values) instructions)
      (map Z.of_nat counts++values) (RuntimeState locations before) (RuntimeState locations after)).
Proof.
  intro POINT; rewrite (@memory_scalar_rectangle_iterations counts instructions values [] [] _ _ eq_refl).
  apply memory_scalar_iterations_lift; exact POINT.
Qed.
Print Assumptions memory_scalar_rectangle_lift.
