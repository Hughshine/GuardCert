From Stdlib Require Import List ZArith Lia.
From compcert.common Require Import Memory.
From Guard Require Import ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops
  GuardMemoryNaryCompute GuardMemoryNaryLoops GuardMemoryNarySequence.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint memory_nary_domain counts prefix values : Prop := match counts with
  | [] => values = prefix
  | count::rest => exists value, 0 <= value < Z.of_nat count /\ memory_nary_domain rest (prefix++[value]) values
  end.
Lemma memory_nary_sequence_locations instructions values before after :
  memory_nary_sequence_point instructions values before after -> runtime_locations after = runtime_locations before.
Proof.
  intro RUN; induction RUN; [reflexivity|rewrite IHRUN; eapply memory_nary_point_locations; eauto].
Qed.
Lemma memory_nary_iterations_locations instructions counts : forall prefix before after,
  memory_nary_iterations (memory_nary_sequence_point instructions) counts prefix before after ->
  runtime_locations after = runtime_locations before.
Proof.
  induction counts as [|count counts IH]; intros prefix before after RUN; cbn in RUN.
  - eapply memory_nary_sequence_locations; exact RUN.
  - eapply counted_locations; [|exact RUN]; intros value first final STEP.
    exact (IH (prefix++[value]) first final STEP).
Qed.
Theorem memory_nary_iterations_lift locations instructions (physical : list Z -> mem -> mem -> Prop) counts :
  forall prefix before after,
  (forall values first final, memory_nary_domain counts prefix values ->
    (physical values first final <-> memory_nary_sequence_point instructions values
      (RuntimeState locations first) (RuntimeState locations final))) ->
  (memory_nary_iterations physical counts prefix before after <->
    memory_nary_iterations (memory_nary_sequence_point instructions) counts prefix
      (RuntimeState locations before) (RuntimeState locations after)).
Proof.
  induction counts as [|count counts IH]; intros prefix before after POINT; cbn [memory_nary_iterations].
  - apply POINT; reflexivity.
  - apply counted_memory_lift with (floor := 0) (upper := Z.of_nat count).
    + intros value first final RANGE; apply IH; intros values initial target DOMAIN.
      apply POINT; exists value; split; assumption.
    + intros; eapply memory_nary_iterations_locations; eassumption.
    + lia.
    + lia.
Qed.
Theorem memory_nary_rectangle_lift locations instructions physical counts before after :
  (forall values first final, memory_nary_domain counts [] values ->
    (physical values first final <-> memory_nary_sequence_point instructions values
      (RuntimeState locations first) (RuntimeState locations final))) ->
  (memory_nary_iterations physical counts [] before after <->
    L.loop_semantics (memory_nary_rectangle 0 (length counts) instructions) (map Z.of_nat counts)
      (RuntimeState locations before) (RuntimeState locations after)).
Proof.
  intro POINT; rewrite (@memory_nary_rectangle_iterations counts instructions [] [] _ _ eq_refl).
  apply memory_nary_iterations_lift; exact POINT.
Qed.
Print Assumptions memory_nary_rectangle_lift.
