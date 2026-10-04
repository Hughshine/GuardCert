From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes Cop ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightGuard ClightNoWrap
  ClightCountedLoop ClightRedundantSet ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRecursiveSource GuardMemoryVectorBounds
  GuardMemoryTripleGuard GuardMemoryParameterRanges.
From GuardMemory Require Import GuardMemoryStartedSourceWords.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_started_active_flag iterator bound s :=
  Int.lt (temp_word iterator (entry_temps s)) (temp_word bound (entry_temps s)).
Definition memory_started_active_tree iterator bound :=
  Test (counter_condition iterator bound) (Decision true) (Decision false).
Lemma memory_started_active_test iterator bound s :
  register_domain iterator s -> register_domain bound s ->
  expression_test (counter_condition iterator bound) s (memory_started_active_flag iterator bound s).
Proof.
  intros [word WORD] [upper BOUND].
  exists (Val.of_bool (Int.lt word upper)); split.
  - eapply eval_Ebinop; [constructor; exact WORD|constructor; exact BOUND|reflexivity].
  - unfold memory_started_active_flag,temp_word; rewrite WORD,BOUND; apply bool_of_bool.
Qed.
Lemma memory_started_active_run iterator bound s :
  register_domain iterator s -> register_domain bound s ->
  decision_run s (memory_started_active_tree iterator bound) (memory_started_active_flag iterator bound s).
Proof.
  intros ITERATOR BOUND; unfold memory_started_active_tree.
  eapply run_test; [apply memory_started_active_test; assumption|].
  destruct (memory_started_active_flag iterator bound s); constructor.
Qed.
Lemma memory_started_active_exact iterator bound s :
  register_domain iterator s -> register_domain bound s -> forall flag,
  decision_run s (memory_started_active_tree iterator bound) flag <-> flag = memory_started_active_flag iterator bound s.
Proof.
  intros ITERATOR BOUND flag.
  assert (PURE : pure_tree (memory_started_active_tree iterator bound)).
  { unfold memory_started_active_tree,counter_condition; repeat constructor. }
  split.
  - intro RUN; eapply pure_tree_determinate; [exact PURE|exact RUN|].
    apply memory_started_active_run; assumption.
  - intro SAME; subst; apply memory_started_active_run; assumption.
Qed.
Lemma memory_started_active_true iterator bound s :
  memory_started_active_flag iterator bound s = true <->
  Int.signed (temp_word iterator (entry_temps s)) < Int.signed (temp_word bound (entry_temps s)).
Proof.
  unfold memory_started_active_flag,Int.lt.
  destruct (zlt (Int.signed (temp_word iterator (entry_temps s)))
    (Int.signed (temp_word bound (entry_temps s)))); cbn; split; intro H; auto; try discriminate; lia.
Qed.
Definition memory_started_bounds_accept rootcap caps iterator bound bounds s :=
  memory_started_active_flag iterator bound s &&
    (memory_parameter_range_flag iterator rootcap s && memory_vector_bounds_accept caps bounds s).
Definition memory_started_bounds_tree rootcap caps iterator bound bounds :=
  decision_bind (memory_started_active_tree iterator bound)
    (decision_bind (memory_parameter_range_tree iterator rootcap)
      (memory_vector_bounds_tree caps bounds (Decision true)) (Decision false)) (Decision false).
Definition memory_started_bounds_domain caps iterator bound bounds s :=
  register_domain iterator s /\ register_domain bound s /\
  (memory_started_active_flag iterator bound s = true -> memory_vector_bounds_domain caps bounds s).
Theorem memory_started_bounds_exact rootcap caps iterator bound bounds s :
  memory_started_bounds_domain caps iterator bound bounds s -> forall flag,
  decision_run s (memory_started_bounds_tree rootcap caps iterator bound bounds) flag <->
  flag = memory_started_bounds_accept rootcap caps iterator bound bounds s.
Proof.
  intros [ITERATOR [BOUND COUNTS]] flag; unfold memory_started_bounds_tree,memory_started_bounds_accept.
  apply memory_guard_gate_exact; [apply memory_started_active_exact; assumption|].
  intro ACTIVE; intro result; apply memory_guard_gate_exact; [apply memory_parameter_range_exact; exact ITERATOR|].
  intros NONNEG accepted.
  rewrite <- (andb_true_r (memory_vector_bounds_accept caps bounds s)).
  apply memory_vector_bounds_exact; [apply COUNTS; exact ACTIVE|].
  intros ALL value; split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
Qed.
Theorem memory_started_bounds_sound rootcap caps iterator bound bounds s :
  0 < rootcap -> signed_range rootcap -> Forall signed_range caps ->
  memory_started_bounds_domain caps iterator bound bounds s ->
  memory_started_bounds_accept rootcap caps iterator bound bounds s = true ->
  0 <= Int.signed (temp_word iterator (entry_temps s)) < Int.signed (temp_word bound (entry_temps s)) /\
  Forall2 (fun cap key => register_range key cap s) caps bounds.
Proof.
  intros POSITIVE SIGNED CAPS [ITERATOR [BOUND DOMAIN]] ACCEPT.
  unfold memory_started_bounds_accept in ACCEPT; rewrite !andb_true_iff in ACCEPT.
  destruct ACCEPT as [ACTIVE [NONNEG COUNTS]].
  split.
  - pose proof (@memory_parameter_range_sound iterator rootcap s POSITIVE SIGNED NONNEG) as RANGE.
    apply memory_started_active_true in ACTIVE; lia.
  - apply memory_vector_bounds_sound; [exact CAPS|apply DOMAIN; exact ACTIVE|exact COUNTS].
Qed.
Print Assumptions memory_started_bounds_exact.
Print Assumptions memory_started_bounds_sound.
