From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Integers.
From Guard Require Import ClightCondition ClightPureExpr ClightNoWrap ClightCountedLoop ClightRedundantSet ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryStartedHeader GuardMemoryVectorBounds GuardMemoryTripleGuard.
From GuardMemory Require Import GuardMemoryIntervalGuard GuardMemoryWindowParameterGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition window_bounds_accept root_lower root_cap caps iterator bound bounds s :=
  memory_started_active_flag iterator bound s &&
    (signed_interval_flag iterator root_lower root_cap s && memory_vector_bounds_accept caps bounds s).
Definition window_bounds_tree root_lower root_cap caps iterator bound bounds :=
  decision_bind (memory_started_active_tree iterator bound)
    (decision_bind (signed_interval_tree iterator root_lower root_cap)
      (memory_vector_bounds_tree caps bounds (Decision true)) (Decision false)) (Decision false).
Theorem window_bounds_encoding_exact root_lower root_cap caps iterator bound bounds s :
  memory_started_bounds_domain caps iterator bound bounds s -> forall flag,
  decision_run s (window_bounds_tree root_lower root_cap caps iterator bound bounds) flag <->
    flag = window_bounds_accept root_lower root_cap caps iterator bound bounds s.
Proof.
  intros [ITERATOR [BOUND COUNTS]] flag; unfold window_bounds_tree,window_bounds_accept.
  apply memory_guard_gate_exact; [apply memory_started_active_exact; assumption|].
  intros ACTIVE result; apply memory_guard_gate_exact; [apply signed_interval_encoding_exact; exact ITERATOR|].
  intros ROOT accepted; rewrite <- (andb_true_r (memory_vector_bounds_accept caps bounds s)).
  apply memory_vector_bounds_exact; [apply COUNTS; exact ACTIVE|].
  intros ALL value; split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
Qed.
Theorem window_bounds_sound root_lower root_cap caps iterator bound bounds s :
  signed_range root_lower -> signed_range (root_cap-1) -> Forall signed_range caps ->
  memory_started_bounds_domain caps iterator bound bounds s ->
  window_bounds_accept root_lower root_cap caps iterator bound bounds s = true ->
  root_lower <= Int.signed (temp_word iterator (entry_temps s)) < Int.signed (temp_word bound (entry_temps s)) /\
  Int.signed (temp_word iterator (entry_temps s)) < root_cap /\
  Forall2 (fun cap key => register_range key cap s) caps bounds.
Proof.
  intros LOWER UPPER CAPS [ITERATOR [BOUND DOMAIN]] ACCEPT.
  unfold window_bounds_accept in ACCEPT; rewrite !andb_true_iff in ACCEPT.
  destruct ACCEPT as [ACTIVE [ROOT COUNTS]].
  apply memory_started_active_true in ACTIVE.
  apply signed_interval_presumption_exact in ROOT; [|exact LOWER|exact UPPER].
  split; [lia|split; [lia|]].
  apply memory_vector_bounds_sound; [exact CAPS|apply DOMAIN; apply memory_started_active_true; exact ACTIVE|exact COUNTS].
Qed.
Definition window_header_accept root_lower root_cap caps iterator bound bounds parameter_bounds parameters s :=
  window_bounds_accept root_lower root_cap caps iterator bound bounds s &&
  window_parameters_accept parameter_bounds parameters s.
Definition window_header_tree root_lower root_cap caps iterator bound bounds parameter_bounds parameters :=
  decision_bind (window_bounds_tree root_lower root_cap caps iterator bound bounds)
    (window_parameters_tree parameter_bounds parameters (Decision true)) (Decision false).
Definition window_header_domain root_lower root_cap caps iterator bound bounds parameters s :=
  memory_started_bounds_domain caps iterator bound bounds s /\
  (window_bounds_accept root_lower root_cap caps iterator bound bounds s = true ->
   Forall (fun identifier => register_domain identifier s) parameters).
Theorem window_header_encoding_exact root_lower root_cap caps iterator bound bounds parameter_bounds parameters s :
  window_header_domain root_lower root_cap caps iterator bound bounds parameters s -> forall flag,
  decision_run s (window_header_tree root_lower root_cap caps iterator bound bounds parameter_bounds parameters) flag <->
    flag = window_header_accept root_lower root_cap caps iterator bound bounds parameter_bounds parameters s.
Proof.
  intros [DOMAIN PARAMETERS] flag; unfold window_header_tree,window_header_accept.
  replace (window_parameters_accept parameter_bounds parameters s) with
    (window_parameters_accept parameter_bounds parameters s && true) at 1 by (rewrite andb_true_r; reflexivity).
  apply memory_guard_gate_exact; [apply window_bounds_encoding_exact; exact DOMAIN|].
  intros ACCEPT result; apply window_parameters_encoding_exact; [apply PARAMETERS; exact ACCEPT|].
  intro value; split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
Qed.
Print Assumptions window_header_encoding_exact.
Print Assumptions window_bounds_sound.
