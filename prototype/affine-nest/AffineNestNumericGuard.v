From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST.
From Guard Require Import ClightCondition ClightNoWrap ClightPureExpr ClightCountedLoop ClightRedundantSet.
From GuardMemory Require Import GuardMemoryIntervalBox GuardMemoryIntervalGuard GuardMemoryWindowParameterGuard
  GuardMemoryRecursiveSource.
From GuardAffineNest Require Import AffineNestExit AffineNestProfile.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition affine_numeric_guard_tree parameter_ranges parameters iterator floor cap :=
  window_parameters_tree parameter_ranges parameters(signed_interval_tree iterator floor cap).
Definition affine_numeric_guard_flag parameter_ranges parameters iterator floor cap state :=
  window_parameters_accept parameter_ranges parameters state && signed_interval_flag iterator floor cap state.

Theorem affine_numeric_guard_encoding parameter_ranges parameters iterator floor cap state :
  Forall(fun identifier => register_domain identifier state) parameters -> register_domain iterator state ->
  forall flag, decision_run state(affine_numeric_guard_tree parameter_ranges parameters iterator floor cap) flag <->
    flag=affine_numeric_guard_flag parameter_ranges parameters iterator floor cap state.
Proof.
  intros PARAMETERS ITERATOR; apply window_parameters_encoding_exact; [exact PARAMETERS|].
  apply signed_interval_encoding_exact; exact ITERATOR.
Qed.

Definition affine_parameter_intervals_check ranges := forallb(fun range =>
  affine_signed_range_check(fst range) && affine_signed_range_check(snd range-1) && (fst range<?snd range)) ranges.
Lemma affine_parameter_intervals_signed ranges : affine_parameter_intervals_check ranges=true ->
  Forall(fun range => signed_range(fst range) /\ signed_range(snd range-1)) ranges.
Proof.
  intro CHECK; apply Forall_forall; intros range MEMBER.
  apply forallb_forall with(x:=range) in CHECK; [|exact MEMBER].
  rewrite !andb_true_iff in CHECK; destruct CHECK as [[LOW HIGH] NONEMPTY].
  split; apply affine_signed_range_check_sound; assumption.
Qed.

Theorem affine_numeric_guard_sound parameter_ranges parameters iterator floor cap state :
  affine_parameter_intervals_check parameter_ranges=true -> signed_range floor -> signed_range(cap-1) ->
  affine_numeric_guard_flag parameter_ranges parameters iterator floor cap state=true ->
  interval_ranges parameter_ranges(map(affine_word_valuation(entry_temps state)) parameters) /\
  floor<=affine_word_valuation(entry_temps state) iterator<cap.
Proof.
  intros CHECK FLOOR CAP ACCEPT; apply andb_true_iff in ACCEPT as [PARAMETERS START].
  split.
  - apply window_parameters_accept_sound; [apply affine_parameter_intervals_signed; exact CHECK|exact PARAMETERS].
  - apply signed_interval_presumption_exact; assumption.
Qed.
Print Assumptions affine_numeric_guard_encoding.
Print Assumptions affine_parameter_intervals_signed.
Print Assumptions affine_numeric_guard_sound.
