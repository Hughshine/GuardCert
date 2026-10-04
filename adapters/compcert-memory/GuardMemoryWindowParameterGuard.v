From Stdlib Require Import List ZArith Lia Bool.
From compcert.common Require Import AST.
From Guard Require Import ClightCondition ClightNoWrap ClightRedundantSet ClightPureExpr ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRecursiveDomain GuardMemoryRecursiveSource GuardMemoryTripleGuard.
From GuardMemory Require Import GuardMemoryIntervalBox GuardMemoryIntervalGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Fixpoint window_parameters_accept bounds identifiers s :=
  match bounds,identifiers with
  | [],[] => true
  | (lower,upper)::rest,identifier::tail => signed_interval_flag identifier lower upper s && window_parameters_accept rest tail s
  | _,_ => false end.
Fixpoint window_parameters_tree bounds identifiers target :=
  match bounds,identifiers with
  | [],[] => target
  | (lower,upper)::rest,identifier::tail => decision_bind (signed_interval_tree identifier lower upper)
      (window_parameters_tree rest tail target) (Decision false)
  | _,_ => Decision false end.
Theorem window_parameters_encoding_exact bounds identifiers target s flag :
  Forall (fun identifier => register_domain identifier s) identifiers ->
  (forall value, decision_run s target value <-> value = flag) -> forall value,
  decision_run s (window_parameters_tree bounds identifiers target) value <->
    value = (window_parameters_accept bounds identifiers s && flag).
Proof.
  revert identifiers; induction bounds as [|[lower upper] bounds IH]; intros [|identifier identifiers] DOMAIN TARGET value;
    cbn [window_parameters_tree window_parameters_accept]; inversion DOMAIN; subst.
  - exact (TARGET value).
  - split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
  - split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
  - rewrite <-andb_assoc; apply memory_guard_gate_exact; [apply signed_interval_encoding_exact; assumption|].
    intros ACCEPT next; apply IH; assumption.
Qed.
Theorem window_parameters_accept_sound bounds identifiers s :
  Forall (fun bound => signed_range (fst bound) /\ signed_range (snd bound-1)) bounds ->
  window_parameters_accept bounds identifiers s = true ->
  interval_ranges bounds (memory_recursive_parameters identifiers (entry_temps s)).
Proof.
  revert identifiers; induction bounds as [|[lower upper] bounds IH]; intros [|identifier identifiers] SIGNED ACCEPT;
    cbn [window_parameters_accept memory_recursive_parameters map] in ACCEPT |- *;
    try discriminate; inversion SIGNED; subst; constructor.
  - apply andb_true_iff in ACCEPT as [HEAD TAIL]; apply signed_interval_presumption_exact; [apply H1|apply H1|exact HEAD].
  - apply IH; [assumption|apply andb_true_iff in ACCEPT; tauto].
Qed.
Print Assumptions window_parameters_encoding_exact.
Print Assumptions window_parameters_accept_sound.
