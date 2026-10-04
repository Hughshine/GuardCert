From Stdlib Require Import List ZArith Lia.
From GuardMemory Require Import GuardMemoryNaryLoops GuardMemoryRecursiveBody GuardMemoryStartedScalarLift.
From GuardMemory Require Import GuardMemoryIntervalBox.
From GuardMemory Require Import GuardMemoryWindowSyntax.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Lemma window_source_inner_ranges counts caps values :
  Forall2 (fun count cap => Z.of_nat count <= cap) counts caps ->
  Forall2 (fun count value => 0 <= value < Z.of_nat count) counts values ->
  interval_ranges (map (fun cap => (0,cap)) caps) values.
Proof.
  intros CAPS; revert values; induction CAPS; intros values RANGES; inversion RANGES; subst;
    cbn [map]; constructor; [cbn; lia|apply IHCAPS; assumption].
Qed.
Lemma window_source_domain_ranges start upper counts root_lower root_cap caps coordinates :
  root_lower <= start -> Z.of_nat upper <= root_cap ->
  Forall2 (fun count cap => Z.of_nat count <= cap) counts caps ->
  memory_started_domain upper counts start coordinates ->
  interval_ranges ((root_lower,root_cap)::map (fun cap => (0,cap)) caps) coordinates.
Proof.
  intros LOWER UPPER CAPS [x [RANGE DOMAIN]].
  destruct (@memory_nary_domain_suffix counts [x] coordinates DOMAIN) as [suffix [VALUES RANGES]].
  rewrite VALUES; cbn [app]; constructor; [cbn; lia|].
  eapply window_source_inner_ranges; eassumption.
Qed.
Lemma window_interval_ranges_append first second values rest :
  interval_ranges first values -> interval_ranges second rest -> interval_ranges (first++second) (values++rest).
Proof. intros FIRST SECOND; unfold interval_ranges in *; apply Forall2_app; assumption. Qed.
Print Assumptions window_source_domain_ranges.
Lemma window_source_bounds_domain start upper counts root_lower caps coordinates :
  root_lower <= start ->
  Forall2 (fun count cap => Z.of_nat count <= cap) (upper::counts) caps ->
  memory_started_domain upper counts start coordinates ->
  interval_ranges (window_source_coordinate_bounds root_lower caps) coordinates.
Proof.
  intros LOWER CAPS DOMAIN; inversion CAPS; subst.
  cbn [window_source_coordinate_bounds]; eapply window_source_domain_ranges; eassumption.
Qed.
