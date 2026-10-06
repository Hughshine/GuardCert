From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightNoWrap ClightCountedLoop
  ClightTempFrame ClightLoopSyntax ClightRegionProgress CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineDependentRow
  GuardMemoryAffineChunkWriteSeparation GuardMemoryObservationStability GuardMemoryMultiPointerSequence GuardMemoryWriteReceipts.
From GuardInterface Require Import GuardInterface GuardedRewrite ReadonlyPrefixScan
  ClightReadonlyRewrite ClightConditionComposition ClightReadonlyBranching ClightIndexedAliasGuard
  ClightDependentBoundSyntax ClightDependentHeaderObservations ClightObservedHeaderPrefix
  ClightAffineInnerPointerSourceGuard ClightAffinePreparedState ClightAffinePreparedRows
  ClightAffineDependentLoadedPrefix ClightStorePermissions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition affine_dependent_row_probe source (package : memory_affine_inner_pointer_package source) root pointer_cache i :=
  memory_affine_dependent_row_probe (affine_inner_pointer_row (affine_inner_pointer_shape package))
    (affine_inner_pointer_column (affine_inner_pointer_shape package)) i
    (affine_inner_pointer_expression package) root pointer_cache (affine_inner_pointer_operations package)
    (Z.to_nat (affine_inner_pointer_column_limit package)).
Fixpoint affine_dependent_stability_tree source (package : memory_affine_inner_pointer_package source)
  root pointer_cache fuel i : decision_tree :=
  match fuel with
  | O => Decision true
  | S rest => Test (indexed_active_expr (affine_inner_pointer_bound (affine_inner_pointer_shape package)) i)
      (decision_bind (affine_dependent_row_probe package root pointer_cache i)
        (affine_dependent_stability_tree package root pointer_cache rest (i+1)) (Decision false))
      (Decision true)
  end.
Definition affine_dependent_row_separated source (package : memory_affine_inner_pointer_package source)
  root pointer_cache i entry :=
  forall j, 0 <= j < affine_prepared_upper package entry i ->
    memory_affine_dependent_write_separated (affine_prepared_point_values package entry i j)
      root pointer_cache (affine_inner_pointer_bound (affine_inner_pointer_shape package))
      (affine_inner_pointer_operations package) entry.
Definition affine_dependent_writes_separated source (package : memory_affine_inner_pointer_package source)
  root pointer_cache entry :=
  forall i, 0 <= i < affine_prepared_count package entry -> affine_dependent_row_separated package root pointer_cache i entry.

Section STABILITY.
Variable source : statement.
Variable package : memory_affine_inner_pointer_package source.
Variables root pointer_cache : ident.
Let shape := affine_inner_pointer_shape package.
Let row := affine_inner_pointer_row shape.
Let column := affine_inner_pointer_column shape.
Let inner_bound := affine_inner_pointer_inner_bound shape.
Let cache := affine_inner_pointer_bound shape.
Let CERT := affine_inner_pointer_syntax package.
Hypothesis ROOT_FRESH : root <> row /\ root <> column /\ root <> inner_bound.
Hypothesis POINTER_FRESH : pointer_cache <> row /\ pointer_cache <> column /\ pointer_cache <> inner_bound.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable O : Type.
Variable observe : fragment_observation -> O -> Prop.

Lemma affine_dependent_column_cap : Z.of_nat (Z.to_nat (affine_inner_pointer_column_limit package)) <= Int.max_signed.
Proof.
  pose proof (affine_inner_pointer_control_limits CERT) as CAPS; inversion CAPS; subst;
    match goal with REST : Forall _ [_] |- _ => inversion REST; subst end.
  rewrite Z2Nat.id by lia; unfold signed_range in *; tauto.
Qed.
Definition affine_dependent_row_condition i : readonly_condition (readonly_clight_host fe observe)
  (fun entry => affine_dependent_package_prefix package root pointer_cache fe i entry /\ i < affine_prepared_count package entry)
  (affine_dependent_row_separated package root pointer_cache i) (affine_dependent_row_probe package root pointer_cache i).
Proof.
  eapply readonly_condition_restrict.
  - exact (@memory_affine_dependent_row_condition fe O observe row column root pointer_cache cache i
      (affine_inner_pointer_expression package) (affine_inner_pointer_operations package)
      (Z.to_nat (affine_inner_pointer_column_limit package)) affine_prepared_valuation
      (fun entry j => affine_prepared_point_values package entry i j)
      (fun entry => affine_prepared_upper package entry i) affine_dependent_column_cap).
  - intros entry [INV ACTIVE]; apply (@affine_dependent_package_row_domain source package root pointer_cache
      ROOT_FRESH POINTER_FRESH fe i entry); assumption.
Defined.
Lemma affine_dependent_row_width entry i : affine_dependent_ready package root pointer_cache entry ->
  0 <= i < affine_prepared_count package entry -> 0 <= affine_prepared_upper package entry i.
Proof. intros [READY CACHED] I; pose proof (affine_prepared_upper_range READY I); lia. Qed.
Lemma affine_dependent_point_permissions entry i j before after :
  affine_prepared_point package entry i j before after -> memory_accesses_back before after.
Proof. apply memory_pointer_sequence_accesses_back. Qed.
Lemma affine_dependent_row_preserves i entry :
  affine_dependent_package_prefix package root pointer_cache fe i entry -> i < affine_prepared_count package entry ->
  affine_dependent_row_separated package root pointer_cache i entry ->
  forall observation, In observation (dependent_header_observations root pointer_cache cache entry) ->
  forall j before after, 0 <= j < affine_prepared_upper package entry i ->
    affine_prepared_point package entry i j before after ->
    location_load (fst observation) after = location_load (fst observation) before.
Proof.
  intros INV ACTIVE APART observation MEMBER j before after J STEP.
  eapply memory_pointer_sequence_observation_preserved; [apply (APART j J observation MEMBER)|exact STEP].
Qed.

Definition affine_dependent_prefix_spec : readonly_prefix_spec (readonly_clight_host fe observe) Z :=
  @observed_header_prefix_spec fe row cache (dependent_bound_test row root) (affine_inner_pointer_outer_body shape)
    (affine_dependent_stable package root pointer_cache) (affine_dependent_ready package root pointer_cache)
    (dependent_header_observations root pointer_cache cache) (affine_prepared_upper package) (affine_prepared_point package)
    (@affine_dependent_fresh_row source package root pointer_cache ROOT_FRESH POINTER_FRESH)
    (@affine_prepared_outer_normal source package) (@affine_prepared_outer_quiet source package)
    (@affine_dependent_actual_header source package root pointer_cache)
    (@affine_dependent_actual_row_decode source package root pointer_cache ROOT_FRESH POINTER_FRESH fe)
    affine_dependent_row_width affine_dependent_point_permissions O observe
    (affine_dependent_row_probe package root pointer_cache) (affine_dependent_row_separated package root pointer_cache)
    affine_dependent_row_condition affine_dependent_row_preserves.
Lemma affine_dependent_stability_synthesis fuel i :
  synthesize_prefix_scan (clight_readonly_check_algebra fe observe)
    (clight_readonly_branch_algebra fe observe) affine_dependent_prefix_spec fuel i =
    affine_dependent_stability_tree package root pointer_cache fuel i.
Proof.
  revert i; induction fuel as [|fuel IH]; intros i;
    cbn [synthesize_prefix_scan affine_dependent_stability_tree affine_dependent_prefix_spec
      observed_header_prefix_spec prefix_active_probe prefix_point_probe prefix_next
      observed_header_active_probe clight_readonly_check_algebra clight_readonly_branch_algebra].
  - reflexivity.
  - rewrite IH; reflexivity.
Qed.
Definition affine_dependent_stability_condition : readonly_condition (readonly_clight_host fe observe)
  (fun entry => affine_dependent_loaded_completed package root pointer_cache fe entry /\ affine_inner_pointer_ready package entry)
  (affine_dependent_writes_separated package root pointer_cache)
  (affine_dependent_stability_tree package root pointer_cache (Z.to_nat (affine_inner_pointer_row_limit package)) 0).
Proof.
  rewrite <- affine_dependent_stability_synthesis.
  eapply readonly_condition_entails.
  - eapply readonly_condition_restrict.
    + apply synthesized_prefix_scan_condition.
    + intros entry [SOURCE READY]; apply (@affine_dependent_prefix_initial source package root pointer_cache ROOT_FRESH POINTER_FRESH fe entry);
        assumption.
  - intros entry [SOURCE READY] CHECKED i I.
    eapply (@observed_header_scan_sound fe row cache (dependent_bound_test row root) (affine_inner_pointer_outer_body shape)
      (affine_dependent_stable package root pointer_cache) (affine_dependent_ready package root pointer_cache)
      (dependent_header_observations root pointer_cache cache) (affine_prepared_upper package) (affine_prepared_point package)
      (@affine_dependent_fresh_row source package root pointer_cache ROOT_FRESH POINTER_FRESH)
      (@affine_prepared_outer_normal source package) (@affine_prepared_outer_quiet source package)
      (@affine_dependent_actual_header source package root pointer_cache)
      (@affine_dependent_actual_row_decode source package root pointer_cache ROOT_FRESH POINTER_FRESH fe)
      affine_dependent_row_width affine_dependent_point_permissions O observe
      (affine_dependent_row_probe package root pointer_cache) (affine_dependent_row_separated package root pointer_cache)
      affine_dependent_row_condition affine_dependent_row_preserves
      (Z.to_nat (affine_inner_pointer_row_limit package)) 0 entry CHECKED i).
    + pose proof (affine_prepared_count_range READY) as COUNT; rewrite Z2Nat.id by lia; lia.
    + exact (proj2 I).
Defined.
End STABILITY.

Print Assumptions affine_dependent_row_condition.
Print Assumptions affine_dependent_point_permissions.
Print Assumptions affine_dependent_row_preserves.
Print Assumptions affine_dependent_prefix_spec.
Print Assumptions affine_dependent_stability_synthesis.
Print Assumptions affine_dependent_stability_condition.
