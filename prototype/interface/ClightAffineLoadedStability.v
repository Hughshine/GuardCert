From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightCountedLoop ClightTempFrame
  ClightPureExpr ClightLoopSyntax ClightRegionProgress CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryNaryCompute
  GuardMemoryAffineRowSeparation GuardMemoryAffineWriteSeparation GuardMemoryWriteReceipts
  GuardMemoryObservationStability GuardMemoryAffinePointerLoadedDomain.
From GuardInterface Require Import GuardInterface GuardedRewrite ReadonlyPrefixScan
  ClightReadonlyRewrite ClightConditionComposition ClightReadonlyBranching ClightIndexedAliasGuard
  ClightLoadedRowScan ClightAffineInnerPointerSourceGuard ClightAffinePreparedState
  ClightAffinePreparedRows ClightAffineLoadedPrefix ClightStorePermissions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition affine_loaded_row_probe source (package : memory_affine_inner_pointer_package source) pointer i :=
  memory_affine_row_probe (affine_inner_pointer_row (affine_inner_pointer_shape package))
    (affine_inner_pointer_column (affine_inner_pointer_shape package)) i
    (affine_inner_pointer_expression package) pointer (affine_inner_pointer_operations package)
    (Z.to_nat (affine_inner_pointer_column_limit package)).

(** Runtime syntax is independent of the ghost prefix and execution witness.
    Each next row is reached only after the previous row probe accepts. *)
Fixpoint affine_loaded_stability_tree source (package : memory_affine_inner_pointer_package source)
  pointer fuel i : decision_tree :=
  match fuel with
  | O => Decision true
  | S rest => Test (indexed_active_expr (affine_inner_pointer_bound (affine_inner_pointer_shape package)) i)
      (decision_bind (affine_loaded_row_probe package pointer i)
        (affine_loaded_stability_tree package pointer rest (i+1)) (Decision false))
      (Decision true)
  end.

Definition affine_loaded_row_separated source (package : memory_affine_inner_pointer_package source) pointer i entry :=
  forall j, 0 <= j < affine_prepared_upper package entry i ->
    memory_affine_writes_separated (affine_prepared_point_values package entry i j)
      pointer (affine_inner_pointer_operations package) entry.
Definition affine_loaded_writes_separated source (package : memory_affine_inner_pointer_package source) pointer entry :=
  forall i, 0 <= i < affine_prepared_count package entry -> affine_loaded_row_separated package pointer i entry.

Section STABILITY.
Variable source : statement.
Variable package : memory_affine_inner_pointer_package source.
Variable pointer : ident.
Let shape := affine_inner_pointer_shape package.
Let row := affine_inner_pointer_row shape.
Let column := affine_inner_pointer_column shape.
Let inner_bound := affine_inner_pointer_inner_bound shape.
Let cache := affine_inner_pointer_bound shape.
Let CERT := affine_inner_pointer_syntax package.
Hypothesis FRESH : pointer <> row /\ pointer <> column /\ pointer <> inner_bound.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable O : Type.
Variable observe : fragment_observation -> O -> Prop.

Lemma affine_loaded_column_cap : Z.of_nat (Z.to_nat (affine_inner_pointer_column_limit package)) <= Int.max_signed.
Proof.
  pose proof (affine_inner_pointer_control_limits CERT) as CAPS; inversion CAPS; subst;
    match goal with REST : Forall _ [_] |- _ => inversion REST; subst end.
  rewrite Z2Nat.id by lia; unfold signed_range in *; tauto.
Qed.

Definition affine_loaded_row_condition i : readonly_condition (readonly_clight_host fe observe)
  (fun entry => affine_loaded_package_prefix package pointer fe i entry /\ i < affine_prepared_count package entry)
  (affine_loaded_row_separated package pointer i) (affine_loaded_row_probe package pointer i).
Proof.
  eapply readonly_condition_restrict.
  - exact (@memory_affine_row_separation_condition fe O observe row column pointer i
      (affine_inner_pointer_expression package) (affine_inner_pointer_operations package)
      (Z.to_nat (affine_inner_pointer_column_limit package)) affine_prepared_valuation
      (fun entry j => affine_prepared_point_values package entry i j)
      (fun entry => affine_prepared_upper package entry i) affine_loaded_column_cap).
  - intros entry [INV ACTIVE]; apply (@affine_loaded_package_row_domain source package pointer FRESH fe i entry);
      assumption.
Defined.

Lemma affine_loaded_row_width entry i : affine_inner_pointer_ready package entry ->
  0 <= i < affine_prepared_count package entry -> 0 <= affine_prepared_upper package entry i.
Proof. intros READY I; pose proof (affine_prepared_upper_range READY I); lia. Qed.

Lemma affine_loaded_point_permissions entry i j before after :
  affine_prepared_point package entry i j before after -> memory_accesses_back before after.
Proof. apply memory_pointer_sequence_accesses_back. Qed.

Lemma affine_loaded_row_preserves i entry :
  affine_loaded_package_prefix package pointer fe i entry -> i < affine_prepared_count package entry ->
  affine_loaded_row_separated package pointer i entry ->
  forall block offset, (entry_temps entry) ! pointer = Some (Vptr block offset) ->
  forall j before after, 0 <= j < affine_prepared_upper package entry i ->
    affine_prepared_point package entry i j before after ->
    location_load (MemoryLocation Mint32 block (Ptrofs.unsigned offset)) after =
    location_load (MemoryLocation Mint32 block (Ptrofs.unsigned offset)) before.
Proof.
  intros INV ACTIVE APART block offset POINTER j before after J STEP.
  eapply memory_pointer_sequence_observation_preserved; [|exact STEP].
  apply (APART j J); exact POINTER.
Qed.

Definition affine_loaded_prefix_spec : readonly_prefix_spec (readonly_clight_host fe observe) Z :=
  @loaded_rows_prefix_spec fe O observe row cache pointer (affine_inner_pointer_outer_body shape)
    (affine_prepared_stable package pointer) (affine_inner_pointer_ready package)
    (affine_prepared_upper package) (affine_prepared_point package)
    (@affine_loaded_prefix_parameter source package pointer)
    (@affine_loaded_prefix_fresh_row source package pointer FRESH)
    (@affine_prepared_outer_normal source package) (@affine_prepared_outer_quiet source package)
    (@affine_prepared_actual_row_decode source package pointer FRESH fe)
    affine_loaded_row_width affine_loaded_point_permissions
    (affine_loaded_row_probe package pointer) (affine_loaded_row_separated package pointer)
    affine_loaded_row_condition affine_loaded_row_preserves.

Lemma affine_loaded_stability_synthesis fuel i :
  synthesize_prefix_scan (clight_readonly_check_algebra fe observe)
    (clight_readonly_branch_algebra fe observe) affine_loaded_prefix_spec fuel i =
    affine_loaded_stability_tree package pointer fuel i.
Proof.
  revert i; induction fuel as [|fuel IH]; intros i;
    cbn [synthesize_prefix_scan affine_loaded_stability_tree affine_loaded_prefix_spec
      loaded_rows_prefix_spec prefix_active_probe prefix_point_probe prefix_next
      loaded_rows_active_probe clight_readonly_check_algebra clight_readonly_branch_algebra].
  - reflexivity.
  - rewrite IH; reflexivity.
Qed.

Definition affine_loaded_stability_condition : readonly_condition (readonly_clight_host fe observe)
  (fun entry => memory_affine_pointer_loaded_completed package pointer fe entry /\ affine_inner_pointer_ready package entry)
  (affine_loaded_writes_separated package pointer)
  (affine_loaded_stability_tree package pointer (Z.to_nat (affine_inner_pointer_row_limit package)) 0).
Proof.
  rewrite <- affine_loaded_stability_synthesis.
  eapply readonly_condition_entails.
  - eapply readonly_condition_restrict.
    + apply synthesized_prefix_scan_condition.
    + intros entry [SOURCE READY]; apply (@affine_loaded_package_prefix_initial source package pointer FRESH fe entry);
        assumption.
  - intros entry [SOURCE READY] CHECKED i I.
    eapply (@loaded_rows_scan_sound fe O observe row cache pointer (affine_inner_pointer_outer_body shape)
      (affine_prepared_stable package pointer) (affine_inner_pointer_ready package)
      (affine_prepared_upper package) (affine_prepared_point package)
      (@affine_loaded_prefix_parameter source package pointer)
      (@affine_loaded_prefix_fresh_row source package pointer FRESH)
      (@affine_prepared_outer_normal source package) (@affine_prepared_outer_quiet source package)
      (@affine_prepared_actual_row_decode source package pointer FRESH fe)
      affine_loaded_row_width affine_loaded_point_permissions
      (affine_loaded_row_probe package pointer) (affine_loaded_row_separated package pointer)
      affine_loaded_row_condition affine_loaded_row_preserves
      (Z.to_nat (affine_inner_pointer_row_limit package)) 0 entry CHECKED i).
    + pose proof (affine_prepared_count_range READY) as COUNT.
      rewrite Z2Nat.id by lia; lia.
    + exact (proj2 I).
Defined.
End STABILITY.

Print Assumptions affine_loaded_row_condition.
Print Assumptions affine_loaded_point_permissions.
Print Assumptions affine_loaded_row_preserves.
Print Assumptions affine_loaded_prefix_spec.
Print Assumptions affine_loaded_stability_synthesis.
Print Assumptions affine_loaded_stability_condition.
