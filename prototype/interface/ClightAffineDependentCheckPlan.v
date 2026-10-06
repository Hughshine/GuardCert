From Stdlib Require Import List ZArith.
From compcert.lib Require Import Integers.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightCondition ClightPureExpr.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineRowSeparation
  GuardMemoryAffineWriteSeparation GuardMemoryNaryCompute GuardMemoryAffineChunkWriteSeparation.
From GuardInterface Require Import ClightCheckPlan ClightReadonlyExpressionScan ClightIndexedAliasGuard
  ClightAffineLoadedStability ClightAffineDependentLoadedStability ClightAffineInnerPointerCandidate ClightAffineInnerPointerCandidateGuard
  ClightAffineInnerPointerSourceGuard ClightAffinePointerSourcePreparation.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint affine_dependent_row_plan row column i expression root pointer_cache operations fuel j :=
  match fuel with
  | O => PlanDecision true
  | S rest => PlanTest (Ebinop Olt (Econst_int (Int.repr j) type_int32s)
      (memory_affine_row_bound row column i expression) type_int32s)
      (PlanAnd (tree_check_plan (memory_affine_dependent_write_probe row column i j root pointer_cache operations))
        (affine_dependent_row_plan row column i expression root pointer_cache operations rest (j+1)))
      (PlanDecision true)
  end.
Lemma affine_dependent_row_plan_tree row column i expression root pointer_cache operations fuel : forall j,
  check_plan_tree (affine_dependent_row_plan row column i expression root pointer_cache operations fuel j) =
  readonly_bound_expression_scan (memory_affine_row_bound row column i expression)
    (fun j => memory_affine_dependent_write_probe row column i j root pointer_cache operations) fuel j.
Proof.
  induction fuel; intros j; cbn [affine_dependent_row_plan check_plan_tree readonly_bound_expression_scan];
    [reflexivity|rewrite tree_check_plan_spec,IHfuel; reflexivity].
Qed.

Fixpoint affine_dependent_stability_plan source (package : memory_affine_inner_pointer_package source) root pointer_cache fuel i :=
  match fuel with
  | O => PlanDecision true
  | S rest => PlanTest (indexed_active_expr (affine_inner_pointer_bound (affine_inner_pointer_shape package)) i)
      (PlanAnd (affine_dependent_row_plan (affine_inner_pointer_row (affine_inner_pointer_shape package))
          (affine_inner_pointer_column (affine_inner_pointer_shape package)) i
          (affine_inner_pointer_expression package) root pointer_cache (affine_inner_pointer_operations package)
          (Z.to_nat (affine_inner_pointer_column_limit package)) 0)
        (affine_dependent_stability_plan package root pointer_cache rest (i+1)))
      (PlanDecision true)
  end.
Lemma affine_dependent_stability_plan_tree source (package : memory_affine_inner_pointer_package source) root pointer_cache fuel : forall i,
  check_plan_tree (affine_dependent_stability_plan package root pointer_cache fuel i) = affine_dependent_stability_tree package root pointer_cache fuel i.
Proof.
  induction fuel; intros i; cbn [affine_dependent_stability_plan affine_dependent_stability_tree check_plan_tree];
    [reflexivity|rewrite affine_dependent_row_plan_tree,IHfuel; reflexivity].
Qed.

Definition affine_dependent_complete_plan source (package : memory_affine_inner_pointer_package source)
  root pointer_cache width alias validator_bounds encoder_bounds :=
  PlanAnd (PlanAnd (tree_check_plan (affine_inner_pointer_package_preparation_tree package width))
    (affine_dependent_stability_plan package root pointer_cache (Z.to_nat (affine_inner_pointer_row_limit package)) 0))
    (tree_check_plan (affine_inner_pointer_candidate_guard_tree package width alias validator_bounds encoder_bounds)).
Lemma affine_dependent_complete_plan_tree source (package : memory_affine_inner_pointer_package source)
  root pointer_cache width alias validator_bounds encoder_bounds :
  check_plan_tree (affine_dependent_complete_plan package root pointer_cache width alias validator_bounds encoder_bounds) =
  decision_bind (decision_bind (affine_inner_pointer_package_preparation_tree package width)
    (affine_dependent_stability_tree package root pointer_cache (Z.to_nat (affine_inner_pointer_row_limit package)) 0) (Decision false))
    (affine_inner_pointer_candidate_guard_tree package width alias validator_bounds encoder_bounds) (Decision false).
Proof. unfold affine_dependent_complete_plan; cbn [check_plan_tree];
  rewrite !tree_check_plan_spec,affine_dependent_stability_plan_tree; reflexivity. Qed.

Print Assumptions affine_dependent_row_plan_tree.
Print Assumptions affine_dependent_stability_plan_tree.
Print Assumptions affine_dependent_complete_plan_tree.
