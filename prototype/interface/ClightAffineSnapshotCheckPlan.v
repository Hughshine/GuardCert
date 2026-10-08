From Stdlib Require Import List ZArith.
From compcert.lib Require Import Integers.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightGuard.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineRowSeparation.
From GuardInterface Require Import ClightCheckPlan ClightAffineLoadedCheckPlan ClightIndexedAliasGuard
  ClightAffineSnapshotSyntax ClightAffineSnapshotRowChecks ClightAffineSnapshotScan
  ClightAffineSnapshotCandidateCondition ClightAffineSnapshotCandidateExecution
  ClightAffinePointerSourcePreparation ClightAffineInnerPointerCandidateGuard
  ReadonlyPrefixScan ReadonlyConditionComposition ReadonlyBranching ClightConditionComposition
  ClightReadonlyBranching ClightObservedBodyPrefix.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Lower conjunctions directly. Flattening this plan is only a proof
    specification; the compiler never expands the complete decision tree. *)
Definition affine_snapshot_check_row_plan source(package:memory_affine_inner_pointer_package source)root child i :=
  let shape:=affine_inner_pointer_shape package in
  let one pointer:=affine_loaded_row_plan(affine_inner_pointer_row shape)(affine_inner_pointer_column shape)
    i(affine_inner_pointer_expression package)pointer(affine_inner_pointer_operations package)
    (Z.to_nat(affine_inner_pointer_column_limit package))0 in
  PlanAnd(one root)(one child).
Lemma affine_snapshot_check_row_plan_tree source(package:memory_affine_inner_pointer_package source)root child i :
  check_plan_tree(affine_snapshot_check_row_plan package root child i)=affine_snapshot_row_probe package root child i.
Proof.
  unfold affine_snapshot_check_row_plan; cbn [check_plan_tree]; rewrite !affine_loaded_row_plan_tree; reflexivity.
Qed.

Fixpoint affine_snapshot_check_scan_plan source(package:memory_affine_inner_pointer_package source)root child fuel i :=
  match fuel with
  | O=>PlanDecision true
  | S rest=>PlanTest(indexed_active_expr(affine_inner_pointer_bound(affine_inner_pointer_shape package))i)
      (PlanAnd(affine_snapshot_check_row_plan package root child i)
        (affine_snapshot_check_scan_plan package root child rest(i+1)))(PlanDecision true)
  end.
Lemma affine_snapshot_check_scan_plan_tree original(site:affine_snapshot_source_package original)fe O
    (observe:fragment_observation->O->Prop)fuel : forall i,
  check_plan_tree(affine_snapshot_check_scan_plan(snapshot_cached_package site)(snapshot_root site)(snapshot_child site)fuel i)=
  synthesize_prefix_scan(clight_readonly_check_algebra fe observe)(clight_readonly_branch_algebra fe observe)
    (@affine_snapshot_scan_spec(snapshot_cached_source site)(snapshot_cached_package site)(snapshot_root site)
      (snapshot_child site)(snapshot_child_cache site)(snapshot_original_header site)
      (snapshot_root_protected site)(snapshot_child_protected site)(snapshot_cache_member site)
      (snapshot_header_word site)(snapshot_cached_body_exact site)fe O observe)fuel i.
Proof.
  induction fuel as [|fuel IH]; intro i;
    cbn [affine_snapshot_check_scan_plan check_plan_tree synthesize_prefix_scan constant_check branch_check
      clight_readonly_check_algebra clight_readonly_branch_algebra prefix_active_probe prefix_point_probe prefix_next
      affine_snapshot_scan_spec observed_body_prefix_spec]; [reflexivity|].
  rewrite affine_snapshot_check_row_plan_tree,IH; reflexivity.
Qed.

Definition affine_snapshot_complete_check_plan original(site:affine_snapshot_source_package original)
    width alias validator encoder :=
  let package:=snapshot_cached_package site in
  PlanAnd(PlanAnd(tree_check_plan(affine_inner_pointer_package_preparation_tree package width))
    (affine_snapshot_check_scan_plan package(snapshot_root site)(snapshot_child site)
      (Z.to_nat(affine_inner_pointer_row_limit package))0))
    (tree_check_plan(affine_inner_pointer_candidate_guard_tree package width alias validator encoder)).
Theorem affine_snapshot_complete_check_plan_tree original(site:affine_snapshot_source_package original)
    width alias validator encoder :
  check_plan_tree(affine_snapshot_complete_check_plan site width alias validator encoder)=
  affine_snapshot_installed_tree site width alias validator encoder.
Proof.
  unfold affine_snapshot_complete_check_plan; cbn [check_plan_tree]; rewrite !tree_check_plan_spec.
  rewrite(affine_snapshot_check_scan_plan_tree site(adapter_entry true)(@eq fragment_observation)).
  reflexivity.
Qed.

Print Assumptions affine_snapshot_check_row_plan_tree.
Print Assumptions affine_snapshot_check_scan_plan_tree.
Print Assumptions affine_snapshot_complete_check_plan_tree.
