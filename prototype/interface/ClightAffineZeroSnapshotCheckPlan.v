From Stdlib Require Import List ZArith.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightGuard.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax.
From GuardInterface Require Import ClightCheckPlan ClightAffineSnapshotSyntax
  ClightAffineSnapshotCheckPlan ClightAffineSnapshotScan ClightAffineZeroSnapshotScan
  ClightAffineZeroSnapshotPreparation ClightAffineZeroSnapshotCandidateCondition
  ClightAffineZeroSnapshotCandidateExecution ClightAffineInnerPointerCandidateGuard.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Reuse the proved scan plan. Only its invocation domain and the numeric
    preparation/candidate certificates change. No complete scan tree is expanded
    during extracted compilation. *)
Definition affine_zero_snapshot_complete_check_plan original(site:affine_snapshot_source_package original)
    first later alias validator encoder:=
  let package:=snapshot_cached_package site in
  PlanAnd(PlanAnd(tree_check_plan(affine_zero_snapshot_preparation_tree site first later))
    (affine_snapshot_check_scan_plan package(snapshot_root site)(snapshot_child site)
      (Z.to_nat(affine_inner_pointer_row_limit package))0))
    (PlanAnd(tree_check_plan alias)
      (tree_check_plan(affine_inner_pointer_candidate_ranges_tree package validator encoder))).

Theorem affine_zero_snapshot_complete_check_plan_tree original(site:affine_snapshot_source_package original)
    first later alias validator encoder :
  check_plan_tree(affine_zero_snapshot_complete_check_plan site first later alias validator encoder)=
  affine_zero_snapshot_installed_tree site first later alias validator encoder.
Proof.
  unfold affine_zero_snapshot_complete_check_plan; cbn [check_plan_tree]; rewrite !tree_check_plan_spec.
  rewrite(affine_snapshot_check_scan_plan_tree site(adapter_entry true)(@eq fragment_observation)).
  unfold affine_zero_snapshot_installed_tree,affine_zero_snapshot_candidate_tree,affine_zero_snapshot_prepare_and_scan_tree.
  rewrite(@affine_zero_snapshot_scan_tree_reuses_original(snapshot_cached_source site)(snapshot_cached_package site)
    (snapshot_root site)(snapshot_child site)(snapshot_child_cache site)(snapshot_original_header site)
    (snapshot_root_protected site)(snapshot_child_protected site)(snapshot_cache_member site)
    (snapshot_header_word site)(snapshot_cached_body_exact site)(adapter_entry true)
    fragment_observation(@eq fragment_observation)).
  reflexivity.
Qed.

Print Assumptions affine_zero_snapshot_complete_check_plan_tree.
