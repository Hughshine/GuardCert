From Stdlib Require Import List ZArith.
From compcert.lib Require Import Integers.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightGuard ClightPureExpr ClightRedundantSet.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax.
From GuardInterface Require Import ClightCheckPlan ClightAffineSnapshotSyntax
  ClightAffineSnapshotCheckPlan ClightAffineSnapshotRowObservation ClightAffineRmwSnapshotCondition
  ClightAffineZeroSnapshotPreparation ClightAffineInnerPointerCandidateGuard ClightZeroRmwCondition.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The constant-size alternative shares the old compact scan on refusal.
    Neither compilation nor the runtime shortcut expands its complete tree. *)
Definition affine_rmw_snapshot_complete_check_plan original(site:affine_snapshot_source_package original)
    (rmw:affine_snapshot_rmw_site site)first later alias validator encoder :=
  let package:=snapshot_cached_package site in
  PlanAnd(PlanAnd(tree_check_plan(affine_zero_snapshot_preparation_tree site first later))
    (PlanTest(register_guard(affine_snapshot_rmw_alpha rmw)Int.zero)(PlanDecision true)
      (affine_snapshot_check_scan_plan package(snapshot_root site)(snapshot_child site)
        (Z.to_nat(affine_inner_pointer_row_limit package))0)))
    (PlanAnd(tree_check_plan alias)
      (tree_check_plan(affine_inner_pointer_candidate_ranges_tree package validator encoder))).

Theorem affine_rmw_snapshot_complete_check_plan_tree original(site:affine_snapshot_source_package original)
    (rmw:affine_snapshot_rmw_site site)first later alias validator encoder :
  check_plan_tree(affine_rmw_snapshot_complete_check_plan rmw first later alias validator encoder)=
  affine_rmw_snapshot_candidate_tree rmw first later alias validator encoder.
Proof.
  unfold affine_rmw_snapshot_complete_check_plan; cbn [check_plan_tree]; rewrite !tree_check_plan_spec.
  unfold affine_rmw_snapshot_candidate_tree,affine_rmw_snapshot_prepare_and_stability_tree,
    affine_rmw_snapshot_stability_tree,affine_rmw_snapshot_scan_tree,zero_rmw_condition,register_tree.
  cbn [decision_bind]; reflexivity.
Qed.

Print Assumptions affine_rmw_snapshot_complete_check_plan_tree.
