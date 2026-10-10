From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Clight ClightBigstep.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleSourceTreeData
  GuardMemoryDoubleSourceTreeState GuardMemoryDoubleTreeCaptureData GuardMemoryDoubleTreeCaptureReceipt
  GuardMemoryDoubleTreeCaptureFacts GuardMemoryDoubleTreeCacheFrame GuardMemoryDoubleTreeActiveValuation
  GuardMemoryDoubleTreeCacheParameters GuardMemoryLongExpressionCapture.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition double_tree_active_profile tree valuation lower upper :=
  forall header, In header (double_source_tree_active_headers valuation tree) -> lower header<=valuation header<=upper header.
Theorem double_tree_capture_accepted_profile ge locals memory cache flag lower upper tree temps after accepted :
  double_tree_capture_receipt ge locals memory cache flag lower upper tree temps after accepted -> accepted=true ->
  double_tree_active_profile tree (double_tree_observed_value ge memory) lower upper.
Proof.
  intro RECEIPT; induction RECEIPT; intros ACCEPT header MEMBER; try discriminate; try solve [contradiction].
  - pose proof (@double_tree_flag_values_unique middle flag accepted_first true
      (double_tree_capture_receipt_flag RECEIPT1) (double_tree_capture_receipt_started RECEIPT2 ACCEPT)) as FIRST.
    apply in_app_or in MEMBER as [MEMBER|MEMBER]; [apply IHRECEIPT1|apply IHRECEIPT2]; assumption.
  - pose proof (@double_tree_accepted_active_value ge locals memory start bound block input
      (lower (tree_bound_header bound)) (upper (tree_bound_header bound)) H0 H1 (proj1 H2) (proj2 H3) H4) as ACTIVE.
    rewrite H5 in ACTIVE; cbn [double_source_tree_active_headers] in MEMBER; rewrite <- ACTIVE in MEMBER.
    destruct MEMBER as [SAME|[]]; subst header.
    rewrite (@double_tree_observed_load ge locals memory _ block input H0 H1); apply memory_long_expression_accept_spec; exact H4.
  - pose proof (@double_tree_accepted_active_value ge locals memory start bound block input
      (lower (tree_bound_header bound)) (upper (tree_bound_header bound)) H0 H1 (proj1 H2) (proj2 H3) H4) as ACTIVE.
    rewrite H5 in ACTIVE; cbn [double_source_tree_active_headers] in MEMBER; rewrite <- ACTIVE in MEMBER.
    destruct MEMBER as [SAME|MEMBER].
    + subst header; rewrite (@double_tree_observed_load ge locals memory _ block input H0 H1).
      apply memory_long_expression_accept_spec; exact H4.
    + apply IHRECEIPT; assumption.
Qed.
Theorem double_tree_capture_cached_profile ge locals memory cache flag lower upper tree temps after accepted :
  double_tree_capture_receipt ge locals memory cache flag lower upper tree temps after accepted ->
  double_tree_cache_distinct (double_source_tree_headers tree) cache ->
  (forall header, In header (double_source_tree_headers tree) -> cache header<>flag) -> accepted=true ->
  double_tree_active_profile tree (double_tree_cached_value cache after) lower upper.
Proof.
  intros RECEIPT DISTINCT FRESH ACCEPT header MEMBER.
  pose proof (@double_tree_accepted_cached_values ge locals memory cache flag lower upper tree temps after accepted
    RECEIPT DISTINCT FRESH ACCEPT) as AGREE.
  rewrite (double_tree_active_headers_agree AGREE) in MEMBER.
  rewrite (AGREE header MEMBER); exact (@double_tree_capture_accepted_profile ge locals memory cache flag lower upper
    tree temps after accepted RECEIPT ACCEPT header MEMBER).
Qed.

Print Assumptions double_tree_capture_accepted_profile.
Print Assumptions double_tree_capture_cached_profile.
