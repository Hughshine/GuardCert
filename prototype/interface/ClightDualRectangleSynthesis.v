From Stdlib Require Import ZArith.
From Guard Require Import ClightGuard ClightCondition ClightRectangularStore ClightRectangularGuard.
From GuardInterface Require Import GuardInterface GuardedRewrite ReadonlyConditionComposition ReadonlyBranching ReadonlyPrefixScan
  ClightReadonlyRewrite ClightConditionComposition ClightReadonlyBranching ClightDualRectangleInnerScan ClightDualRectangleOuterScan
  ClightDualRectangleGuard.
Set Implicit Arguments.

Lemma dual_rect_inner_syntax d VALID fe O (observe : fragment_observation -> O -> Prop)
  array row rows column columns body outer RC RN RM CN CM BODY fuel point i :
  synthesize_prefix_scan (clight_readonly_check_algebra fe observe) (clight_readonly_branch_algebra fe observe)
    (@dual_rect_inner_spec d VALID fe array row rows column columns body outer RC RN RM CN CM BODY O observe i) fuel point =
  synthesize_prefix_scan (clight_readonly_check_algebra (adapter_entry true) eq) (clight_readonly_branch_algebra (adapter_entry true) eq)
    (@dual_rect_inner_spec d VALID (adapter_entry true) array row rows column columns body outer RC RN RM CN CM BODY fragment_observation eq i) fuel point.
Proof.
  revert point; induction fuel as [|fuel IH]; intro point; cbn [synthesize_prefix_scan dual_rect_inner_spec
    prefix_next prefix_active_probe prefix_point_probe clight_readonly_check_algebra clight_readonly_branch_algebra constant_check branch_check].
  - reflexivity.
  - rewrite IH; reflexivity.
Qed.
Lemma dual_rect_outer_syntax d VALID fe O (observe : fragment_observation -> O -> Prop)
  array row rows column columns body outer RC RN RM CN CM BODY OUTER fuel point :
  synthesize_prefix_scan (clight_readonly_check_algebra fe observe) (clight_readonly_branch_algebra fe observe)
    (@dual_rect_outer_spec d VALID fe array row rows column columns body outer RC RN RM CN CM BODY OUTER O observe) fuel point =
  synthesize_prefix_scan (clight_readonly_check_algebra (adapter_entry true) eq) (clight_readonly_branch_algebra (adapter_entry true) eq)
    (@dual_rect_outer_spec d VALID (adapter_entry true) array row rows column columns body outer RC RN RM CN CM BODY OUTER fragment_observation eq) fuel point.
Proof.
  revert point; induction fuel as [|fuel IH]; intro point; cbn [synthesize_prefix_scan dual_rect_outer_spec
    prefix_next prefix_active_probe prefix_point_probe clight_readonly_check_algebra clight_readonly_branch_algebra constant_check branch_check].
  - reflexivity.
  - rewrite IH; unfold dual_rect_inner_tree.
    rewrite (@dual_rect_inner_syntax d VALID fe O observe array row rows column columns body outer RC RN RM CN CM BODY
      (Z.to_nat (rectangle_stride d)) 0 point); reflexivity.
Qed.
Definition dual_rect_generated_tree d VALID array row rows column columns body outer RC RN RM CN CM BODY OUTER :=
  @dual_rect_tree d VALID (adapter_entry true) fragment_observation eq array row rows column columns body outer RC RN RM CN CM BODY OUTER.
Definition dual_rect_generated_condition d (VALID : rectangle_layout_valid d) fe O (observe : fragment_observation -> O -> Prop)
  array row rows column columns body outer RC RN RM CN CM BODY OUTER :
  readonly_condition (readonly_clight_host fe observe) (dual_rect_domain row rows outer) (dual_rect_property d array row rows columns)
    (@dual_rect_generated_tree d VALID array row rows column columns body outer RC RN RM CN CM BODY OUTER).
Proof.
  unfold dual_rect_generated_tree,dual_rect_tree,dual_rect_outer_tree.
  rewrite <- (@dual_rect_outer_syntax d VALID fe O observe array row rows column columns body outer RC RN RM CN CM BODY OUTER).
  exact (@dual_rect_condition d VALID fe O observe array row rows column columns body outer RC RN RM CN CM BODY OUTER).
Defined.
Print Assumptions dual_rect_inner_syntax.
Print Assumptions dual_rect_outer_syntax.
Print Assumptions dual_rect_generated_condition.
