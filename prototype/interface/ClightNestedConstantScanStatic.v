From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight Ctypes.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightRegionProgress
  ClightFrontendLoopProtocol ClightLoopSyntax ClightRectangularLoops ClightPureExpr ClightCountedLoop.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestSourceDecode AffineNestGuardPackage
  AffineNestLeafModel AffineNestStaticPackage.
From GuardInterface Require Import ClightNestedConstantSite ClightNestedConstantSiteFacts
  ClightNestedConstantHeaders ClightNestedConstantModel ClightConstantBoundModel
  ClightLoadedBoundSyntax ClightSignedIndexedOffsetHeader ClightAffineJointObservation ClightStrictLoopProgress.
Import ListNotations.
Set Implicit Arguments.

Section STATIC.
Variables source : statement.
Variables parameters live : list ident.
Variable proposal : affine_guard_proposal.
Variable shape : nested_constant_shape.
Variable site : nested_constant_site source parameters live proposal shape.

Definition ncs_scan_leaf : affine_leaf_certificate(ncs_leaf shape)(affine_proposed_leaf_bounds proposal)
  (affine_proposed_window_lower proposal)(affine_proposed_window_upper proposal)
  (ncs_coordinates shape++parameters) [](affine_proposed_pointers proposal)(affine_proposed_operations proposal).
Proof.
  pose proof(affine_package_leaf(ncs_package site)) as LEAF.
  unfold affine_proposal_layout in LEAF; rewrite(ncs_model_exact site) in LEAF; exact LEAF.
Defined.

Lemma ncs_scan_coordinate_unique : NoDup(ncs_coordinates shape).
Proof.
  pose proof(ncs_original_unique site) as FRESH.
  cbv [ncs_names ncs_coordinates ncs_caches ncs_helpers app] in FRESH.
  repeat match goal with H : NoDup(_::_) |- _ => apply NoDup_cons_iff in H as [? H] end.
  unfold ncs_coordinates; repeat constructor; cbn [List.In] in *; intuition congruence.
Qed.

Lemma ncs_scan_component_shape : affine_nest_shapes(ncs_component shape) /\
  NoDup(affine_nest_controls(ncs_component shape)) /\
  affine_nest_bound_dependencies[ncs_row shape;ncs_column shape] parameters(ncs_component shape).
Proof.
  split; [repeat split|split].
  - pose proof(ncs_original_unique site) as FRESH.
    cbv [ncs_names ncs_coordinates ncs_caches ncs_helpers app] in FRESH.
    repeat match goal with H : NoDup(_::_) |- _ => apply NoDup_cons_iff in H as [? H] end.
    change(NoDup[ncs_iterator shape;ncs_component_helper shape]); repeat constructor;
      cbn [List.In] in *; intuition congruence.
  - split; [intros identifier MEMBER; contradiction|exact I].
Qed.

Lemma ncs_scan_coordinate_not_stable identifier : In identifier(ncs_coordinates shape) ->
  ~In identifier(ncs_stable source parameters live shape).
Proof. intros COORDINATE MEMBER; exact(proj2(proj1(@ncs_site_stable_member source parameters live shape identifier) MEMBER) COORDINATE). Qed.

Lemma ncs_scan_helpers_stable : incl(ncs_helpers shape)(ncs_stable source parameters live shape).
Proof.
  intros identifier MEMBER; apply(@ncs_site_stable_member source parameters live shape); split.
  - unfold ncs_ports,ncs_package_live; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact MEMBER.
  - pose proof(ncs_original_unique site) as FRESH.
    cbv [ncs_names ncs_coordinates ncs_caches ncs_helpers app] in FRESH.
    repeat match goal with H : NoDup(_::_) |- _ => apply NoDup_cons_iff in H as [? H] end.
    unfold ncs_helpers in MEMBER; unfold ncs_coordinates; cbn [List.In] in *; intuition congruence.
Qed.

Lemma ncs_scan_component_protected identifier :
  In identifier(([ncs_row shape;ncs_column shape]++parameters)++affine_proposed_pointers proposal) ->
  ~In identifier(affine_nest_mutated(ncs_component shape)).
Proof.
  intro MEMBER; change(~In identifier[ncs_iterator shape]); cbn [List.In]; intros [SAME|[]]; subst identifier.
  apply in_app_iff in MEMBER as [PREFIX|POINTER]; [apply in_app_iff in PREFIX as [COORDINATE|PARAMETER]|].
  - pose proof(ncs_scan_coordinate_unique) as FRESH; unfold ncs_coordinates in FRESH.
    repeat match goal with H : NoDup(_::_) |- _ => apply NoDup_cons_iff in H as [? H] end.
    cbn [List.In] in *; intuition congruence.
  - apply(ncs_site_parameters_coordinates site PARAMETER); unfold ncs_coordinates; right; right; left; reflexivity.
  - apply(ncs_pointer_coordinates site ltac:(right; exact POINTER)); unfold ncs_coordinates; right; right; left; reflexivity.
Qed.

Lemma ncs_scan_word_scope : incl([ncs_row shape;ncs_column shape]++parameters)
  (ncs_column shape::ncs_row shape::ncs_stable source parameters live shape).
Proof.
  intros identifier MEMBER; apply in_app_iff in MEMBER as [COORDINATE|PARAMETER].
  - cbn [List.In] in *; tauto.
  - right; right; apply(ncs_site_parameters_stable site); exact PARAMETER.
Qed.

Lemma ncs_scan_stable_live : incl(ncs_stable source parameters live shape)(ncs_ports source parameters live shape).
Proof. intros identifier MEMBER; exact(proj1(proj1(@ncs_site_stable_member source parameters live shape identifier) MEMBER)). Qed.

Lemma ncs_scan_source_effects :
  normal_statement(constant_body_source(ncs_iterator shape)(Int.repr(ncs_upper shape))(ncs_leaf shape))=true /\
  quiet_statement(constant_body_source(ncs_iterator shape)(Int.repr(ncs_upper shape))(ncs_leaf shape))=true /\
  writes_only[ncs_iterator shape](constant_body_source(ncs_iterator shape)(Int.repr(ncs_upper shape))(ncs_leaf shape)).
Proof.
  pose proof(affine_leaf_quiet ncs_scan_leaf) as QUIET.
  pose proof(affine_leaf_writes ncs_scan_leaf) as WRITES.
  unfold constant_body_source,strict_frontend_loop,rectangle_reset,counter_increment; split; [|split].
  - cbn [normal_statement quiet_statement]; rewrite QUIET; reflexivity.
  - cbn [quiet_statement]; rewrite QUIET; reflexivity.
  - apply writes_sequence; [apply writes_set; cbn; auto|].
    apply writes_loop.
    + apply writes_sequence; [repeat constructor|].
      eapply writes_only_weaken; [|exact WRITES]; cbn; tauto.
    + apply writes_sequence; [constructor|apply writes_set; cbn; auto].
Qed.

Lemma ncs_scan_observer_scope entry observers(receipt:ncs_observation_receipt shape entry observers) observer :
  In observer observers -> expression_scope(ncs_stable source parameters live shape)(word_observer_address observer).
Proof.
  intro MEMBER.
  assert(ADDRESS : In(word_observer_address observer)(map word_observer_address(ncs_observer_templates shape))).
  { rewrite <-(ncs_receipt_addresses receipt); apply in_map; exact MEMBER. }
  cbn [ncs_observer_templates map word_observer_address List.In] in ADDRESS.
  destruct ADDRESS as [SAME|[SAME|[]]]; rewrite <-SAME;
    unfold expression_scope; intros identifier TEMP;
    cbn [signed_pointer_temp signed_indexed_pointer expression_temps app List.In] in TEMP;
    destruct TEMP as [SAME_ID|[]]; subst identifier;
    apply(ncs_site_pointer_stable site); left; reflexivity.
Qed.

Lemma ncs_scan_model_unique : NoDup[ncs_row shape;ncs_column shape;ncs_iterator shape;
  ncs_child_cache shape;ncs_child_helper shape;ncs_component_helper shape].
Proof.
  exact(@NoDup_remove_1 ident[ncs_row shape;ncs_column shape;ncs_iterator shape]
    [ncs_child_cache shape;ncs_child_helper shape;ncs_component_helper shape](ncs_root_cache shape)(ncs_original_unique site)).
Qed.

Lemma ncs_scan_model_pointer_private identifier : In identifier(affine_proposed_pointers proposal) ->
  ~In identifier(affine_nest_mutated(ncs_nest shape)).
Proof.
  intros MEMBER BAD.
  change(In identifier[ncs_row shape;ncs_column shape;ncs_child_helper shape;
    ncs_iterator shape;ncs_component_helper shape]) in BAD.
  cbn [List.In] in BAD; destruct BAD as [SAME|[SAME|[SAME|[SAME|[SAME|[]]]]]]; subst identifier.
  - apply(ncs_pointer_coordinates site ltac:(right; exact MEMBER)); unfold ncs_coordinates; cbn [List.In]; tauto.
  - apply(ncs_pointer_coordinates site ltac:(right; exact MEMBER)); unfold ncs_coordinates; cbn [List.In]; tauto.
  - apply(ncs_helper_private site ltac:(left; reflexivity)); apply in_or_app; left; apply(ncs_pointer_scope site); right; exact MEMBER.
  - apply(ncs_pointer_coordinates site ltac:(right; exact MEMBER)); unfold ncs_coordinates; cbn [List.In]; tauto.
  - apply(ncs_helper_private site ltac:(right; left; reflexivity)); apply in_or_app; left; apply(ncs_pointer_scope site); right; exact MEMBER.
Qed.
End STATIC.

Print Assumptions ncs_scan_leaf.
Print Assumptions ncs_scan_coordinate_unique.
Print Assumptions ncs_scan_component_shape.
Print Assumptions ncs_scan_coordinate_not_stable.
Print Assumptions ncs_scan_helpers_stable.
Print Assumptions ncs_scan_component_protected.
Print Assumptions ncs_scan_word_scope.
Print Assumptions ncs_scan_stable_live.
Print Assumptions ncs_scan_source_effects.
Print Assumptions ncs_scan_observer_scope.
Print Assumptions ncs_scan_model_unique.
Print Assumptions ncs_scan_model_pointer_private.
