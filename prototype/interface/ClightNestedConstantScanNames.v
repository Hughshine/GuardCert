From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestGuardPackage AffineNestScanNamespace.
From GuardInterface Require Import ClightNestedConstantSite ClightNestedConstantSiteFacts ClightNestedConstantModel.
Import ListNotations.
Set Implicit Arguments.

Definition ncs_scan_controls proposal := affine_proposal_rename proposal.
Definition ncs_scan_values shape proposal := affine_scan_values(ncs_nest shape)(ncs_scan_controls proposal).
Definition ncs_outer_controls shape proposal :=
  [ncs_scan_controls proposal(ncs_row shape);ncs_scan_controls proposal(ncs_root_cache shape);
   ncs_scan_controls proposal(ncs_column shape);ncs_scan_controls proposal(ncs_child_helper shape)].

Section NAMES.
Variables source : compcert.cfrontend.Clight.statement.
Variables parameters live : list ident.
Variable proposal : affine_guard_proposal.
Variable shape : nested_constant_shape.
Variable site : nested_constant_site source parameters live proposal shape.

Lemma ncs_scan_control_private identifier : In identifier(affine_nest_controls(ncs_nest shape)) ->
  ~In(ncs_scan_controls proposal identifier)(ncs_ports source parameters live shape) /\
  ncs_scan_controls proposal identifier<>affine_proposed_result proposal.
Proof.
  intro MEMBER; destruct(affine_scan_names_private(ncs_scan_names site) identifier MEMBER) as [PRIVATE FLAG]; split; [|exact FLAG].
  intro BAD; apply PRIVATE,in_or_app; right; exact BAD.
Qed.

Lemma ncs_scan_outer_unique : NoDup(ncs_outer_controls shape proposal).
Proof.
  pose proof(affine_scan_names_unique(ncs_scan_names site)) as FRESH.
  change(NoDup[ncs_scan_controls proposal(ncs_row shape);ncs_scan_controls proposal(ncs_root_cache shape);
    ncs_scan_controls proposal(ncs_column shape);ncs_scan_controls proposal(ncs_child_helper shape);
    ncs_scan_controls proposal(ncs_iterator shape);ncs_scan_controls proposal(ncs_component_helper shape)]) in FRESH.
  repeat match goal with H : NoDup(_::_) |- _ => apply NoDup_cons_iff in H as [? H] end.
  unfold ncs_outer_controls; repeat constructor; cbn [List.In] in *; intuition congruence.
Qed.

Lemma ncs_scan_component_unique : NoDup(map(ncs_scan_controls proposal)(affine_nest_controls(ncs_component shape))).
Proof.
  pose proof(affine_scan_names_unique(ncs_scan_names site)) as FRESH.
  change(NoDup[ncs_scan_controls proposal(ncs_row shape);ncs_scan_controls proposal(ncs_root_cache shape);
    ncs_scan_controls proposal(ncs_column shape);ncs_scan_controls proposal(ncs_child_helper shape);
    ncs_scan_controls proposal(ncs_iterator shape);ncs_scan_controls proposal(ncs_component_helper shape)]) in FRESH.
  do 4 apply NoDup_cons_iff in FRESH as [_ FRESH]; exact FRESH.
Qed.

Lemma ncs_scan_component_private identifier : In identifier(affine_nest_controls(ncs_component shape)) ->
  ~In(ncs_scan_controls proposal identifier)(ncs_outer_controls shape proposal++ncs_ports source parameters live shape) /\
  ncs_scan_controls proposal identifier<>affine_proposed_result proposal.
Proof.
  intro MEMBER.
  assert(FULL : In identifier(affine_nest_controls(ncs_nest shape))).
  { change(In identifier[ncs_iterator shape;ncs_component_helper shape]) in MEMBER.
    change(In identifier[ncs_row shape;ncs_root_cache shape;ncs_column shape;ncs_child_helper shape;
      ncs_iterator shape;ncs_component_helper shape]); right; right; right; right; exact MEMBER. }
  destruct(ncs_scan_control_private FULL) as [PRIVATE FLAG]; split; [|exact FLAG].
  intro BAD; apply in_app_iff in BAD as [OUTER|PORT]; [|exact(PRIVATE PORT)].
  pose proof(affine_scan_names_unique(ncs_scan_names site)) as FRESH.
  change(NoDup[ncs_scan_controls proposal(ncs_row shape);ncs_scan_controls proposal(ncs_root_cache shape);
    ncs_scan_controls proposal(ncs_column shape);ncs_scan_controls proposal(ncs_child_helper shape);
    ncs_scan_controls proposal(ncs_iterator shape);ncs_scan_controls proposal(ncs_component_helper shape)]) in FRESH.
  repeat match goal with H : NoDup(_::_) |- _ => apply NoDup_cons_iff in H as [? H] end.
  change(In identifier[ncs_iterator shape;ncs_component_helper shape]) in MEMBER.
  unfold ncs_outer_controls in OUTER; cbn [List.In] in *; intuition congruence.
Qed.

Lemma ncs_scan_outer_private identifier : In identifier(ncs_outer_controls shape proposal) ->
  ~In identifier(ncs_ports source parameters live shape) /\ identifier<>affine_proposed_result proposal.
Proof.
  unfold ncs_outer_controls; cbn [List.In]; intros [SAME|[SAME|[SAME|[SAME|[]]]]]; subst identifier.
  - apply(ncs_scan_control_private(identifier:=ncs_row shape)); change(In (ncs_row shape) [ncs_row shape;ncs_root_cache shape;
      ncs_column shape;ncs_child_helper shape;ncs_iterator shape;ncs_component_helper shape]); cbn [List.In]; tauto.
  - apply(ncs_scan_control_private(identifier:=ncs_root_cache shape)); change(In (ncs_root_cache shape) [ncs_row shape;ncs_root_cache shape;
      ncs_column shape;ncs_child_helper shape;ncs_iterator shape;ncs_component_helper shape]); cbn [List.In]; tauto.
  - apply(ncs_scan_control_private(identifier:=ncs_column shape)); change(In (ncs_column shape) [ncs_row shape;ncs_root_cache shape;
      ncs_column shape;ncs_child_helper shape;ncs_iterator shape;ncs_component_helper shape]); cbn [List.In]; tauto.
  - apply(ncs_scan_control_private(identifier:=ncs_child_helper shape)); change(In (ncs_child_helper shape) [ncs_row shape;ncs_root_cache shape;
      ncs_column shape;ncs_child_helper shape;ncs_iterator shape;ncs_component_helper shape]); cbn [List.In]; tauto.
Qed.

Lemma ncs_scan_flag_private : ~In(affine_proposed_result proposal)
  (ncs_outer_controls shape proposal++ncs_ports source parameters live shape).
Proof.
  intro BAD; apply in_app_iff in BAD as [OUTER|PORT].
  - exact(proj2(ncs_scan_outer_private OUTER) eq_refl).
  - apply(affine_scan_names_flag_private(ncs_scan_names site)),in_or_app; right; exact PORT.
Qed.

Lemma ncs_scan_value_iterator identifier : In identifier(ncs_coordinates shape) ->
  ncs_scan_values shape proposal identifier=ncs_scan_controls proposal identifier.
Proof.
  intro MEMBER; apply affine_scan_values_iterator; change(In identifier(ncs_coordinates shape)); exact MEMBER.
Qed.

Lemma ncs_scan_value_parameter identifier : In identifier parameters -> ncs_scan_values shape proposal identifier=identifier.
Proof. intro MEMBER; exact(affine_scan_names_parameters(ncs_scan_names site) identifier MEMBER). Qed.

Lemma ncs_scan_flag_word : ~In(affine_proposed_result proposal)
  (map(ncs_scan_values shape proposal)(ncs_coordinates shape++parameters)).
Proof.
  intro BAD; apply in_map_iff in BAD as [identifier [SAME MEMBER]].
  apply in_app_iff in MEMBER as [COORDINATE|PARAMETER].
  - rewrite(ncs_scan_value_iterator COORDINATE) in SAME.
    assert(FULL : In identifier(affine_nest_controls(ncs_nest shape))).
    { apply affine_nest_controls_member; left; change(In identifier(ncs_coordinates shape)); exact COORDINATE. }
    exact(proj2(ncs_scan_control_private FULL) SAME).
  - rewrite(ncs_scan_value_parameter identifier PARAMETER) in SAME; subst identifier.
    apply(affine_scan_names_flag_private(ncs_scan_names site)),in_or_app; left; exact PARAMETER.
Qed.
End NAMES.

Print Assumptions ncs_scan_control_private.
Print Assumptions ncs_scan_outer_unique.
Print Assumptions ncs_scan_component_unique.
Print Assumptions ncs_scan_component_private.
Print Assumptions ncs_scan_outer_private.
Print Assumptions ncs_scan_flag_private.
Print Assumptions ncs_scan_value_iterator.
Print Assumptions ncs_scan_value_parameter.
Print Assumptions ncs_scan_flag_word.
