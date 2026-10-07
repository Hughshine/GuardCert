From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST.
From Guard Require Import ClightTempFrame ClightTempFootprint ClightPureExpr.
From GuardAffineNest Require Import AffineNestSyntax AffineNestGuardPackage AffineNestStaticPackage.
From GuardInterface Require Import ClightNestedConstantSite ClightLoadedBoundSyntax ClightLoadedOffsetHeader
  ClightSignedIndexedOffsetHeader.
Import ListNotations.
Set Implicit Arguments.

Section FACTS.
Variables source : compcert.cfrontend.Clight.statement.
Variables parameters live : list ident.
Variable proposal : affine_guard_proposal.
Variable shape : nested_constant_shape.
Variable site : nested_constant_site source parameters live proposal shape.

Lemma ncs_site_root_ids : affine_proposed_iterator proposal=ncs_row shape /\ affine_proposed_bound proposal=ncs_root_cache shape.
Proof.
  pose proof(ncs_model_exact site) as EXACT.
  unfold affine_proposal_nest,ncs_nest,ClightNestedConstantModel.nested_constant_model_nest in EXACT.
  inversion EXACT; auto.
Qed.

Lemma ncs_site_cache_helpers : forall cache helper,
  In cache(ncs_caches shape) -> In helper(ncs_helpers shape) -> cache<>helper.
Proof.
  intros cache helper CACHE HELPER; pose proof(ncs_original_unique site) as FRESH.
  cbn [ncs_names ncs_coordinates ncs_caches ncs_helpers app] in FRESH.
  repeat match goal with
  | H : NoDup(_::_) |- _ => apply NoDup_cons_iff in H as [? H]
  end.
  cbn [ncs_caches ncs_helpers List.In] in CACHE,HELPER.
  cbn [ncs_helpers List.In] in *; intuition congruence.
Qed.

Lemma ncs_site_caches_distinct : ncs_root_cache shape<>ncs_child_cache shape.
Proof.
  pose proof(ncs_original_unique site) as FRESH.
  cbn [ncs_names ncs_coordinates ncs_caches ncs_helpers app] in FRESH.
  repeat match goal with
  | H : NoDup(_::_) |- _ => apply NoDup_cons_iff in H as [? H]
  end.
  cbn [List.In] in *; intuition congruence.
Qed.

Lemma ncs_site_capture_private : forall cache,In cache(ncs_caches shape) ->
  ~In cache(statement_temps(ncs_original shape)++ncs_package_live source live shape).
Proof.
  intros cache MEMBER; rewrite <-(ncs_exact site); unfold ncs_package_live.
  repeat rewrite in_app_iff; intros [SOURCE|[SCOPE|HELPER]].
  - apply(ncs_cache_private site MEMBER); unfold ncs_scope; apply in_or_app; left; exact SOURCE.
  - apply(ncs_cache_private site MEMBER); exact SCOPE.
  - exact(ncs_site_cache_helpers MEMBER HELPER eq_refl).
Qed.

Lemma ncs_site_parameters_coordinates : forall identifier,In identifier parameters -> ~In identifier(ncs_coordinates shape).
Proof.
  pose proof(described_affine_parameters_fresh(affine_package_description(ncs_package site))) as FRESH.
  rewrite(affine_package_nest(ncs_package site)),(ncs_model_exact site) in FRESH.
  intros identifier MEMBER BAD; apply(FRESH identifier MEMBER).
  unfold ncs_nest,ncs_coordinates in *.
  cbn [ClightNestedConstantModel.nested_constant_model_nest affine_nest_iterators affine_nest_bounds app tl List.In] in *.
  tauto.
Qed.

Lemma ncs_site_stable_member identifier :
  In identifier(ncs_stable source parameters live shape) <->
  In identifier(ncs_ports source parameters live shape) /\ ~In identifier(ncs_coordinates shape).
Proof.
  unfold ncs_stable; rewrite filter_In; split.
  - intros [MEMBER PRIVATE]; split; [exact MEMBER|].
    apply affine_ident_private_check_sound; apply negb_true_iff; exact PRIVATE.
  - intros [MEMBER PRIVATE]; split; [exact MEMBER|].
    destruct(affine_ident_member_check identifier(ncs_coordinates shape)) eqn:CHECK; [|reflexivity].
    exfalso; apply PRIVATE,affine_ident_member_check_sound; exact CHECK.
Qed.

Lemma ncs_site_parameters_stable : incl parameters(ncs_stable source parameters live shape).
Proof.
  intros identifier MEMBER; apply ncs_site_stable_member; split.
  - unfold ncs_ports; apply in_or_app; left; exact MEMBER.
  - apply ncs_site_parameters_coordinates; exact MEMBER.
Qed.

Lemma ncs_site_pointer_stable : incl(ncs_pointer shape::affine_proposed_pointers proposal)
  (ncs_stable source parameters live shape).
Proof.
  intros identifier MEMBER; apply ncs_site_stable_member; split.
  - unfold ncs_ports,ncs_package_live; apply in_or_app; right; apply in_or_app; right.
    apply in_or_app; left; apply(ncs_pointer_scope site); exact MEMBER.
  - apply(ncs_pointer_coordinates site); exact MEMBER.
Qed.

Lemma ncs_site_caches_stable : incl(ncs_caches shape)(ncs_stable source parameters live shape).
Proof. intros identifier MEMBER; apply ncs_site_parameters_stable,(ncs_cache_parameters site); exact MEMBER. Qed.

Lemma ncs_site_header_scopes :
  expression_scope(ncs_scope source live)(signed_load_offset(ncs_pointer shape)(ncs_delta shape)) /\
  expression_scope(ncs_scope source live)(signed_indexed_offset(ncs_pointer shape)(ncs_index shape)(ncs_child_delta shape)).
Proof.
  split; unfold expression_scope; intros identifier MEMBER;
    cbn [signed_load_offset signed_load signed_pointer_temp signed_indexed_offset signed_indexed_load
      signed_indexed_pointer expression_temps app List.In] in MEMBER;
    destruct MEMBER as [SAME|[]]; subst identifier; apply(ncs_pointer_scope site); left; reflexivity.
Qed.

End FACTS.

Print Assumptions ncs_site_root_ids.
Print Assumptions ncs_site_cache_helpers.
Print Assumptions ncs_site_caches_distinct.
Print Assumptions ncs_site_capture_private.
Print Assumptions ncs_site_parameters_coordinates.
Print Assumptions ncs_site_stable_member.
Print Assumptions ncs_site_parameters_stable.
Print Assumptions ncs_site_pointer_stable.
Print Assumptions ncs_site_caches_stable.
Print Assumptions ncs_site_header_scopes.
