From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightNoWrap ClightTempFootprint
  ClightRectangularGuard ClightRedundantSet.
From GuardAffineNest Require Import AffineNestGuardPackage AffineNestMathDomain AffineNestExit.
From GuardInterface Require Import ClightNestedConstantSite ClightNestedConstantSiteFacts
  ClightNestedConstantHeaders ClightNestedConstantSiteNumeric ClightNestedConstantNumericInputs
  ClightNestedConstantFirstLeaf ClightNestedConstantNumericGuard ClightNestedConstantModel
  ClightConstantBoundModel ClightNestedExpressionCapture ClightExpressionBodyPrefix
  ClightLoadedOffsetHeader ClightSignedIndexedOffsetHeader ClightObservedHeaderPrefix ClightAffineJointObservation.
Import ListNotations.
Set Implicit Arguments.

Definition ncs_prepare_code shape := prepare_model_bounds(ncs_child_cache shape)
  (ncs_child_helper shape)(ncs_component_helper shape)(Int.repr(ncs_upper shape)).
Definition ncs_prepared_temps shape temps := prepared_model_temps temps(ncs_child_helper shape)
  (ncs_component_helper shape)(temp_word(ncs_child_cache shape) temps)(Int.repr(ncs_upper shape)).

Section PREPARE.
Variables source : statement.
Variables parameters live : list ident.
Variable proposal : affine_guard_proposal.
Variable shape : nested_constant_shape.
Variable site : nested_constant_site source parameters live proposal shape.

Lemma ncs_site_helpers_distinct : ncs_child_helper shape<>ncs_component_helper shape.
Proof.
  pose proof(ncs_original_unique site) as FRESH.
  cbv [ncs_names ncs_coordinates ncs_caches ncs_helpers app] in FRESH.
  repeat match goal with H : NoDup(_::_) |- _ => apply NoDup_cons_iff in H as [? H] end.
  cbn [List.In] in *; intuition congruence.
Qed.

Lemma ncs_site_row_child_distinct : ncs_row shape<>ncs_child_cache shape.
Proof.
  pose proof(ncs_original_unique site) as FRESH.
  cbv [ncs_names ncs_coordinates ncs_caches ncs_helpers app] in FRESH.
  repeat match goal with H : NoDup(_::_) |- _ => apply NoDup_cons_iff in H as [? H] end.
  cbn [List.In] in *; intuition congruence.
Qed.

Lemma ncs_site_helper_source_private helper : In helper(ncs_helpers shape) ->
  ~In helper(ncs_scope source live).
Proof.
  intros MEMBER BAD; apply(ncs_helper_private site MEMBER); apply in_or_app; left; exact BAD.
Qed.

Lemma ncs_site_helper_numeric_private helper : In helper(ncs_helpers shape) ->
  ~In helper(parameters++[ncs_row shape;ncs_root_cache shape]).
Proof.
  intros MEMBER BAD; apply in_app_iff in BAD as [PARAMETER|CONTROL].
  - apply(ncs_helper_private site MEMBER); apply in_or_app; right; exact PARAMETER.
  - cbn [List.In] in CONTROL; destruct CONTROL as [ROW|[CACHE|[]]].
    + subst helper; apply(ncs_site_helper_source_private MEMBER).
      unfold ncs_scope; rewrite(ncs_exact site); apply in_or_app; left; apply nested_constant_row_scope.
    + subst helper; apply(ncs_helper_private site MEMBER); apply in_or_app; right.
      apply(ncs_cache_parameters site); left; reflexivity.
Qed.

Lemma ncs_preparation_frames temps :
  temp_agree(ncs_scope source live) temps(ncs_prepared_temps shape temps) /\
  temp_agree(parameters++[ncs_row shape;ncs_root_cache shape]) temps(ncs_prepared_temps shape temps).
Proof.
  split; apply model_bounds_prepare_frame.
  - apply ncs_site_helper_source_private; left; reflexivity.
  - apply ncs_site_helper_source_private; right; left; reflexivity.
  - apply ncs_site_helper_numeric_private; left; reflexivity.
  - apply ncs_site_helper_numeric_private; right; left; reflexivity.
Qed.

(** This receipt describes the new, actual scan entry after the two emitted
    helper assignments. It does not claim that numeric code wrote those helpers.
    Every field is produced from an accepted numeric execution receipt below. *)
Record ncs_prepared_receipt fe ge locals checked memory checked_source_after final : Prop := NCSPreparedReceipt {
  ncs_prepare_run : exec_stmt fe ge locals checked memory(ncs_prepare_code shape)
    E0(ncs_prepared_temps shape checked) memory Out_normal;
  ncs_prepare_public : temp_agree(ncs_scope source live) checked(ncs_prepared_temps shape checked);
  ncs_prepare_numeric_frame : temp_agree(parameters++[ncs_row shape;ncs_root_cache shape])
    checked(ncs_prepared_temps shape checked);
  ncs_prepare_source : exists after,
    exec_stmt fe ge locals(ncs_prepared_temps shape checked) memory source E0 after final Out_normal /\
    temp_agree(ncs_scope source live) checked_source_after after /\
    after!(ncs_child_helper shape)=Some(Vint(temp_word(ncs_child_cache shape) checked)) /\
    after!(ncs_component_helper shape)=Some(Vint(Int.repr(ncs_upper shape)));
  ncs_prepare_row : (ncs_prepared_temps shape checked)!(ncs_row shape)=Some(Vint Int.zero);
  ncs_prepare_child : (ncs_prepared_temps shape checked)!(ncs_child_helper shape)=
    Some(Vint(temp_word(ncs_child_cache shape)(ncs_prepared_temps shape checked)));
  ncs_prepare_component : (ncs_prepared_temps shape checked)!(ncs_component_helper shape)=Some(Vint(Int.repr(ncs_upper shape)));
  ncs_prepare_accept : ncs_numeric_flag parameters proposal shape(Entry ge locals(ncs_prepared_temps shape checked) memory)=true;
  ncs_prepare_domains : Forall(fun identifier=>register_domain identifier(Entry ge locals(ncs_prepared_temps shape checked) memory)) parameters;
  ncs_prepare_math : affine_math_domain(affine_proposed_leaf_bounds proposal)(affine_proposal_layout proposal parameters)
    (affine_proposal_nest proposal)(affine_word_valuation(ncs_prepared_temps shape checked)) 0;
  ncs_prepare_scan_inputs : nested_constant_scan_inputs(ncs_row shape)(ncs_root_cache shape)(ncs_column shape)
    (ncs_child_cache shape)(ncs_iterator shape)(ncs_component_helper shape)(ncs_upper shape)(ncs_leaf shape)
    parameters(affine_proposed_leaf_bounds proposal)(Entry ge locals(ncs_prepared_temps shape checked) memory);
  ncs_prepare_observers : exists block offset raw child_raw,
    ncs_observation_receipt shape(Entry ge locals(ncs_prepared_temps shape checked) memory)(ncs_observers shape block offset raw child_raw)
}.

Theorem ncs_accepted_numeric_prepare fe ge locals original memory original_after final checked
  (receipt:ncs_numeric_receipt site fe ge locals original memory original_after final checked) :
  ncs_numeric_flag parameters proposal shape(Entry ge locals checked memory)=true ->
  exists checked_source_after,
    temp_agree(ncs_scope source live) original_after checked_source_after /\
    ncs_prepared_receipt fe ge locals checked memory checked_source_after final.
Proof.
  intro ACCEPT.
  destruct(ncs_preparation_frames checked) as [PUBLIC NUMERIC].
  assert(CURRENT_ACCEPT : ncs_numeric_flag parameters proposal shape(Entry ge locals(ncs_prepared_temps shape checked) memory)=true).
  { rewrite(@ncs_numeric_flag_frame _ _ _ _ _ site ge locals memory checked(ncs_prepared_temps shape checked) NUMERIC); exact ACCEPT. }
  assert(ROW : (ncs_prepared_temps shape checked)!(ncs_row shape)=Some(Vint Int.zero)).
  { rewrite NUMERIC by(apply in_or_app; right; left; reflexivity); exact(ncs_numeric_row receipt). }
  destruct(ncs_numeric_domain receipt ACCEPT) as [DEFINED [DOMAIN INPUTS]].
  assert(CURRENT_DEFINED : Forall(fun identifier=>register_domain identifier(Entry ge locals(ncs_prepared_temps shape checked) memory)) parameters).
  { rewrite Forall_forall in *; intros identifier MEMBER.
    destruct(DEFINED identifier MEMBER) as [word WORD]; exists word; cbn [entry_temps].
    rewrite NUMERIC by(apply in_or_app; left; exact MEMBER); exact WORD. }
  pose proof(ncs_numeric_flag_domain site(Entry ge locals(ncs_prepared_temps shape checked) memory) ROW CURRENT_ACCEPT) as CURRENT_DOMAIN.
  assert(CURRENT_INPUTS : nested_constant_scan_inputs(ncs_row shape)(ncs_root_cache shape)(ncs_column shape)
    (ncs_child_cache shape)(ncs_iterator shape)(ncs_component_helper shape)(ncs_upper shape)(ncs_leaf shape)
    parameters(affine_proposed_leaf_bounds proposal)(Entry ge locals(ncs_prepared_temps shape checked) memory)).
  { eapply nested_constant_package_scan_inputs with(child_helper:=ncs_child_helper shape)(package:=ncs_package site).
    - exact(ncs_model_exact site).
    - exact ncs_site_row_child_distinct.
    - exact CURRENT_DEFINED.
    - exact CURRENT_DOMAIN. }
  destruct(ncs_numeric_source receipt) as [after [SOURCE EXIT]].
  destruct(@model_bounds_prepare_source fe ge locals checked memory source after final live
    (ncs_child_helper shape)(ncs_component_helper shape)(temp_word(ncs_child_cache shape) checked)(Int.repr(ncs_upper shape))
    (ncs_frameable site) ncs_site_helpers_distinct
    (ncs_site_helper_source_private ltac:(left; reflexivity))
    (ncs_site_helper_source_private ltac:(right; left; reflexivity)) SOURCE)
    as [prepared_after [PREPARED [PREPARED_EXIT [CHILD_HELPER COMPONENT_HELPER]]]].
  destruct(ncs_numeric_observers receipt ACCEPT) as [block [offset [raw [child_raw HEADERS]]]].
  assert(POINTER_SCOPE : In(ncs_pointer shape)(ncs_scope source live)) by(apply(ncs_pointer_scope site); left; reflexivity).
  pose proof(@ncs_root_header_from_receipt shape(Entry ge locals checked memory) _ HEADERS
    (ncs_scope source live)(ncs_prepared_temps shape checked) memory POINTER_SCOPE PUBLIC(ncs_receipt_initial HEADERS)) as ROOT_EVAL.
  pose proof(@ncs_child_header_from_receipt shape(Entry ge locals checked memory) _ HEADERS
    (ncs_scope source live)(ncs_prepared_temps shape checked) memory POINTER_SCOPE PUBLIC(ncs_receipt_initial HEADERS)) as CHILD_EVAL.
  assert(ROOT_CACHE : (ncs_prepared_temps shape checked)!(ncs_root_cache shape)=Some(Vint(temp_word(ncs_root_cache shape) checked))).
  { rewrite NUMERIC by(apply in_or_app; left; apply(ncs_cache_parameters site); left; reflexivity).
    destruct(proj1(ncs_receipt_ready HEADERS)) as [b [o [r [P [READ WORD]]]]]; cbn [entry_temps] in WORD; unfold temp_word; rewrite WORD; reflexivity. }
  assert(CHILD_CACHE : (ncs_prepared_temps shape checked)!(ncs_child_cache shape)=Some(Vint(temp_word(ncs_child_cache shape) checked))).
  { rewrite NUMERIC by(apply in_or_app; left; apply(ncs_cache_parameters site); right; left; reflexivity).
    destruct(proj2(ncs_receipt_ready HEADERS)) as [b [o [r [P [READ WORD]]]]]; cbn [entry_temps] in WORD; unfold temp_word; rewrite WORD; reflexivity. }
  exists after; split; [exact EXIT|constructor].
  - apply model_bounds_prepare_execution; pose proof CHILD_CACHE as CACHE.
    rewrite NUMERIC in CACHE by(apply in_or_app; left; apply(ncs_cache_parameters site); right; left; reflexivity); exact CACHE.
  - exact PUBLIC.
  - exact NUMERIC.
  - exists prepared_after; repeat split; assumption.
  - exact ROW.
  - assert(SAME : temp_word(ncs_child_cache shape)(ncs_prepared_temps shape checked)=temp_word(ncs_child_cache shape) checked).
    { unfold temp_word; rewrite NUMERIC by(apply in_or_app; left; apply(ncs_cache_parameters site); right; left; reflexivity); reflexivity. }
    rewrite SAME; unfold ncs_prepared_temps,prepared_model_temps.
    rewrite PTree.gso by exact ncs_site_helpers_distinct; apply PTree.gss.
  - unfold ncs_prepared_temps,prepared_model_temps; apply PTree.gss.
  - exact CURRENT_ACCEPT.
  - exact CURRENT_DEFINED.
  - exact CURRENT_DOMAIN.
  - exact CURRENT_INPUTS.
  - eapply ncs_headers_from_actual_evaluations; eassumption.
Qed.

Theorem ncs_prepared_initial_prefix fe ge locals checked memory checked_source_after final
  (receipt:ncs_prepared_receipt fe ge locals checked memory checked_source_after final) :
  exists block offset raw child_raw,
    ncs_observation_receipt shape(Entry ge locals(ncs_prepared_temps shape checked) memory)(ncs_observers shape block offset raw child_raw) /\
    expression_body_prefix fe(ncs_row shape)(ncs_root_cache shape)
      (signed_load_offset(ncs_pointer shape)(ncs_delta shape))
      (nested_expression_body(ncs_column shape)(signed_indexed_offset(ncs_pointer shape)(ncs_index shape)(ncs_child_delta shape))
        (constant_body_source(ncs_iterator shape)(Int.repr(ncs_upper shape))(ncs_leaf shape)))
      (ncs_stable source parameters live shape)(ncs_header_ready shape)
      (fun _=>map word_observer_snapshot(ncs_observers shape block offset raw child_raw))
      0(Entry ge locals(ncs_prepared_temps shape checked) memory).
Proof.
  destruct(ncs_prepare_observers receipt) as [block [offset [raw [child_raw HEADERS]]]].
  destruct(ncs_prepare_source receipt) as [after [SOURCE REST]]; rewrite(ncs_exact site) in SOURCE.
  pose proof(ncs_prepare_accept receipt) as ACTIVE; unfold ncs_numeric_flag,nested_constant_numeric_flag in ACTIVE.
  destruct(register_positive(ncs_root_cache shape)(Entry ge locals(ncs_prepared_temps shape checked) memory)) eqn:ROOT; [|discriminate].
  exists block,offset,raw,child_raw; split; [exact HEADERS|].
  eapply expression_body_prefix_initial with(after:=after)(final:=final).
  - exact(ncs_receipt_ready HEADERS).
  - destruct(proj1(ncs_receipt_ready HEADERS)) as [b [o [r [P [READ WORD]]]]]; exists(Int.add r(ncs_delta shape)); exact WORD.
  - pose proof(@register_positive_sound(ncs_root_cache shape)(Entry ge locals(ncs_prepared_temps shape checked) memory) ROOT); lia.
  - exact(ncs_prepare_row receipt).
  - exact(ncs_receipt_initial HEADERS).
  - exact SOURCE.
Qed.
End PREPARE.

Print Assumptions ncs_site_helpers_distinct.
Print Assumptions ncs_site_row_child_distinct.
Print Assumptions ncs_site_helper_source_private.
Print Assumptions ncs_site_helper_numeric_private.
Print Assumptions ncs_preparation_frames.
Print Assumptions ncs_accepted_numeric_prepare.
Print Assumptions ncs_prepared_initial_prefix.
