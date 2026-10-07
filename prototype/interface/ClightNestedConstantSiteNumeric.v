From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightPureExpr ClightNoWrap
  ClightRedundantSet ClightRectangularGuard ClightRegionProgress ClightProjectedExecution.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestLeafModel AffineNestGuardPackage
  AffineNestPackageGuard AffineNestGuardFactTransport AffineNestAcceptedDomain AffineNestGuardParameterCheck
  AffineNestGuardDomain AffineNestMathDomain.
From GuardInterface Require Import ClightNestedConstantSite ClightNestedConstantSiteFacts ClightNestedConstantHeaders
  ClightNestedConstantNumericGuard ClightNestedConstantNumericInputs ClightNestedConstantFirstLeaf ClightNestedConstantModel
  ClightNestedExpressionCapture ClightConstantBoundModel ClightLoadedBoundSyntax ClightLoadedOffsetHeader
  ClightSignedIndexedOffsetHeader ClightAffineNestMaterialized ClightCheckPlanFrame
  ClightExpressionBodyPrefix ClightAffineJointObservation ClightObservedHeaderPrefix.
Import ListNotations.
Set Implicit Arguments.

Definition ncs_numeric_code source parameters live proposal shape
  (site:nested_constant_site source parameters live proposal shape) :=
  Ssequence(nested_expression_capture(ncs_row shape)(ncs_root_cache shape)
    (signed_load_offset(ncs_pointer shape)(ncs_delta shape))(ncs_child_cache shape)
    (signed_indexed_offset(ncs_pointer shape)(ncs_index shape)(ncs_child_delta shape)))
    (nested_constant_numeric_code(ncs_root_cache shape)(ncs_child_cache shape)(affine_proposed_result proposal)
      (affine_package_guard_code(ncs_package site))).
Definition ncs_numeric_flag parameters proposal shape entry :=
  nested_constant_numeric_flag(ncs_root_cache shape)(ncs_child_cache shape) parameters proposal entry.

Section CLIENT.
Variables source : statement.
Variables parameters live : list ident.
Variable proposal : affine_guard_proposal.
Variable shape : nested_constant_shape.
Variable site : nested_constant_site source parameters live proposal shape.

Theorem ncs_numeric_flag_frame ge locals memory before after :
  temp_agree(parameters++[ncs_row shape;ncs_root_cache shape]) before after ->
  ncs_numeric_flag parameters proposal shape(Entry ge locals after memory)=
    ncs_numeric_flag parameters proposal shape(Entry ge locals before memory).
Proof.
  intro FRAME; destruct(ncs_site_root_ids site) as [ROW BOUND].
  assert(ROOT : after!(ncs_root_cache shape)=before!(ncs_root_cache shape)).
  { apply FRAME; apply in_or_app; left; apply(ncs_cache_parameters site); left; reflexivity. }
  assert(CHILD : after!(ncs_child_cache shape)=before!(ncs_child_cache shape)).
  { apply FRAME; apply in_or_app; left; apply(ncs_cache_parameters site); right; left; reflexivity. }
  unfold ncs_numeric_flag,nested_constant_numeric_flag,register_positive,temp_word; cbn [entry_temps].
  rewrite ROOT,CHILD; fold(temp_word(ncs_root_cache shape) before)(temp_word(ncs_child_cache shape) before).
  rewrite(@affine_package_guard_flag_frame _ _ _ _ (ncs_package site) ge locals memory before after).
  - reflexivity.
  - rewrite ROW,BOUND; exact FRAME.
Qed.

Theorem ncs_numeric_flag_domain entry :
  (entry_temps entry)!(ncs_row shape)=Some(Vint Int.zero) ->
  ncs_numeric_flag parameters proposal shape entry=true ->
  affine_math_domain(affine_proposed_leaf_bounds proposal)(affine_proposal_layout proposal parameters)
    (affine_proposal_nest proposal)(affine_word_valuation(entry_temps entry)) 0.
Proof.
  intros ROW ACCEPT; unfold ncs_numeric_flag,nested_constant_numeric_flag in ACCEPT.
  destruct(register_positive(ncs_root_cache shape) entry); [|discriminate].
  destruct(register_positive(ncs_child_cache shape) entry); [|discriminate].
  destruct(ncs_site_root_ids site) as [ITERATOR BOUND].
  replace 0%Z with(affine_word_valuation(entry_temps entry)(affine_proposed_iterator proposal)).
  - eapply affine_domain_guard_accepted.
    + exact(affine_package_profile(ncs_package site)).
    + exact(affine_package_parameter_intervals(ncs_package site)).
    + pose proof(@affine_nest_fresh_controls _ (described_affine_fresh(affine_package_description(ncs_package site)))) as UNIQUE.
      rewrite(affine_package_nest(ncs_package site)) in UNIQUE; exact UNIQUE.
    + intros identifier MEMBER; exact(proj2(@check_affine_guard_parameters_sound _ _ _ _ _
        (affine_package_used(ncs_package site)) identifier MEMBER)).
    + exact ACCEPT.
  - rewrite ITERATOR; unfold affine_word_valuation,temp_word; rewrite ROW,Int.signed_zero; reflexivity.
Qed.

Record ncs_numeric_receipt fe ge locals original memory original_after final checked : Prop := NCSNumericReceipt {
  ncs_numeric_run : exec_stmt fe ge locals original memory(ncs_numeric_code site) E0 checked memory Out_normal;
  ncs_numeric_public : temp_agree(ncs_scope source live) original checked;
  ncs_numeric_source : exists after,
    exec_stmt fe ge locals checked memory source E0 after final Out_normal /\
    temp_agree(ncs_scope source live) original_after after;
  ncs_numeric_row : checked!(ncs_row shape)=Some(Vint Int.zero);
  ncs_numeric_result : checked!(affine_proposed_result proposal)=
    Some(Vint(if ncs_numeric_flag parameters proposal shape(Entry ge locals checked memory) then Int.one else Int.zero));
  ncs_numeric_domain : ncs_numeric_flag parameters proposal shape(Entry ge locals checked memory)=true ->
    Forall(fun identifier=>register_domain identifier(Entry ge locals checked memory)) parameters /\
    affine_math_domain(affine_proposed_leaf_bounds proposal)(affine_proposal_layout proposal parameters)
      (affine_proposal_nest proposal)(affine_word_valuation checked) 0 /\
    nested_constant_scan_inputs(ncs_row shape)(ncs_root_cache shape)(ncs_column shape)(ncs_child_cache shape)
      (ncs_iterator shape)(ncs_component_helper shape)(ncs_upper shape)(ncs_leaf shape)
      parameters(affine_proposed_leaf_bounds proposal)(Entry ge locals checked memory);
  ncs_numeric_observers : ncs_numeric_flag parameters proposal shape(Entry ge locals checked memory)=true ->
    exists block offset raw child_raw,
      ncs_observation_receipt shape(Entry ge locals checked memory)(ncs_observers shape block offset raw child_raw)
}.

(** The checked site supplies every static obligation of the original
    capture/numeric services. All acceptance facts now name the actual exit
    of the emitted check, rather than an earlier hypothetical entry. *)
Theorem ncs_numeric_site_execution fe ge locals temps memory source_after final :
  temps!(ncs_row shape)=Some(Vint Int.zero) ->
  exec_stmt fe ge locals temps memory source E0 source_after final Out_normal ->
  exists checked,ncs_numeric_receipt fe ge locals temps memory source_after final checked.
Proof.
  intros ROW SOURCE.
  pose proof(ncs_exact site) as EXACT; pose proof(ncs_frameable site) as FRAMEABLE.
  rewrite EXACT in SOURCE,FRAMEABLE.
  pose proof(affine_leaf_quiet(affine_package_leaf(ncs_package site))) as QUIET.
  rewrite(ncs_model_exact site) in QUIET; change(quiet_statement(ncs_leaf shape)=true) in QUIET.
  assert(COLUMN_PRIVATE : ~In(ncs_column shape)(expression_temps
    (signed_indexed_offset(ncs_pointer shape)(ncs_index shape)(ncs_child_delta shape)))).
  { cbn [signed_indexed_offset signed_indexed_load signed_indexed_pointer signed_pointer_temp expression_temps app List.In].
    intros [SAME|[]]; apply(ncs_pointer_coordinates site (or_introl eq_refl)).
    unfold ncs_coordinates; right; left; symmetry; exact SAME. }
  destruct(@nested_expression_capture_execution fe ge locals temps memory(ncs_row shape)
    (signed_load_offset(ncs_pointer shape)(ncs_delta shape))(ncs_column shape)
    (signed_indexed_offset(ncs_pointer shape)(ncs_index shape)(ncs_child_delta shape))
    (constant_body_source(ncs_iterator shape)(Int.repr(ncs_upper shape))(ncs_leaf shape))
    (ncs_root_cache shape)(ncs_child_cache shape)(ncs_package_live source live shape) source_after final
    eq_refl eq_refl(@constant_literal_source_quiet _ _ _ QUIET) FRAMEABLE
    (ncs_site_capture_private site (or_introl eq_refl))
    (ncs_site_capture_private site (or_intror(or_introl eq_refl)))
    (ncs_site_caches_distinct site) COLUMN_PRIVATE SOURCE)
    as [root_word [child [prepared_after [CAPTURE [PREPARED_SOURCE [PUBLIC [ROOT CHILD]]]]]]].
  set(prepared:=nested_expression_captured(ncs_root_cache shape)(ncs_child_cache shape) temps root_word child).
  assert(FRAME : temp_agree(ncs_scope source live) temps prepared).
  { apply nested_expression_captured_frame;
      [exact(ncs_cache_private site (or_introl eq_refl))|
       exact(ncs_cache_private site (or_intror(or_introl eq_refl)))]. }
  assert(ROW_MEMBER : In(ncs_row shape)(ncs_scope source live)).
  { unfold ncs_scope; rewrite EXACT; apply in_or_app; left; apply nested_constant_row_scope. }
  assert(PREPARED_ROW : prepared!(ncs_row shape)=Some(Vint Int.zero)) by(rewrite FRAME by exact ROW_MEMBER; exact ROW).
  assert(ROOT_WORD : prepared!(ncs_root_cache shape)=Some(Vint root_word))
    by(apply nested_expression_captured_root; exact(ncs_site_caches_distinct site)).
  assert(ROOT_READ : eval_expr ge locals prepared memory(signed_load_offset(ncs_pointer shape)(ncs_delta shape))(Vint root_word)).
  { eapply expression_temp_transport; [exact(proj1(ncs_site_header_scopes site))|exact FRAME|exact ROOT]. }
  assert(CHILD_READ : register_positive(ncs_root_cache shape)(Entry ge locals prepared memory)=true -> exists child_word,
    prepared!(ncs_child_cache shape)=Some(Vint child_word) /\
    eval_expr ge locals prepared memory(signed_indexed_offset(ncs_pointer shape)(ncs_index shape)(ncs_child_delta shape))(Vint child_word)).
  { intro ACTIVE; destruct child as [child_word|].
    - destruct CHILD as [_ READ]; exists child_word; split; [apply nested_expression_captured_child|].
      eapply expression_temp_transport; [exact(proj2(ncs_site_header_scopes site))|exact FRAME|exact READ].
    - unfold register_positive,temp_word in ACTIVE,CHILD; cbn [entry_temps] in ACTIVE.
      rewrite ROOT_WORD in ACTIVE; rewrite ROW in CHILD; congruence. }
  destruct(@nested_constant_numeric_guard_execution(ncs_row shape)(ncs_root_cache shape)(ncs_column shape)(ncs_child_cache shape)
    (ncs_child_helper shape)(ncs_iterator shape)(ncs_component_helper shape)(ncs_upper shape)(ncs_leaf shape)
    parameters(ncs_package_live source live shape) proposal(ncs_package site) fe ge locals
    (signed_load_offset(ncs_pointer shape)(ncs_delta shape))
    (signed_indexed_offset(ncs_pointer shape)(ncs_index shape)(ncs_child_delta shape)) root_word prepared memory prepared_after final
    (ncs_model_exact site) eq_refl eq_refl COLUMN_PRIVATE PREPARED_ROW ROOT_WORD ROOT_READ CHILD_READ
    (ncs_literal_positive site) PREPARED_SOURCE) as [checked [NUMERIC [KEEP [RESULT SOUND]]]].
  destruct(ncs_site_root_ids site) as [ITERATOR BOUND].
  unfold affine_single_materialized_ports in KEEP; rewrite ITERATOR,BOUND in KEEP; fold(ncs_ports source parameters live shape) in KEEP.
  assert(SCOPE_PORTS : incl(ncs_scope source live)(ncs_ports source parameters live shape)).
  { unfold ncs_ports,ncs_package_live; intros identifier MEMBER; apply in_or_app; right; apply in_or_app; right;
      apply in_or_app; left; exact MEMBER. }
  assert(WHOLE_FRAME : temp_agree(ncs_scope source live) temps checked)
    by(eapply temp_agree_trans; [exact FRAME|eapply temp_agree_weaken; eassumption]).
  assert(FLAG_FRAME : ncs_numeric_flag parameters proposal shape(Entry ge locals checked memory)=
    ncs_numeric_flag parameters proposal shape(Entry ge locals prepared memory)).
  { apply ncs_numeric_flag_frame; eapply temp_agree_weaken; [|exact KEEP].
    unfold ncs_ports; intros identifier MEMBER; repeat rewrite in_app_iff in *; tauto. }
  assert(CHECKED_ROW : checked!(ncs_row shape)=Some(Vint Int.zero)) by(rewrite WHOLE_FRAME by exact ROW_MEMBER; exact ROW).
  exists checked; constructor.
  - unfold ncs_numeric_code; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); eassumption.
  - exact WHOLE_FRAME.
  - rewrite <-EXACT in SOURCE.
    eapply structured_execution_temp_transport with(live:=ncs_scope source live)(allowed:=statement_temps source).
    + exact SOURCE.
    + apply check_plan_frameable_writes; exact(ncs_frameable site).
    + unfold statement_scope,ncs_scope; intros identifier MEMBER; apply in_or_app; left; exact MEMBER.
    + exact WHOLE_FRAME.
  - exact CHECKED_ROW.
  - rewrite FLAG_FRAME; exact RESULT.
  - intro ACCEPT; pose proof ACCEPT as BEFORE; rewrite FLAG_FRAME in BEFORE.
    destruct(SOUND BEFORE) as [PARAMETERS DOMAIN].
    assert(CURRENT_PARAMETERS : Forall(fun identifier=>register_domain identifier(Entry ge locals checked memory)) parameters).
    { eapply affine_register_domains_transport; [exact PARAMETERS|eapply temp_agree_weaken; [|exact KEEP]].
      unfold ncs_ports; intros identifier MEMBER; apply in_or_app; left; exact MEMBER. }
    assert(CURRENT_DOMAIN : affine_math_domain(affine_proposed_leaf_bounds proposal)(affine_proposal_layout proposal parameters)
      (affine_proposal_nest proposal)(affine_word_valuation checked) 0)
      by exact(@ncs_numeric_flag_domain(Entry ge locals checked memory) CHECKED_ROW ACCEPT).
    split; [exact CURRENT_PARAMETERS|split; [exact CURRENT_DOMAIN|]].
    eapply nested_constant_package_scan_inputs with(package:=ncs_package site); [exact(ncs_model_exact site)| |exact CURRENT_PARAMETERS|exact CURRENT_DOMAIN].
    intro SAME; apply(ncs_site_parameters_coordinates site (ncs_cache_parameters site (or_intror(or_introl eq_refl)))).
    unfold ncs_coordinates; left; exact SAME.
  - intro ACCEPT; rewrite FLAG_FRAME in ACCEPT; unfold ncs_numeric_flag,nested_constant_numeric_flag in ACCEPT.
    destruct(register_positive(ncs_root_cache shape)(Entry ge locals prepared memory)) eqn:ACTIVE; [|discriminate].
    destruct(CHILD_READ eq_refl) as [child_word [CHILD_WORD CHILD_EVAL]].
    eapply ncs_headers_from_actual_evaluations with(root_word:=root_word)(child_word:=child_word).
    + rewrite KEEP; [exact ROOT_WORD|unfold ncs_ports; apply in_or_app; left; apply(ncs_cache_parameters site); left; reflexivity].
    + rewrite KEEP; [exact CHILD_WORD|unfold ncs_ports; apply in_or_app; left; apply(ncs_cache_parameters site); right; left; reflexivity].
    + eapply expression_temp_transport; [exact(proj1(ncs_site_header_scopes site))|eapply temp_agree_weaken; [exact SCOPE_PORTS|exact KEEP]|exact ROOT_READ].
    + eapply expression_temp_transport; [exact(proj2(ncs_site_header_scopes site))|eapply temp_agree_weaken; [exact SCOPE_PORTS|exact KEEP]|exact CHILD_EVAL].
Qed.

Theorem ncs_numeric_initial_prefix fe ge locals original memory original_after final checked
  (receipt:ncs_numeric_receipt fe ge locals original memory original_after final checked) :
  ncs_numeric_flag parameters proposal shape(Entry ge locals checked memory)=true ->
  exists block offset raw child_raw,
    ncs_observation_receipt shape(Entry ge locals checked memory)(ncs_observers shape block offset raw child_raw) /\
    expression_body_prefix fe(ncs_row shape)(ncs_root_cache shape)
      (signed_load_offset(ncs_pointer shape)(ncs_delta shape))
      (nested_expression_body(ncs_column shape)
        (signed_indexed_offset(ncs_pointer shape)(ncs_index shape)(ncs_child_delta shape))
        (constant_body_source(ncs_iterator shape)(Int.repr(ncs_upper shape))(ncs_leaf shape)))
      (ncs_stable source parameters live shape)(ncs_header_ready shape)
      (fun _=>map word_observer_snapshot(ncs_observers shape block offset raw child_raw)) 0(Entry ge locals checked memory).
Proof.
  intro ACCEPT; destruct(ncs_numeric_observers receipt ACCEPT) as [block [offset [raw [child_raw HEADERS]]]].
  destruct(ncs_numeric_source receipt) as [after [SOURCE PUBLIC]]; rewrite(ncs_exact site) in SOURCE.
  pose proof ACCEPT as ACTIVE; unfold ncs_numeric_flag,nested_constant_numeric_flag in ACTIVE.
  destruct(register_positive(ncs_root_cache shape)(Entry ge locals checked memory)) eqn:ROOT; [|discriminate].
  exists block,offset,raw,child_raw; split; [exact HEADERS|].
  eapply expression_body_prefix_initial with(after:=after)(final:=final).
  - exact(ncs_receipt_ready HEADERS).
  - destruct(proj1(ncs_receipt_ready HEADERS)) as [location [base [word [POINTER [READ CACHE]]]]].
    exists(Int.add word(ncs_delta shape)); exact CACHE.
  - pose proof(@register_positive_sound(ncs_root_cache shape)(Entry ge locals checked memory) ROOT); lia.
  - exact(ncs_numeric_row receipt).
  - exact(ncs_receipt_initial HEADERS).
  - exact SOURCE.
Qed.

End CLIENT.

Print Assumptions ncs_numeric_flag_frame.
Print Assumptions ncs_numeric_flag_domain.
Print Assumptions ncs_numeric_site_execution.
Print Assumptions ncs_numeric_initial_prefix.
