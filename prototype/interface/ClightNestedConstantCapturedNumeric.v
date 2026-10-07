From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightRedundantSet ClightTempFrame ClightTempFootprint
  ClightPureExpr ClightRegionProgress ClightProjectedExecution ClightRectangularGuard.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestLeafModel AffineNestGuardPackage
  AffineNestPackageGuard AffineNestMathDomain.
From GuardInterface Require Import ClightConstantBoundModel ClightNestedExpressionCapture ClightNestedConstantModel
  ClightNestedConstantFirstLeaf ClightNestedConstantNumericInputs ClightNestedConstantNumericGuard
  ClightAffineNestMaterialized ClightCheckPlanFrame.
Import ListNotations.
Set Implicit Arguments.

Definition nested_constant_captured_numeric_code row bound child_bound root_cache child_cache result numeric :=
  Ssequence(nested_expression_capture row root_cache bound child_cache child_bound)
    (nested_constant_numeric_code root_cache child_cache result numeric).

(** Original completion supplies ordered captures and an actual first leaf
    only on the active path. No caller supplies parameter domains, numeric
    execution, or a cached-source completion witness. *)
Theorem nested_constant_captured_numeric_execution row root_cache column child_cache child_helper iterator component_helper
  upper body parameters live proposal
  (package:affine_guard_package
    (nested_constant_model_source row root_cache column child_cache child_helper iterator component_helper upper body)
    parameters live proposal)
  fe ge locals bound child_bound temps memory source_after source_final :
  affine_proposal_nest proposal=nested_constant_model_nest row root_cache column child_cache child_helper
    iterator component_helper upper body(AffineSourceLeaf body) ->
  typeof bound=type_int32s -> typeof child_bound=type_int32s -> ~In column(expression_temps child_bound) ->
  temps!row=Some(Vint Int.zero) -> root_cache<>child_cache ->
  check_plan_frameable(nested_expression_source row bound column child_bound
    (constant_body_source iterator(Int.repr upper) body))=true ->
  ~In root_cache(statement_temps(nested_expression_source row bound column child_bound
    (constant_body_source iterator(Int.repr upper) body))++live) ->
  ~In child_cache(statement_temps(nested_expression_source row bound column child_bound
    (constant_body_source iterator(Int.repr upper) body))++live) ->
  Int.lt Int.zero(Int.repr upper)=true ->
  exec_stmt fe ge locals temps memory
    (nested_expression_source row bound column child_bound(constant_body_source iterator(Int.repr upper) body))
    E0 source_after source_final Out_normal ->
  exists root_word child prepared_after after,
    let prepared:=nested_expression_captured root_cache child_cache temps root_word child in
    exec_stmt fe ge locals temps memory
      (nested_constant_captured_numeric_code row bound child_bound root_cache child_cache
        (affine_proposed_result proposal)(affine_package_guard_code package)) E0 after memory Out_normal /\
    temp_agree live temps after /\
    exec_stmt fe ge locals prepared memory
      (nested_expression_source row bound column child_bound(constant_body_source iterator(Int.repr upper) body))
      E0 prepared_after source_final Out_normal /\
    temp_agree(statement_temps(nested_expression_source row bound column child_bound
      (constant_body_source iterator(Int.repr upper) body))++live) source_after prepared_after /\
    eval_expr ge locals prepared memory bound(Vint root_word) /\
    (register_positive root_cache(Entry ge locals prepared memory)=true -> exists child_word,
      prepared!child_cache=Some(Vint child_word) /\ eval_expr ge locals prepared memory child_bound(Vint child_word)) /\
    after!(affine_proposed_result proposal)=Some(Vint(if nested_constant_numeric_flag root_cache child_cache
      parameters proposal(Entry ge locals prepared memory) then Int.one else Int.zero)) /\
    (nested_constant_numeric_flag root_cache child_cache parameters proposal(Entry ge locals prepared memory)=true ->
      Forall(fun identifier=>register_domain identifier(Entry ge locals prepared memory)) parameters /\
      affine_math_domain(affine_proposed_leaf_bounds proposal)(affine_proposal_layout proposal parameters)
        (affine_proposal_nest proposal)(affine_word_valuation prepared) 0 /\
      nested_constant_scan_inputs row root_cache column child_cache iterator component_helper upper body
        parameters(affine_proposed_leaf_bounds proposal)(Entry ge locals prepared memory)).
Proof.
  intros NEST TYPE CHILD_TYPE COLUMN_PRIVATE ROW DISTINCT FRAMEABLE PRIVATE CHILD_PRIVATE LITERAL_ACTIVE SOURCE.
  pose proof(affine_leaf_quiet(affine_package_leaf package)) as QUIET; rewrite NEST in QUIET.
  change (quiet_statement body=true) in QUIET.
  destruct(@nested_expression_capture_execution fe ge locals temps memory row bound column child_bound
    (constant_body_source iterator(Int.repr upper) body) root_cache child_cache live source_after source_final
    TYPE CHILD_TYPE(@constant_literal_source_quiet iterator(Int.repr upper)body QUIET)
    FRAMEABLE PRIVATE CHILD_PRIVATE DISTINCT COLUMN_PRIVATE SOURCE)
    as [root_word [child [prepared_after [CAPTURE [PREPARED_SOURCE [PUBLIC [ROOT CHILD]]]]]]].
  set(prepared:=nested_expression_captured root_cache child_cache temps root_word child).
  set(scope:=statement_temps(nested_expression_source row bound column child_bound
    (constant_body_source iterator(Int.repr upper)body))++live).
  assert (FRAME : temp_agree scope temps prepared) by(apply nested_expression_captured_frame; assumption).
  assert (PREPARED_ROW : prepared!row=Some(Vint Int.zero)).
  { rewrite FRAME; [exact ROW|].
    unfold scope; apply in_or_app; left; apply nested_constant_row_scope. }
  assert (CACHE : prepared!root_cache=Some(Vint root_word)) by(apply nested_expression_captured_root; exact DISTINCT).
  assert (ROOT_READ : eval_expr ge locals prepared memory bound(Vint root_word)).
  { eapply expression_temp_transport; [|exact FRAME|exact ROOT].
    unfold expression_scope,scope; intros identifier MEMBER; apply in_or_app; left.
    exact(@nested_constant_bound_scope row bound column child_bound iterator(Int.repr upper)body identifier MEMBER). }
  assert (CHILD_READ : register_positive root_cache(Entry ge locals prepared memory)=true -> exists child_word,
    prepared!child_cache=Some(Vint child_word) /\ eval_expr ge locals prepared memory child_bound(Vint child_word)).
  { intro ACTIVE; destruct child as [child_word|].
    - destruct CHILD as [_ EVAL]; exists child_word; split; [apply nested_expression_captured_child|].
      eapply expression_temp_transport; [|exact FRAME|exact EVAL].
      unfold expression_scope,scope; intros identifier MEMBER; apply in_or_app; left.
      exact(@nested_constant_child_bound_scope row bound column child_bound iterator(Int.repr upper)body identifier MEMBER).
    - unfold register_positive,temp_word in ACTIVE,CHILD; cbn [entry_temps] in ACTIVE.
      rewrite CACHE in ACTIVE; rewrite ROW in CHILD; congruence. }
  destruct(@nested_constant_numeric_guard_execution row root_cache column child_cache child_helper iterator component_helper
    upper body parameters live proposal package fe ge locals bound child_bound root_word prepared memory
    prepared_after source_final NEST TYPE CHILD_TYPE COLUMN_PRIVATE PREPARED_ROW CACHE ROOT_READ CHILD_READ
    LITERAL_ACTIVE PREPARED_SOURCE) as [after [NUMERIC [KEEP [RESULT SOUND]]]].
  exists root_word,child,prepared_after,after; cbn zeta; fold prepared.
  split.
  - unfold nested_constant_captured_numeric_code; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); eassumption.
  - split.
    + eapply temp_agree_trans; [|eapply temp_agree_weaken; [|exact KEEP]].
      * eapply temp_agree_weaken; [|exact FRAME].
        unfold scope; intros identifier MEMBER; apply in_or_app; right; exact MEMBER.
      * unfold affine_single_materialized_ports; intros identifier MEMBER.
        apply in_or_app; right; apply in_or_app; right; exact MEMBER.
    + split; [exact PREPARED_SOURCE|split; [exact PUBLIC|split; [exact ROOT_READ|split; [exact CHILD_READ|split; [exact RESULT|]]]]].
      intro ACCEPT; destruct(SOUND ACCEPT) as [PARAMETERS DOMAIN].
      split; [exact PARAMETERS|split; [exact DOMAIN|]].
      eapply nested_constant_package_scan_inputs with (package:=package);
        [exact NEST| |exact PARAMETERS|exact DOMAIN].
      intro SAME; subst child_cache; apply CHILD_PRIVATE,in_or_app; left; apply nested_constant_row_scope.
Qed.

Print Assumptions nested_constant_captured_numeric_execution.
