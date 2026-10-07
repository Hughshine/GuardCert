From Stdlib Require Import List.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightProjectedExecution
  ClightPureExpr ClightNoWrap ClightLoopSyntax ClightRegionProgress ClightStraightLine ClightRectangularLoops.
From GuardInterface Require Import ClightConstantBoundModel ClightSignedExpressionProgress ClightStrictLoopProgress ClightStrictIteration
  ClightExpressionHeaderCapture ClightNestedExpressionCapture.
Import ListNotations.
Set Implicit Arguments.

Lemma constant_literal_source_quiet iterator literal body :
  quiet_statement body=true -> quiet_statement(constant_body_source iterator literal body)=true.
Proof.
  intro QUIET; unfold constant_body_source,strict_frontend_loop,rectangle_reset.
  cbn [quiet_statement]; rewrite QUIET; reflexivity.
Qed.

Lemma constant_literal_source_normal iterator literal body :
  quiet_statement body=true -> normal_statement(constant_body_source iterator literal body)=true.
Proof.
  intro QUIET; unfold constant_body_source,strict_frontend_loop,rectangle_reset.
  cbn [normal_statement quiet_statement]; rewrite QUIET; reflexivity.
Qed.

(** Only the actual first source path is used. No cached execution, alias
    stability, mathematical range, or private helper word licenses this leaf. *)
Theorem nested_constant_original_first_leaf fe ge locals row bound column child_bound iterator literal body
  temps memory after final root_word child_word :
  typeof bound=type_int32s -> typeof child_bound=type_int32s ->
  normal_statement body=true -> quiet_statement body=true ->
  ~In column(expression_temps child_bound) ->
  eval_expr ge locals temps memory bound(Vint root_word) ->
  eval_expr ge locals temps memory child_bound(Vint child_word) ->
  Int.lt(temp_word row temps) root_word=true -> Int.lt Int.zero child_word=true ->
  Int.lt Int.zero literal=true ->
  exec_stmt fe ge locals temps memory
    (nested_expression_source row bound column child_bound(constant_body_source iterator literal body))
    E0 after final Out_normal ->
  exists leaf_after leaf_final,
    exec_stmt fe ge locals(PTree.set iterator(Vint Int.zero)(PTree.set column(Vint Int.zero)temps))
      memory body E0 leaf_after leaf_final Out_normal.
Proof.
  intros TYPE CHILD_TYPE NORMAL QUIET COLUMN_PRIVATE ROOT CHILD ROOT_ACTIVE CHILD_ACTIVE LITERAL_ACTIVE SOURCE.
  destruct(@nested_expression_first_child fe ge locals temps memory row bound column child_bound
    (constant_body_source iterator literal body) after final root_word TYPE
    (@constant_literal_source_quiet iterator literal body QUIET) ROOT ROOT_ACTIVE SOURCE)
    as [child_after [child_final CHILD_SOURCE]].
  assert (CHILD_EVAL : eval_expr ge locals(PTree.set column(Vint Int.zero)temps) memory child_bound(Vint child_word)).
  { eapply expression_temp_transport; [unfold expression_scope; apply incl_refl| |exact CHILD].
    intros identifier MEMBER; rewrite PTree.gso; [reflexivity|].
    intro SAME; subst identifier; contradiction. }
  pose proof(@signed_expression_test_eval ge locals(PTree.set column(Vint Int.zero)temps) memory column child_bound
    Int.zero child_word CHILD_TYPE(PTree.gss _ _ _) CHILD_EVAL) as CHILD_TEST.
  rewrite CHILD_ACTIVE in CHILD_TEST.
  destruct(@strict_active_iteration fe ge locals column(signed_expression_test column child_bound)
    (constant_body_source iterator literal body)(PTree.set column(Vint Int.zero)temps) memory child_after child_final
    (@constant_literal_source_normal iterator literal body QUIET)(@constant_literal_source_quiet iterator literal body QUIET)
    CHILD_TEST CHILD_SOURCE) as [component_after [component_final [next [next_memory [COMPONENT REST]]]]].
  destruct(sequence_normal_decode COMPONENT) as [reset [reset_memory [RESET LOOP]]].
  destruct(rectangle_reset_decode RESET) as [_ [TEMPS [MEMORY _]]]; subst reset reset_memory.
  pose proof(@signed_expression_test_eval ge locals
    (PTree.set iterator(Vint Int.zero)(PTree.set column(Vint Int.zero)temps)) memory iterator(Econst_int literal type_int32s)
    Int.zero literal eq_refl(PTree.gss _ _ _) ltac:(constructor)) as COMPONENT_TEST.
  rewrite LITERAL_ACTIVE in COMPONENT_TEST.
  destruct(@strict_active_iteration fe ge locals iterator(signed_expression_test iterator(Econst_int literal type_int32s))
    body _ memory component_after component_final NORMAL QUIET COMPONENT_TEST LOOP)
    as [leaf_after [leaf_final [following [following_memory [LEAF _]]]]].
  exists leaf_after,leaf_final; exact LEAF.
Qed.

Lemma nested_constant_bound_scope row bound column child_bound iterator literal body :
  expression_scope(statement_temps(nested_expression_source row bound column child_bound
    (constant_body_source iterator literal body))) bound.
Proof. unfold nested_expression_source; apply signed_expression_bound_in_scope. Qed.

Lemma nested_constant_child_bound_scope row bound column child_bound iterator literal body :
  expression_scope(statement_temps(nested_expression_source row bound column child_bound
    (constant_body_source iterator literal body))) child_bound.
Proof.
  unfold expression_scope,nested_expression_source,nested_expression_body,strict_frontend_loop,signed_expression_test.
  cbn [statement_temps expression_temps]; intros identifier MEMBER.
  repeat rewrite in_app_iff; cbn; tauto.
Qed.

Lemma nested_constant_row_scope row bound column child_bound iterator literal body :
  In row(statement_temps(nested_expression_source row bound column child_bound
    (constant_body_source iterator literal body))).
Proof.
  unfold nested_expression_source,strict_frontend_loop,signed_expression_test.
  cbn [statement_temps expression_temps]; repeat rewrite in_app_iff; cbn; tauto.
Qed.

Print Assumptions constant_literal_source_quiet.
Print Assumptions constant_literal_source_normal.
Print Assumptions nested_constant_original_first_leaf.
Print Assumptions nested_constant_bound_scope.
Print Assumptions nested_constant_child_bound_scope.
Print Assumptions nested_constant_row_scope.
