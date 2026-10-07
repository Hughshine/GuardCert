From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightNoWrap ClightRegionProgress
  ClightProjectedExecution ClightPureExpr.
From GuardAffineNest Require Import AffineNestGuardPackage AffineNestNamespace.
From GuardInterface Require Import ClightNestedConstantSite ClightNestedConstantSiteFacts
  ClightNestedConstantSiteNumeric ClightNestedExpressionCapture ClightNestedConstantFirstLeaf
  ClightExpressionHeaderCapture ClightLoadedOffsetHeader ClightSignedExpressionProgress ClightCheckPlanFrame.
Import ListNotations.
Set Implicit Arguments.

Definition ncs_zero_row_expr row := Ebinop Cop.Oeq(Etempvar row type_int32s)(Econst_int Int.zero type_int32s) type_int32s.
Definition ncs_zero_row_flag row entry := Int.eq(temp_word row(entry_temps entry)) Int.zero.
Lemma ncs_zero_row_evaluation ge locals temps memory row word :
  temps!row=Some(Vint word) -> expression_test(ncs_zero_row_expr row)(Entry ge locals temps memory)(Int.eq word Int.zero).
Proof.
  intro ROW; exists(Val.of_bool(Int.eq word Int.zero)); split; [|apply bool_of_bool].
  eapply eval_Ebinop; [constructor; exact ROW|constructor|reflexivity].
Qed.

Definition ncs_entry_numeric_code source parameters live proposal shape
  (site:nested_constant_site source parameters live proposal shape) :=
  Sifthenelse(ncs_zero_row_expr(ncs_row shape))(ncs_numeric_code site)
    (Sset(affine_proposed_result proposal)(Econst_int Int.zero type_int32s)).
Definition ncs_entry_numeric_flag parameters proposal shape entry :=
  ncs_zero_row_flag(ncs_row shape) entry && ncs_numeric_flag parameters proposal shape entry.

Section ENTRY.
Variables source : statement.
Variables parameters live : list ident.
Variable proposal : affine_guard_proposal.
Variable shape : nested_constant_shape.
Variable site : nested_constant_site source parameters live proposal shape.

Lemma ncs_site_result_private : ~In(affine_proposed_result proposal)(ncs_scope source live).
Proof.
  pose proof(affine_names_result_private(affine_package_namespace(ncs_package site))) as PRIVATE.
  intro MEMBER; apply PRIVATE.
  apply in_or_app; right; apply in_or_app; right.
  unfold ncs_package_live; apply in_or_app; left; exact MEMBER.
Qed.

Record ncs_entry_numeric_receipt fe ge locals original memory original_after final checked : Prop := NCSEntryNumericReceipt {
  ncs_entry_run : exec_stmt fe ge locals original memory(ncs_entry_numeric_code site) E0 checked memory Out_normal;
  ncs_entry_public : temp_agree(ncs_scope source live) original checked;
  ncs_entry_source : exists after,exec_stmt fe ge locals checked memory source E0 after final Out_normal /\
    temp_agree(ncs_scope source live) original_after after;
  ncs_entry_result : checked!(affine_proposed_result proposal)=
    Some(Vint(if ncs_entry_numeric_flag parameters proposal shape(Entry ge locals checked memory) then Int.one else Int.zero));
  ncs_entry_accept : ncs_entry_numeric_flag parameters proposal shape(Entry ge locals checked memory)=true ->
    ncs_numeric_receipt site fe ge locals original memory original_after final checked
}.

(** Original source completion supplies the row word. A nonzero entry row
    bypasses both loaded headers and all BODY inputs; no contextual row=0
    invariant is needed to instantiate this emitted check. *)
Theorem ncs_entry_numeric_execution fe ge locals temps memory source_after final :
  exec_stmt fe ge locals temps memory source E0 source_after final Out_normal ->
  exists checked,ncs_entry_numeric_receipt fe ge locals temps memory source_after final checked.
Proof.
  intro SOURCE; pose proof SOURCE as ORIGINAL.
  rewrite(ncs_exact site) in SOURCE.
  destruct(@signed_expression_completed_header fe ge locals temps memory(ncs_row shape)
    (signed_load_offset(ncs_pointer shape)(ncs_delta shape))
    (nested_expression_body(ncs_column shape)
      (ClightSignedIndexedOffsetHeader.signed_indexed_offset(ncs_pointer shape)(ncs_index shape)(ncs_child_delta shape))
      (ClightConstantBoundModel.constant_body_source(ncs_iterator shape)(Int.repr(ncs_upper shape))(ncs_leaf shape)))
    E0 source_after final Out_normal SOURCE) as [flag HEADER].
  destruct(@signed_expression_test_facts ge locals temps memory(ncs_row shape)
    (signed_load_offset(ncs_pointer shape)(ncs_delta shape)) flag eq_refl HEADER) as [word [upper [ROW REST]]].
  destruct(@ncs_zero_row_evaluation ge locals temps memory(ncs_row shape) word ROW) as [value [EVAL BOOL]].
  assert(ROW_SCOPE : In(ncs_row shape)(ncs_scope source live)).
  { unfold ncs_scope; rewrite(ncs_exact site); apply in_or_app; left; apply nested_constant_row_scope. }
  pose proof(Int.eq_spec word Int.zero) as ZERO.
  destruct(Int.eq word Int.zero) eqn:ACTIVE.
  - subst word; destruct(ncs_numeric_site_execution site ROW ORIGINAL) as [checked RECEIPT].
    assert(CURRENT_ROW : ncs_zero_row_flag(ncs_row shape)(Entry ge locals checked memory)=true).
    { unfold ncs_zero_row_flag,temp_word; cbn [entry_temps]; rewrite(ncs_numeric_row RECEIPT); apply Int.eq_true. }
    exists checked; constructor.
    + unfold ncs_entry_numeric_code; eapply exec_Sifthenelse; [exact EVAL|exact BOOL|exact(ncs_numeric_run RECEIPT)].
    + exact(ncs_numeric_public RECEIPT).
    + exact(ncs_numeric_source RECEIPT).
    + unfold ncs_entry_numeric_flag; rewrite CURRENT_ROW; exact(ncs_numeric_result RECEIPT).
    + intro ACCEPT; exact RECEIPT.
  - set(checked:=PTree.set(affine_proposed_result proposal)(Vint Int.zero)temps).
    assert(FRAME : temp_agree(ncs_scope source live) temps checked) by(apply temp_agree_set; exact ncs_site_result_private).
    assert(CURRENT_ROW : ncs_zero_row_flag(ncs_row shape)(Entry ge locals checked memory)=false).
    { unfold ncs_zero_row_flag,temp_word; cbn [entry_temps]; rewrite FRAME by exact ROW_SCOPE; rewrite ROW; exact ACTIVE. }
    exists checked; constructor.
    + unfold ncs_entry_numeric_code,checked; eapply exec_Sifthenelse; [exact EVAL|exact BOOL|constructor; constructor].
    + exact FRAME.
    + eapply structured_execution_temp_transport with(live:=ncs_scope source live)(allowed:=statement_temps source).
      * exact ORIGINAL.
      * apply check_plan_frameable_writes; exact(ncs_frameable site).
      * unfold statement_scope,ncs_scope; intros identifier MEMBER; apply in_or_app; left; exact MEMBER.
      * exact FRAME.
    + unfold ncs_entry_numeric_flag; rewrite CURRENT_ROW; unfold checked; apply PTree.gss.
    + unfold ncs_entry_numeric_flag; rewrite CURRENT_ROW; discriminate.
Qed.

End ENTRY.

Print Assumptions ncs_zero_row_evaluation.
Print Assumptions ncs_site_result_private.
Print Assumptions ncs_entry_numeric_execution.
