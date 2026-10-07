From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightTempFootprint.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightLoadedOffsetHeader ClightSignedIndexedOffsetHeader
  ClightStableLoopCondition ClightSignedExpressionProgress ClightStrictLoopProgress ClightNestedExpressionCapture
  ClightNestedConstantSite.
Set Implicit Arguments.

Lemma signed_indexed_zero_address offset : signed_indexed_address offset Int.zero=offset.
Proof.
  unfold signed_indexed_address; rewrite Int.signed_zero.
  change(Ptrofs.add offset(Ptrofs.mul(Ptrofs.repr 4)Ptrofs.zero)=offset).
  rewrite Ptrofs.mul_zero,Ptrofs.add_zero; reflexivity.
Qed.

Theorem signed_zero_index_load_equivalent ge locals temps memory pointer value :
  eval_expr ge locals temps memory(signed_indexed_load pointer Int.zero)value <->
  eval_expr ge locals temps memory(signed_load pointer)value.
Proof.
  split.
  - intro RUN; destruct(signed_indexed_load_inv RUN) as [block [offset [POINTER READ]]].
    rewrite signed_indexed_zero_address in READ.
    eapply eval_Elvalue with(loc:=block)(ofs:=offset)(bf:=Full).
    + apply eval_Ederef,eval_Etempvar; exact POINTER.
    + apply deref_loc_value with(chunk:=Mint32); [reflexivity|exact READ].
  - intro RUN; destruct(signed_load_inv RUN) as [block [offset [POINTER READ]]].
    eapply signed_indexed_load_eval; [exact POINTER|].
    rewrite signed_indexed_zero_address; exact READ.
Qed.

Theorem signed_zero_index_offset_equivalent ge locals temps memory pointer delta value :
  eval_expr ge locals temps memory(signed_indexed_offset pointer Int.zero delta)value <->
  eval_expr ge locals temps memory(signed_load_offset pointer delta)value.
Proof.
  split; intro RUN; apply scalar_binary_inv in RUN;
    destruct RUN as [loaded [constant [LOAD [CONST OP]]]]; eapply eval_Ebinop;
    [apply(proj1(signed_zero_index_load_equivalent _ _ _ _ _ _)); exact LOAD|exact CONST|exact OP|
     apply(proj2(signed_zero_index_load_equivalent _ _ _ _ _ _)); exact LOAD|exact CONST|exact OP].
Qed.

Lemma signed_zero_index_test_equivalent ge locals temps memory row pointer delta flag :
  expression_test(signed_expression_test row(signed_indexed_offset pointer Int.zero delta))(Entry ge locals temps memory)flag <->
  expression_test(signed_expression_test row(signed_load_offset pointer delta))(Entry ge locals temps memory)flag.
Proof.
  split; intros [value [EVAL BOOL]]; apply scalar_binary_inv in EVAL;
    destruct EVAL as [counter [upper [ROW [UPPER OP]]]]; exists value; split; [|exact BOOL| |exact BOOL];
    eapply eval_Ebinop; [exact ROW| |exact OP|exact ROW| |exact OP].
  - apply(proj1(signed_zero_index_offset_equivalent _ _ _ _ _ _ _)); exact UPPER.
  - apply(proj2(signed_zero_index_offset_equivalent _ _ _ _ _ _ _)); exact UPPER.
Qed.

Definition ncs_zero_index_original shape := nested_expression_source(ncs_row shape)
  (signed_indexed_offset(ncs_pointer shape)Int.zero(ncs_delta shape))(ncs_column shape)
  (signed_indexed_offset(ncs_pointer shape)(ncs_index shape)(ncs_child_delta shape))
  (ClightConstantBoundModel.constant_body_source(ncs_iterator shape)(Int.repr(ncs_upper shape))(ncs_leaf shape)).

Theorem ncs_zero_index_execution_equivalent fe ge locals temps memory shape trace after final outcome :
  exec_stmt fe ge locals temps memory(ncs_zero_index_original shape)trace after final outcome <->
  exec_stmt fe ge locals temps memory(ncs_original shape)trace after final outcome.
Proof.
  unfold ncs_zero_index_original,ncs_original,nested_expression_source.
  split; intro SOURCE.
  - exact(proj1(@strict_loop_condition_transport fe ge locals(ncs_row shape) _ _ _ (fun _ _=>True)
      (fun le m flag _=>proj1(@signed_zero_index_test_equivalent ge locals le m(ncs_row shape)(ncs_pointer shape)(ncs_delta shape)flag))
      (fun _ _ _ _ _ _ _ _=>I)(fun _ _ _ _ _ _ _ _=>I) _ _ _ _ _ _ SOURCE I)).
  - exact(proj1(@strict_loop_condition_transport fe ge locals(ncs_row shape) _ _ _ (fun _ _=>True)
      (fun le m flag _=>proj2(@signed_zero_index_test_equivalent ge locals le m(ncs_row shape)(ncs_pointer shape)(ncs_delta shape)flag))
      (fun _ _ _ _ _ _ _ _=>I)(fun _ _ _ _ _ _ _ _=>I) _ _ _ _ _ _ SOURCE I)).
Qed.

Lemma ncs_zero_index_temps shape : statement_temps(ncs_zero_index_original shape)=statement_temps(ncs_original shape).
Proof. unfold ncs_zero_index_original,ncs_original,nested_expression_source,strict_frontend_loop,
  signed_expression_test,signed_indexed_offset,signed_load_offset,signed_indexed_load,signed_load,signed_indexed_pointer,
  signed_pointer_temp; cbn [statement_temps expression_temps]; repeat rewrite app_nil_r; reflexivity. Qed.

Print Assumptions signed_indexed_zero_address.
Print Assumptions signed_zero_index_load_equivalent.
Print Assumptions signed_zero_index_offset_equivalent.
Print Assumptions signed_zero_index_test_equivalent.
Print Assumptions ncs_zero_index_execution_equivalent.
Print Assumptions ncs_zero_index_temps.
