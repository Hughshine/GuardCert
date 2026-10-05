From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightNoWrap ClightRedundantSet ClightStraightLine
  ClightTempFrame ClightRegionProgress ClightFrontendLoopProtocol ClightLoopExecution ClightLoopSyntax ClightRectangularStore
  ClightRectangularGuard ClightRectangularLoops ClightRectangularRegion.
From GuardInterface Require Import ClightReadonlyRewrite ClightReadonlyProjectedCompiler ClightRegionBoundary ClightLoadedRectangleRow
  ClightLoadedRectangleGuard ClightLoadedRectangleForward ClightLoadedStrideTransport ClightLoadedStrideGuard
  ClightRuntimeStrideBody ClightRuntimeStrideLoops ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.

Theorem loaded_stride_candidate_runtime d fe ge locals array row bound column columns stride cache
  le memory after final :
  stride <> row -> stride <> column -> cache <> stride ->
  le ! stride = Some (Vint (Int.repr (rectangle_stride d))) ->
  exec_stmt fe ge locals le memory (loaded_rectangle_candidate d array row bound column columns cache) E0 after final Out_normal ->
  exec_stmt fe ge locals le memory (loaded_stride_candidate d array row bound column columns stride cache) E0 after final Out_normal.
Proof.
  intros SR SC CS STRIDE SOURCE.
  destruct (sequence_normal_decode SOURCE) as [middle [mem1 [SNAPSHOT LOOP]]].
  assert (NEXT : middle ! stride = Some (Vint (Int.repr (rectangle_stride d)))).
  { eapply fixed_temp_execution with (allowed := [cache]);
      [constructor; cbn; auto|cbn; intuition|exact STRIDE|exact SNAPSHOT]. }
  unfold loaded_stride_candidate; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact SNAPSHOT|].
  exact (@constant_interchanged_runtime fe ge locals d array row cache column columns stride
    middle mem1 after final SR SC NEXT LOOP).
Qed.

Theorem loaded_stride_forward d fe live array row bound column columns stride cache body outer_body models entry observed :
  row <> bound -> row <> column -> bound <> column -> row <> columns -> column <> columns ->
  stride <> row -> stride <> column -> cache <> row -> cache <> bound -> cache <> column -> cache <> columns ->
  cache <> stride -> ~ In cache live ->
  flatten_region body = [runtime_stride_store d array row column stride] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body] ->
  loaded_stride_domain row bound outer_body entry ->
  @loaded_stride_property d array row bound columns stride models entry ->
  clight_fragment_run fe (loaded_rectangle_source row bound outer_body) entry observed ->
  exists transformed, clight_fragment_run fe (loaded_stride_candidate d array row bound column columns stride cache) entry transformed /\
    boundary_observe (public_exit_ports live) observed transformed.
Proof.
  intros RQ RC QC RM CM SR SC CR CQ CC CK CS FRESH BODY OUTER DOMAIN [PRELIMINARY [model [IN [MATCH PREMISE]]]] SOURCE.
  assert (CONSTANT_DOMAIN : loaded_rectangle_domain row bound
    (loaded_stride_constant_outer (loaded_stride_shape d (model_stride model)) array row column columns) entry).
  { eapply loaded_stride_domain_constant; [exact SR|exact SC|exact BODY|exact OUTER|exact DOMAIN|exact MATCH]. }
  assert (CONSTANT_SOURCE : clight_fragment_run fe
    (loaded_rectangle_source row bound (loaded_stride_constant_outer (loaded_stride_shape d (model_stride model)) array row column columns)) entry observed).
  { destruct entry, observed; eapply loaded_stride_source_constant;
      [exact SR|exact SC|exact BODY|exact OUTER|exact MATCH|exact SOURCE]. }
  destruct (@loaded_rectangle_forward (loaded_stride_shape d (model_stride model)) (model_layout_valid model) fe live
    array row bound column columns cache (rect_store (loaded_stride_shape d (model_stride model)) array row column)
    (loaded_stride_constant_outer (loaded_stride_shape d (model_stride model)) array row column columns) entry observed
    RQ RC QC RM CM CR CQ CC CK FRESH eq_refl eq_refl CONSTANT_DOMAIN PREMISE CONSTANT_SOURCE)
    as [transformed [RUN PUBLIC]].
  exists transformed; split; [|exact PUBLIC].
  destruct entry as [ge locals le memory], transformed as [trace after final outcome].
  assert (QUIET : quiet_statement (loaded_rectangle_candidate (loaded_stride_shape d (model_stride model))
    array row bound column columns cache) = true) by reflexivity.
  pose proof (@quiet_execution_silent fe ge locals le memory _ trace after final outcome RUN QUIET) as SILENT; subst trace.
  pose proof (@normal_statement_execution fe ge locals
    (loaded_rectangle_candidate (loaded_stride_shape d (model_stride model)) array row bound column columns cache)
    ltac:(reflexivity) le memory E0 after final outcome RUN) as NORMAL; subst outcome.
  exact (@loaded_stride_candidate_runtime (loaded_stride_shape d (model_stride model)) fe ge locals array row bound column columns stride cache
    le memory after final SR SC CS MATCH RUN).
Qed.

Print Assumptions loaded_stride_candidate_runtime.
Print Assumptions loaded_stride_forward.
