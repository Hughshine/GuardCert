From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightFrontendLoopProtocol ClightFrontendRegion
  ClightLoopExecution ClightLoopSyntax ClightStraightLine ClightTempFrame ClightRegionProgress
  ClightNoWrap ClightRectangularStore ClightRectangularGuard ClightRectangularLoops ClightRectangularRegion.
From GuardInterface Require Import ClightStrictLoopProgress ClightLoopBodyTransport ClightRuntimeStrideBody
  ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.

Lemma fixed_temp_execution fe ge locals allowed code stride word le memory trace after final outcome :
  writes_only allowed code -> ~ In stride allowed -> le ! stride = Some word ->
  exec_stmt fe ge locals le memory code trace after final outcome -> after ! stride = Some word.
Proof.
  intros WRITES FRESH LOOKUP RUN; rewrite (@writes_only_frame fe ge locals le memory code trace after final outcome
    RUN allowed WRITES stride FRESH); exact LOOKUP.
Qed.

Theorem counted_body_transport_fixed fe ge locals iterator bound source_body target_body stride word
  (DISTINCT : stride <> iterator)
  (BODY : forall le memory trace after final outcome,
    le ! stride = Some word -> exec_stmt fe ge locals le memory source_body trace after final outcome ->
    exec_stmt fe ge locals le memory target_body trace after final outcome /\ after ! stride = Some word) :
  forall le memory trace after final outcome,
  le ! stride = Some word ->
  exec_stmt fe ge locals le memory (frontend_counted_loop iterator bound source_body) trace after final outcome ->
  exec_stmt fe ge locals le memory (frontend_counted_loop iterator bound target_body) trace after final outcome.
Proof.
  intros le memory trace after final outcome LOOKUP RUN.
  exact (proj1 (@strict_loop_body_transport fe ge locals iterator (counter_condition iterator bound)
    source_body target_body (fun le _ => le ! stride = Some word) BODY
    ltac:(intros before mem tr exit mem' out' STRIDE INC;
      eapply fixed_temp_execution with (allowed := [iterator]); [repeat constructor; cbn; auto|cbn; intuition|exact STRIDE|exact INC])
    le memory trace after final outcome RUN LOOKUP)).
Qed.

Lemma runtime_body_writes d array row column stride body :
  flatten_region body = [runtime_stride_store d array row column stride] -> writes_only [] body.
Proof. intro FLAT; apply flatten_writes_certificate; rewrite FLAT; repeat constructor. Qed.
Lemma runtime_body_quiet d array row column stride body :
  flatten_region body = [runtime_stride_store d array row column stride] -> quiet_statement body = true.
Proof. intro FLAT; apply flatten_quiet_certificate; rewrite FLAT; constructor; [reflexivity|constructor]. Qed.
Lemma runtime_body_normal d array row column stride body :
  flatten_region body = [runtime_stride_store d array row column stride] -> normal_statement body = true.
Proof. intro FLAT; apply flatten_normal_certificate; rewrite FLAT; constructor; [reflexivity|constructor]. Qed.

Theorem runtime_inner_constant fe ge locals d array row column iterator bound stride body le memory trace after final outcome :
  stride <> iterator -> flatten_region body = [runtime_stride_store d array row column stride] ->
  le ! stride = Some (Vint (Int.repr (rectangle_stride d))) ->
  exec_stmt fe ge locals le memory (frontend_counted_loop iterator bound body) trace after final outcome ->
  exec_stmt fe ge locals le memory (frontend_counted_loop iterator bound (rect_store d array row column)) trace after final outcome.
Proof.
  intros SC FLAT LOOKUP RUN; eapply counted_body_transport_fixed; [exact SC| |exact LOOKUP|exact RUN].
  intros before mem tr exit mem' out' STRIDE BODY.
  pose proof (@quiet_execution_silent fe ge locals before mem body tr exit mem' out' BODY
    (@runtime_body_quiet d array row column stride body FLAT)) as SILENT; subst tr.
  pose proof (@normal_statement_execution fe ge locals body (@runtime_body_normal d array row column stride body FLAT)
    before mem E0 exit mem' out' BODY) as EXIT; subst out'.
  assert (FRAME := @fixed_temp_execution fe ge locals [] body stride _ before mem E0 exit mem' Out_normal
    (@runtime_body_writes d array row column stride body FLAT) ltac:(cbn; tauto) STRIDE BODY).
  apply (flattened_singleton_execution FLAT) in BODY; split; [|exact FRAME].
  apply (proj1 (@runtime_stride_store_constant fe ge locals before mem d array row column stride E0 exit mem' Out_normal STRIDE)); exact BODY.
Qed.

Theorem constant_inner_runtime fe ge locals d array row column iterator bound stride le memory trace after final outcome :
  stride <> iterator -> le ! stride = Some (Vint (Int.repr (rectangle_stride d))) ->
  exec_stmt fe ge locals le memory (frontend_counted_loop iterator bound (rect_store d array row column)) trace after final outcome ->
  exec_stmt fe ge locals le memory (frontend_counted_loop iterator bound (runtime_stride_store d array row column stride)) trace after final outcome.
Proof.
  intros SC LOOKUP RUN; eapply counted_body_transport_fixed; [exact SC| |exact LOOKUP|exact RUN].
  intros before mem tr exit mem' out' STRIDE BODY; split.
  - apply (proj2 (@runtime_stride_store_constant fe ge locals before mem d array row column stride tr exit mem' out' STRIDE)); exact BODY.
  - eapply fixed_temp_execution with (allowed := []); [constructor|cbn; tauto|exact STRIDE|exact BODY].
Qed.

Theorem runtime_rectangle_constant fe ge locals d array row bound column inner_bound stride body outer_body
  le memory trace after final outcome :
  stride <> row -> stride <> column ->
  flatten_region body = [runtime_stride_store d array row column stride] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column inner_bound body] ->
  le ! stride = Some (Vint (Int.repr (rectangle_stride d))) ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) trace after final outcome ->
  exec_stmt fe ge locals le memory
    (frontend_counted_loop row bound (rectangle_outer_body column inner_bound (rect_store d array row column)))
    trace after final outcome.
Proof.
  intros SR SC FLAT OUTER LOOKUP RUN; eapply counted_body_transport_fixed; [exact SR| |exact LOOKUP|exact RUN].
  intros before mem tr exit mem' out' STRIDE OUTER_RUN.
  assert (QUIET : quiet_statement outer_body = true).
  { apply flatten_quiet_certificate; rewrite OUTER; constructor; [reflexivity|constructor; [|constructor]].
    cbn [frontend_counted_loop quiet_statement counter_increment];
      rewrite (@runtime_body_quiet d array row column stride body FLAT); reflexivity. }
  pose proof (@quiet_execution_silent fe ge locals before mem outer_body tr exit mem' out' OUTER_RUN QUIET) as SILENT; subst tr.
  pose proof (@normal_statement_execution fe ge locals outer_body
    (@rectangle_outer_normal column inner_bound body outer_body (@runtime_body_quiet d array row column stride body FLAT) OUTER)
    before mem E0 exit mem' out' OUTER_RUN) as EXIT; subst out'.
  pose proof (@fixed_temp_execution fe ge locals [column] outer_body stride _ before mem E0 exit mem' Out_normal
    (@rectangle_outer_writes column inner_bound body outer_body (@runtime_body_writes d array row column stride body FLAT) OUTER)
    ltac:(cbn; intuition) STRIDE OUTER_RUN) as FRAME.
  apply (@flattened_pair_execution fe ge locals outer_body (rectangle_reset column)
    (frontend_counted_loop column inner_bound body) before mem exit mem' OUTER) in OUTER_RUN; destruct (sequence_normal_decode OUTER_RUN) as [middle [mem1 [RESET INNER]]].
  assert (NEXT := @fixed_temp_execution fe ge locals [column] (rectangle_reset column) stride _ before mem E0 middle mem1 Out_normal
    ltac:(constructor; cbn; auto) ltac:(cbn; intuition) STRIDE RESET).
  split; [|exact FRAME]; unfold rectangle_outer_body; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact RESET|].
  exact (@runtime_inner_constant fe ge locals d array row column column inner_bound stride body middle mem1 E0 exit mem' Out_normal SC FLAT NEXT INNER).
Qed.
Print Assumptions counted_body_transport_fixed.
Print Assumptions runtime_inner_constant.
Print Assumptions constant_inner_runtime.
Print Assumptions runtime_rectangle_constant.

Theorem constant_interchanged_runtime fe ge locals d array row bound column inner_bound stride
  le memory after final :
  stride <> row -> stride <> column ->
  le ! stride = Some (Vint (Int.repr (rectangle_stride d))) ->
  exec_stmt fe ge locals le memory
    (rectangle_interchanged row bound column inner_bound (rect_store d array row column)) E0 after final Out_normal ->
  exec_stmt fe ge locals le memory
    (rectangle_interchanged row bound column inner_bound (runtime_stride_store d array row column stride)) E0 after final Out_normal.
Proof.
  intros SR SC LOOKUP RUN; unfold rectangle_interchanged in RUN |- *.
  destruct (sequence_normal_decode RUN) as [middle [mem1 [RESET LOOP]]].
  pose proof (@fixed_temp_execution fe ge locals [column] (rectangle_reset column) stride _ le memory E0 middle mem1 Out_normal
    ltac:(constructor; cbn; auto) ltac:(cbn; intuition) LOOKUP RESET) as NEXT.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact RESET|].
  eapply counted_body_transport_fixed; [exact SC| |exact NEXT|exact LOOP].
  intros before mem tr exit mem' out' STRIDE OUTER.
  assert (QUIET : quiet_statement (rectangle_outer_body row bound (rect_store d array row column)) = true) by reflexivity.
  pose proof (@quiet_execution_silent fe ge locals before mem _ tr exit mem' out' OUTER QUIET) as SILENT; subst tr.
  pose proof (@normal_statement_execution fe ge locals _
    (@rectangle_outer_normal row bound (rect_store d array row column)
      (rectangle_outer_body row bound (rect_store d array row column)) ltac:(reflexivity) ltac:(reflexivity))
    before mem E0 exit mem' out' OUTER) as EXIT; subst out'.
  assert (FRAME : exit ! stride = Some (Vint (Int.repr (rectangle_stride d)))).
  { eapply fixed_temp_execution with (allowed := [row]); [|cbn; intuition|exact STRIDE|exact OUTER].
    unfold rectangle_outer_body, frontend_counted_loop, counter_increment;
      repeat constructor; cbn; auto. }
  destruct (sequence_normal_decode OUTER) as [inner_temps [inner_mem [RESET_ROW INNER]]].
  pose proof (@fixed_temp_execution fe ge locals [row] (rectangle_reset row) stride _ before mem E0 inner_temps inner_mem Out_normal
    ltac:(constructor; cbn; auto) ltac:(cbn; intuition) STRIDE RESET_ROW) as INNER_STRIDE.
  split; [|exact FRAME]; unfold rectangle_outer_body; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact RESET_ROW|].
  exact (@constant_inner_runtime fe ge locals d array row column row bound stride inner_temps inner_mem E0 exit mem' Out_normal
    SR INNER_STRIDE INNER).
Qed.

Theorem runtime_stride_rectangle_forward fe ge locals d array row bound column inner_bound stride body outer_body
  le memory after final N M :
  rectangle_layout_valid d -> row <> bound -> row <> column -> bound <> column ->
  row <> inner_bound -> column <> inner_bound -> stride <> row -> stride <> column ->
  flatten_region body = [runtime_stride_store d array row column stride] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column inner_bound body] ->
  le ! stride = Some (Vint (Int.repr (rectangle_stride d))) ->
  le ! row = Some (Vint Int.zero) -> le ! bound = Some (Vint (Int.repr N)) ->
  le ! inner_bound = Some (Vint (Int.repr M)) -> signed_range N -> signed_range M ->
  (0 < N <= rectangle_outer_limit d)%Z -> (0 < M <= rectangle_stride d)%Z ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 after final Out_normal ->
  exec_stmt fe ge locals le memory
    (rectangle_interchanged row bound column inner_bound (runtime_stride_store d array row column stride)) E0 after final Out_normal.
Proof.
  intros VALID RN RC NC RM CM SR SC FLAT OUTER STRIDE ZERO NB MB NS MS NR MR SOURCE.
  pose proof (@runtime_rectangle_constant fe ge locals d array row bound column inner_bound stride body outer_body
    le memory E0 after final Out_normal SR SC FLAT OUTER STRIDE SOURCE) as CONSTANT.
  pose proof (@rectangle_local d VALID array row bound column inner_bound (rect_store d array row column)
    (rectangle_outer_body column inner_bound (rect_store d array row column)) RN RC NC RM CM
    ltac:(reflexivity) ltac:(reflexivity) fe ge locals le memory after final N M ZERO NB MB NS MS NR MR CONSTANT) as INTERCHANGED.
  exact (@constant_interchanged_runtime fe ge locals d array row bound column inner_bound stride
    le memory after final SR SC STRIDE INTERCHANGED).
Qed.
Print Assumptions constant_interchanged_runtime.
Print Assumptions runtime_stride_rectangle_forward.
