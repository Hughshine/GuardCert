From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightNoWrap ClightPureExpr ClightMatrixGuard ClightRedundantSet ClightCountedLoop ClightCountedProtocol
  ClightFrontendLoopProtocol ClightFrontendRegion ClightLoopExecution ClightLoopSyntax ClightStraightLine
  ClightTempFrame ClightRegionProgress ClightZeroTrip ClightFramedLoop ClightRectangularStore ClightRectangularGuard ClightRectangularLoops ClightRectangularRegion.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightLoadedBoundGuard ClightLoadedMatrixSyntax
  ClightLoadedRectangleRow ClightLoadedRectangleAtoms ClightLoadedRectangleGuard ClightLoadedRectangleForward ClightStrictIteration
  ClightStrictLoopProgress ClightLoopBodyTransport ClightRuntimeStrideBody ClightRuntimeStrideLoops
  ClightQuietDeterminacy ClightReadonlyRewrite ClightRegionBoundary ClightLoopBridge.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition loaded_stride_shape d step := RectangleShape (rectangle_extent d) step
  (rectangle_coefficient d) (rectangle_bias d).
Definition loaded_stride_constant_outer d array row column columns :=
  rectangle_outer_body column columns (rect_store d array row column).
Definition loaded_stride_candidate d array row bound column columns stride cache :=
  Ssequence (Sset cache (signed_load bound))
    (rectangle_interchanged row cache column columns (runtime_stride_store d array row column stride)).
Definition loaded_stride_domain row bound outer_body entry :=
  loaded_bound_entry row bound entry /\ quiet_source_completion (loaded_rectangle_source row bound outer_body) entry.

Lemma loaded_stride_product_bound d step count : 0 < step ->
  (count <= rectangle_extent d / step <-> count * step <= rectangle_extent d).
Proof.
  intro POS; split.
  - intro LIMIT; pose proof (Z.div_mod (rectangle_extent d) step ltac:(lia)) as DIV.
    pose proof (Z.mod_pos_bound (rectangle_extent d) step POS) as MOD; nia.
  - intro PRODUCT; apply Z.div_le_lower_bound; [exact POS|nia].
Qed.

Lemma loaded_stride_outer_quiet d array row column columns stride body outer_body :
  flatten_region body = [runtime_stride_store d array row column stride] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body] ->
  quiet_statement outer_body = true.
Proof.
  intros BODY OUTER; apply flatten_quiet_certificate; rewrite OUTER.
  constructor; [reflexivity|constructor; [|constructor]].
  cbn [frontend_counted_loop quiet_statement counter_increment];
    rewrite (@runtime_body_quiet d array row column stride body BODY); reflexivity.
Qed.
Lemma loaded_stride_source_quiet d array row bound column columns stride body outer_body :
  flatten_region body = [runtime_stride_store d array row column stride] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body] ->
  quiet_statement (loaded_rectangle_source row bound outer_body) = true.
Proof.
  intros BODY OUTER; cbn [loaded_rectangle_source loaded_bound_loop strict_frontend_loop quiet_statement counter_increment].
  rewrite (@loaded_stride_outer_quiet d array row column columns stride body outer_body BODY OUTER); reflexivity.
Qed.
Lemma loaded_stride_writes d array row bound column columns stride body outer_body :
  flatten_region body = [runtime_stride_store d array row column stride] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body] ->
  writes_only [row;column] (loaded_rectangle_source row bound outer_body).
Proof.
  intros BODY OUTER; pose proof (@rectangle_outer_writes column columns body outer_body
    (@runtime_body_writes d array row column stride body BODY) OUTER) as WRITES.
  unfold loaded_rectangle_source, loaded_bound_loop, strict_frontend_loop, counter_increment.
  repeat constructor; cbn; auto; eapply writes_only_weaken; [|exact WRITES]; cbn; tauto.
Qed.

Theorem loaded_stride_outer_constant fe ge locals d array row column columns stride body outer_body
  le memory trace after final outcome :
  stride <> column -> flatten_region body = [runtime_stride_store d array row column stride] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body] ->
  le ! stride = Some (Vint (Int.repr (rectangle_stride d))) ->
  exec_stmt fe ge locals le memory outer_body trace after final outcome ->
  exec_stmt fe ge locals le memory (loaded_stride_constant_outer d array row column columns) trace after final outcome /\
  after ! stride = Some (Vint (Int.repr (rectangle_stride d))).
Proof.
  intros SC BODY OUTER STRIDE RUN.
  pose proof (@quiet_execution_silent fe ge locals le memory outer_body trace after final outcome RUN
    (@loaded_stride_outer_quiet d array row column columns stride body outer_body BODY OUTER)) as SILENT; subst trace.
  pose proof (@normal_statement_execution fe ge locals outer_body
    (@rectangle_outer_normal column columns body outer_body (@runtime_body_quiet d array row column stride body BODY) OUTER)
    le memory E0 after final outcome RUN) as NORMAL; subst outcome.
  split.
  - apply (@flattened_pair_execution fe ge locals outer_body (rectangle_reset column)
      (frontend_counted_loop column columns body) le memory after final OUTER) in RUN.
    destruct (sequence_normal_decode RUN) as [middle [mem1 [RESET INNER]]].
    pose proof (@fixed_temp_execution fe ge locals [column] (rectangle_reset column) stride _ le memory E0 middle mem1 Out_normal
      ltac:(constructor; cbn; auto) ltac:(cbn; intuition) STRIDE RESET) as NEXT.
    unfold loaded_stride_constant_outer, rectangle_outer_body; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact RESET|].
    exact (@runtime_inner_constant fe ge locals d array row column column columns stride body middle mem1 E0 after final Out_normal
      SC BODY NEXT INNER).
  - eapply fixed_temp_execution with (allowed := [column]); [|cbn; intuition|exact STRIDE|exact RUN].
    exact (@rectangle_outer_writes column columns body outer_body (@runtime_body_writes d array row column stride body BODY) OUTER).
Qed.

Theorem loaded_stride_source_constant fe ge locals d array row bound column columns stride body outer_body
  le memory trace after final outcome :
  stride <> row -> stride <> column -> flatten_region body = [runtime_stride_store d array row column stride] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body] ->
  le ! stride = Some (Vint (Int.repr (rectangle_stride d))) ->
  exec_stmt fe ge locals le memory (loaded_rectangle_source row bound outer_body) trace after final outcome ->
  exec_stmt fe ge locals le memory
    (loaded_rectangle_source row bound (loaded_stride_constant_outer d array row column columns)) trace after final outcome.
Proof.
  intros SR SC BODY OUTER STRIDE RUN.
  exact (proj1 (@strict_loop_body_transport fe ge locals row (loaded_bound_test row bound) outer_body
    (loaded_stride_constant_outer d array row column columns) (fun le _ => le ! stride = Some (Vint (Int.repr (rectangle_stride d))))
    (fun before mem tr exit mem' out' LOOKUP BODY_RUN =>
      @loaded_stride_outer_constant fe ge locals d array row column columns stride body outer_body
        before mem tr exit mem' out' SC BODY OUTER LOOKUP BODY_RUN)
    ltac:(intros before mem tr exit mem' out' LOOKUP INC;
      eapply fixed_temp_execution with (allowed := [row]);
      [repeat constructor; cbn; auto|cbn; intuition|exact LOOKUP|exact INC])
    le memory trace after final outcome RUN STRIDE)).
Qed.

Lemma loaded_stride_domain_from_source d fe ge locals le memory array row bound column columns stride body outer_body after final :
  flatten_region body = [runtime_stride_store d array row column stride] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body] ->
  exec_stmt fe ge locals le memory (loaded_rectangle_source row bound outer_body) E0 after final Out_normal ->
  loaded_stride_domain row bound outer_body (Entry ge locals le memory).
Proof.
  intros BODY OUTER SOURCE; split.
  - destruct (@loaded_matrix_entry_test fe ge locals le memory row bound outer_body after final SOURCE) as [flag TEST].
    destruct (loaded_bound_test_facts TEST) as [word [upper [q [qofs [ITER [BOUND [READ FLAG]]]]]]].
    exists word, upper, q, qofs; repeat split; assumption.
  - eapply quiet_source_completion_from_run with (observed := FragmentObservation E0 after final Out_normal);
      [exact (@loaded_stride_source_quiet d array row bound column columns stride body outer_body BODY OUTER)|exact SOURCE].
Qed.

Theorem loaded_stride_domain_constant d array row bound column columns stride body outer_body entry :
  stride <> row -> stride <> column -> flatten_region body = [runtime_stride_store d array row column stride] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body] ->
  loaded_stride_domain row bound outer_body entry ->
  register_equals stride (Int.repr (rectangle_stride d)) tt entry ->
  loaded_rectangle_domain row bound (loaded_stride_constant_outer d array row column columns) entry.
Proof.
  intros SR SC BODY OUTER [ENTRY [observed COMPLETE]] STRIDE; split; [exact ENTRY|].
  destruct entry as [ge locals le memory], observed as [trace after final outcome].
  assert (QUIET := @loaded_stride_source_quiet d array row bound column columns stride body outer_body BODY OUTER).
  pose proof (@quiet_execution_silent _ ge locals le memory _ trace after final outcome
    (COMPLETE (adapter_entry true)) QUIET) as SILENT; subst trace.
  pose proof (@quiet_loop_normal _ ge locals le memory _ _ E0 after final outcome QUIET
    (COMPLETE (adapter_entry true))) as NORMAL; subst outcome.
  exists (FragmentObservation E0 after final Out_normal); intro fe.
  exact (@loaded_stride_source_constant fe ge locals d array row bound column columns stride body outer_body
    le memory E0 after final Out_normal SR SC BODY OUTER STRIDE (COMPLETE fe)).
Qed.

(** Definition of the runtime parameter is established only on an actual
    active outer/inner source path, before any stability assumption. *)
Theorem loaded_stride_active_domains d array row bound column columns stride body outer_body entry :
  column <> columns -> stride <> column -> flatten_region body = [runtime_stride_store d array row column stride] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body] ->
  loaded_stride_domain row bound outer_body entry -> register_equals row Int.zero tt entry ->
  0 < Int.signed (loaded_rectangle_word bound entry) ->
  register_domain columns entry /\
    (0 < Int.signed (temp_word columns (entry_temps entry)) -> register_domain stride entry).
Proof.
  intros CM SC BODY OUTER [[word [upper [q [qofs [ITER [BOUND READ]]]]]] [observed COMPLETE]] ZERO POS.
  destruct entry as [ge locals le memory], observed as [trace after final outcome].
  assert (QUIET := @loaded_stride_source_quiet d array row bound column columns stride body outer_body BODY OUTER).
  pose proof (COMPLETE (adapter_entry true)) as SOURCE.
  pose proof (@quiet_execution_silent _ ge locals le memory _ trace after final outcome SOURCE QUIET) as SILENT; subst trace.
  pose proof (@quiet_loop_normal _ ge locals le memory _ _ E0 after final outcome QUIET SOURCE) as NORMAL; subst outcome.
  cbn [entry_temps entry_memory] in ZERO, BOUND, READ.
  unfold loaded_rectangle_word in POS; cbn [entry_temps entry_memory] in POS; rewrite BOUND, READ in POS.
  assert (LT : Int.lt Int.zero upper = true).
  { unfold Int.lt; change (Int.signed Int.zero) with 0; destruct (zlt 0 (Int.signed upper)); [reflexivity|lia]. }
  assert (ACTIVE : expression_test (loaded_bound_test row bound) (Entry ge locals le memory) true).
  { rewrite <- LT; eapply loaded_bound_test_eval; eassumption. }
  destruct (@strict_active_iteration _ ge locals row (loaded_bound_test row bound) outer_body le memory after final
    (@rectangle_outer_normal column columns body outer_body (@runtime_body_quiet d array row column stride body BODY) OUTER)
    (@loaded_stride_outer_quiet d array row column columns stride body outer_body BODY OUTER) ACTIVE SOURCE)
    as [body_temps [body_memory [next_temps [next_memory [BODY_RUN REST]]]]].
  apply (@flattened_pair_execution _ ge locals outer_body (rectangle_reset column)
    (frontend_counted_loop column columns body) le memory body_temps body_memory OUTER) in BODY_RUN.
  destruct (sequence_normal_decode BODY_RUN) as [reset_temps [reset_memory [RESET INNER]]].
  destruct (rectangle_reset_decode RESET) as [_ [TEMPS [MEMORY _]]]; subst reset_temps reset_memory.
  destruct (frontend_entry_test INNER) as [flag TEST].
  destruct (@counter_test_domain column columns _ flag TEST) as [j [m [J M]]].
  assert (COLS : le ! columns = Some (Vint m)) by (cbn in M; rewrite PTree.gso in M by congruence; exact M).
  split; [exists m; exact COLS|].
  intro M_POS; unfold temp_word in M_POS; cbn [entry_temps] in M_POS; rewrite COLS in M_POS.
  assert (INNER_ACTIVE : expression_test (counter_condition column columns)
    (Entry ge locals (PTree.set column (Vint Int.zero) le) memory) true).
  { replace true with (0 <? Int.signed m) by (apply Z.ltb_lt; exact M_POS).
    apply (@counter_condition_at ge locals _ memory column columns 0 (Int.signed m));
      try exact CM; try apply Int.signed_range; try apply PTree.gss;
      try (change (-2147483648 <= 0 <= 2147483647); lia).
    rewrite PTree.gso by congruence; rewrite Int.repr_signed; exact COLS. }
  assert (FRAME : forall before mem tr exit mem', exec_stmt (adapter_entry true) ge locals before mem body tr exit mem' Out_normal ->
    temp_agree [column;columns] before exit).
  { intros; eapply structured_temp_frame;
      [exact (@runtime_body_writes d array row column stride body BODY)|intros id _ BAD; exact BAD|eassumption]. }
  destruct (@frontend_iteration_decode (adapter_entry true) ge locals _ memory column columns body body_temps body_memory INNER_ACTIVE
    (@normal_statement_execution _ ge locals body (@runtime_body_normal d array row column stride body BODY)) FRAME INNER)
    as [first [first_mem [STORE TAIL]]].
  apply (flattened_singleton_execution BODY) in STORE; inversion STORE; subst.
  match goal with LV : eval_lvalue _ _ _ _ (runtime_stride_lvalue _ _ _ _ _) _ _ _ |- _ =>
    destruct (runtime_stride_lvalue_domain LV) as [step LOOKUP]; exists step;
    cbn in LOOKUP |- *; rewrite PTree.gso in LOOKUP by congruence; exact LOOKUP end.
Qed.

Print Assumptions loaded_stride_outer_constant.
Print Assumptions loaded_stride_product_bound.
Print Assumptions loaded_stride_source_constant.
Print Assumptions loaded_stride_domain_from_source.
Print Assumptions loaded_stride_domain_constant.
Print Assumptions loaded_stride_active_domains.
