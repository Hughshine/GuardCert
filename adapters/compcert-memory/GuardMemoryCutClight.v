From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import CompCertStoreSchedule RectangularSchedule ClightCondition ClightPureExpr ClightNoWrap ClightTempFrame
  ClightRectangularStore ClightRectangularGuard ClightRectangularRegion
  ClightRectangularLoops ClightLoopSyntax ClightStraightLine ClightFrontendLoopProtocol
  ClightRegionProgress ClightCountedLoop ClightTempFootprint ClightLoopExecution RectangularIteration
  ClightFrontendRegion ClightZeroTrip ClightCountedProtocol ClightParametricLoops ClightFramedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles
  GuardMemoryLoops GuardMemoryArrayBackend GuardMemoryConditionalLoops GuardMemoryCutExecution.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_cut_expression a b :=
  L.make_sum (L.make_mult a (L.Var 1)) (L.make_mult b (L.Var 0)).
Lemma memory_cut_expression_at a b j i :
  L.eval_expr [j;i] (memory_cut_expression a b) = a*i+b*j.
Proof. unfold memory_cut_expression; rewrite L.make_sum_correct,!L.make_mult_correct; reflexivity. Qed.
Definition memory_cut_operand_bounds d :=
  [MemoryNested.A.Interval 0 (rectangle_stride d-1);
   MemoryNested.A.Interval 0 (rectangle_outer_limit d-1)].
Definition compile_memory_cut_condition d row column a b c : option expr :=
  match MemoryNested.A.compile_expr [column;row] (memory_cut_operand_bounds d) (memory_cut_expression a b),
        MemoryNested.A.checked (MemoryNested.A.Interval c c) with
  | Some (expression,_),Some _ => Some (Ebinop Ole expression (Econst_int (Int.repr c) type_int32s) type_int32s)
  | _,_ => None end.
Definition memory_cut_statement d array row column condition :=
  Sifthenelse condition (Ssequence Sskip (rect_store d array row column)) Sskip.
Definition memory_cut_flag a b c i j := (a*i+b*j <=? c).

Lemma memory_cut_operand_view row column i j temps :
  signed_range i -> signed_range j ->
  temps ! row = Some (Vint (Int.repr i)) -> temps ! column = Some (Vint (Int.repr j)) ->
  MemoryNested.A.typed_view [column;row] [j;i] temps.
Proof.
  intros IR JR ROW COLUMN index id INDEX.
  destruct index as [|[|index]]; cbn in INDEX; try rewrite nth_error_nil in INDEX;
    try discriminate; inversion INDEX; subst id.
  - exists (Int.repr j); split; [exact COLUMN|cbn; rewrite Int.signed_repr by exact JR; reflexivity].
  - exists (Int.repr i); split; [exact ROW|cbn; rewrite Int.signed_repr by exact IR; reflexivity].
Qed.
Lemma memory_cut_operand_within d i j :
  0 <= i < rectangle_outer_limit d -> 0 <= j < rectangle_stride d ->
  MemoryNested.A.env_within (memory_cut_operand_bounds d) [j;i].
Proof.
  intros I J index interval INDEX; unfold memory_cut_operand_bounds in INDEX.
  destruct index as [|[|index]]; cbn in INDEX; try rewrite nth_error_nil in INDEX;
    try discriminate; inversion INDEX; subst interval; unfold MemoryNested.A.contains; cbn; lia.
Qed.

Lemma compile_memory_cut_condition_pure d row column a b c condition :
  compile_memory_cut_condition d row column a b c = Some condition -> pure_scalar condition.
Proof.
  unfold compile_memory_cut_condition,MemoryNested.A.compile_expr.
  destruct (MemoryNested.A.analyze (memory_cut_operand_bounds d) (memory_cut_expression a b)); try discriminate.
  destruct (MemoryNested.A.lower_expr [column;row] (memory_cut_expression a b)) as [expression|] eqn:LOWER;
    try discriminate.
  destruct (MemoryNested.A.checked (MemoryNested.A.Interval c c)); try discriminate.
  intro EQ; inversion EQ; subst condition; constructor; [|constructor].
  eapply MemoryNested.A.lower_expr_pure; exact LOWER.
Qed.

Lemma compile_memory_cut_condition_evaluation d row column a b c condition ge locals temps memory i j :
  rectangle_layout_valid d ->
  compile_memory_cut_condition d row column a b c = Some condition ->
  0 <= i < rectangle_outer_limit d -> 0 <= j < rectangle_stride d ->
  temps ! row = Some (Vint (Int.repr i)) -> temps ! column = Some (Vint (Int.repr j)) ->
  expression_test condition (Entry ge locals temps memory) (memory_cut_flag a b c i j).
Proof.
  intros VALID COMPILE I J ROW COLUMN.
  unfold compile_memory_cut_condition in COMPILE.
  destruct (MemoryNested.A.compile_expr [column;row] (memory_cut_operand_bounds d) (memory_cut_expression a b))
    as [[expression interval]|] eqn:EXPRESSION; try discriminate.
  destruct (MemoryNested.A.checked (MemoryNested.A.Interval c c)) as [limit|] eqn:LIMIT; try discriminate.
  inversion COMPILE; subst condition.
  pose proof (@rectangle_limits d VALID) as [[LOLOW LOHIGH] [[STRLOW STRHIGH] REST]].
  assert (IR : signed_range i) by (unfold signed_range; change Int.min_signed with (-2147483648) in *; lia).
  assert (JR : signed_range j) by (unfold signed_range; change Int.min_signed with (-2147483648) in *; lia).
  destruct (@MemoryNested.A.compile_expr_sound [column;row] (memory_cut_operand_bounds d)
    (memory_cut_expression a b) expression interval [j;i] temps EXPRESSION
    (@memory_cut_operand_within d i j I J) (@memory_cut_operand_view row column i j temps IR JR ROW COLUMN))
    as [TYPE [RANGE [WITHIN EVALUATION]]].
  rewrite memory_cut_expression_at in RANGE,EVALUATION.
  apply MemoryNested.A.checked_sound in LIMIT as [EQ [_ [CLOW CHIGH]]]; cbn in CLOW,CHIGH.
  unfold expression_test,memory_cut_flag; cbn [entry_ge entry_env entry_temps entry_memory].
  exists (Val.of_bool (a*i+b*j <=? c)); split.
  - eapply eval_Ebinop; [apply EVALUATION|constructor|].
    rewrite TYPE; cbn [typeof].
    change (Some (Val.of_bool (Int.cmp Cle (Int.repr (a*i+b*j)) (Int.repr c))) =
      Some (Val.of_bool (a*i+b*j <=? c))).
    rewrite MemoryNested.A.signed_le_exact; [reflexivity|exact RANGE|split; assumption].
  - destruct (_ <=? _); reflexivity.
Qed.

Lemma memory_cut_statement_inverse d array row column condition a b c i j fe ge locals temps memory after final :
  rectangle_layout_valid d -> compile_memory_cut_condition d row column a b c = Some condition ->
  0 <= i < rectangle_outer_limit d -> 0 <= j < rectangle_stride d ->
  0 <= i*rectangle_stride d+j < rectangle_extent d ->
  temps ! row = Some (Vint (Int.repr i)) -> temps ! column = Some (Vint (Int.repr j)) ->
  exec_stmt fe ge locals temps memory (memory_cut_statement d array row column condition) E0 after final Out_normal ->
  (if memory_cut_flag a b c i j then
    exists block, rect_array_binding d ge locals array block /\
      store_action_run (rectangle_action block (rectangle_stride d) (rect_payload d) (i,j)) memory final
   else final = memory) /\ after = temps.
Proof.
  intros VALID COMPILE I J INDEX ROW COLUMN RUN; unfold memory_cut_statement in RUN.
  inversion RUN; subst.
  match goal with EV : eval_expr _ _ _ _ condition ?value, BOOL : bool_val _ _ _ = Some ?flag |- _ =>
    assert (CHECK : expression_test condition (Entry ge locals temps memory) flag)
      by (exists value; split; assumption);
    assert (KNOWN := @compile_memory_cut_condition_evaluation d row column a b c condition ge locals temps memory
      i j VALID COMPILE I J ROW COLUMN);
    assert (SAME : flag = memory_cut_flag a b c i j)
      by (eapply pure_test_determinate; [eapply compile_memory_cut_condition_pure; exact COMPILE|exact CHECK|exact KNOWN]);
    destruct flag; cbn in *
  end.
  - rewrite <- SAME.
    match goal with SEQ : exec_stmt _ _ _ _ _ (Ssequence Sskip _) _ _ _ _ |- _ =>
      destruct (sequence_normal_decode SEQ) as [middle [middle_memory [SKIP STORE]]];
      inversion SKIP; subst middle middle_memory end.
    match goal with STORE : exec_stmt _ _ _ _ _ (rect_store _ _ _ _) _ _ _ _ |- _ =>
      destruct (@rect_store_inverse d VALID fe ge locals temps memory array row column i j E0 after final Out_normal
        ROW COLUMN INDEX STORE) as [block [BINDING [_ [TEMPS [_ EXEC]]]]] end.
    split; [exists block; auto|exact TEMPS].
  - rewrite <- SAME.
    match goal with SKIP : exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ => inversion SKIP; subst end; auto.
Qed.

Print Assumptions compile_memory_cut_condition_evaluation.
Print Assumptions memory_cut_statement_inverse.

Lemma memory_cut_body_normal d array row column condition body :
  flatten_region body = [memory_cut_statement d array row column condition] -> normal_statement body = true.
Proof. intro FLAT; apply flatten_normal_certificate; rewrite FLAT; repeat constructor. Qed.
Lemma memory_cut_body_quiet d array row column condition body :
  flatten_region body = [memory_cut_statement d array row column condition] -> quiet_statement body = true.
Proof. intro FLAT; apply flatten_quiet_certificate; rewrite FLAT; repeat constructor. Qed.
Lemma memory_cut_body_writes d array row column condition body :
  flatten_region body = [memory_cut_statement d array row column condition] -> writes_only [] body.
Proof. intro FLAT; apply flatten_writes_certificate; rewrite FLAT; repeat constructor. Qed.
Lemma memory_cut_source_guard_domain d condition fe ge locals le memory array row bound column inner_bound body outer_body le' final :
  row <> bound -> row <> column -> bound <> column -> column <> inner_bound ->
  flatten_region body = [memory_cut_statement d array row column condition] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column inner_bound body] ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 le' final Out_normal ->
  rectangle_guard_domain row bound inner_bound (Entry ge locals le memory).
Proof.
  intros RN RC NC CM BODY OUTER RUN.
  destruct (@frontend_entry_test fe ge locals le memory row bound outer_body le' final RUN) as [flag TEST].
  destruct (@counter_test_domain row bound (Entry ge locals le memory) flag TEST)
    as [x [upper [X UP]]].
  cbn [entry_temps] in X, UP.
  split; [exists x; exact X|split; [exists upper; exact UP|]].
  intros ZERO POS; change (le ! row = Some (Vint Int.zero)) in ZERO.
  cbn [entry_temps] in POS; unfold temp_word in POS; rewrite UP in POS.
  assert (UP' : le ! bound = Some (Vint (Int.repr (Int.signed upper)))).
  { rewrite Int.repr_signed; exact UP. }
  assert (TEST0 : expression_test (counter_condition row bound) (Entry ge locals le memory) true).
  { replace true with (0 <? Int.signed upper) by (apply Z.ltb_lt; exact POS).
    apply (@counter_condition_at ge locals le memory row bound 0 (Int.signed upper)); auto.
    - change (-2147483648 <= 0 <= 2147483647); lia.
    - apply Int.signed_range. }
  assert (WRITES := @rectangle_outer_writes column inner_bound body outer_body
    (@memory_cut_body_writes d array row column condition body BODY) OUTER).
  assert (FRAME : forall before mem tr after mem',
    exec_stmt fe ge locals before mem outer_body tr after mem' Out_normal -> temp_agree [row;bound] before after).
  { intros; eapply structured_temp_frame; [exact WRITES|cbn; intros id LIVE WRITE; intuition congruence|eassumption]. }
  destruct (@frontend_iteration_decode fe ge locals le memory row bound outer_body le' final TEST0
    (@normal_statement_execution fe ge locals outer_body
      (@rectangle_outer_normal column inner_bound body outer_body (@memory_cut_body_quiet d array row column condition body BODY) OUTER)) FRAME RUN)
    as [body_temps [body_memory [BODY_RUN REST]]].
  apply (@flattened_pair_execution fe ge locals outer_body (rectangle_reset column)
    (frontend_counted_loop column inner_bound body) le memory body_temps body_memory OUTER) in BODY_RUN.
  destruct (sequence_normal_decode BODY_RUN) as [reset_temps [reset_memory [RESET INNER]]].
  destruct (rectangle_reset_decode RESET) as [_ [TEMPS [MEMORY _]]]; subst reset_temps reset_memory.
  destruct (@frontend_entry_test fe ge locals _ memory column inner_bound body body_temps body_memory INNER)
    as [inner_flag INNER_TEST].
  destruct (@counter_test_domain column inner_bound _ inner_flag INNER_TEST) as [j [m [J M]]].
  exists m; cbn in M |- *; rewrite PTree.gso in M by congruence; exact M.
Qed.


Definition memory_cut_physical_any d ge locals array a b c i j before after :=
  if memory_cut_flag a b c i j then
    exists block, rect_array_binding d ge locals array block /\
      store_action_run (rectangle_action block (rectangle_stride d) (rect_payload d) (i,j)) before after
  else after = before.
Definition memory_cut_physical d block a b c i j before after :=
  if memory_cut_flag a b c i j then
    store_action_run (rectangle_action block (rectangle_stride d) (rect_payload d) (i,j)) before after
  else after = before.

Section CUT_SOURCE.
Variable d : rectangle_shape.
Hypothesis VALID : rectangle_layout_valid d.
Variable a b c : Z.
Variable condition : expr.
Variable array row bound column inner_bound : ident.
Hypothesis COMPILE : compile_memory_cut_condition d row column a b c = Some condition.
Variable body outer_body : statement.
Hypothesis RN : row <> bound.
Hypothesis RC : row <> column.
Hypothesis NC : bound <> column.
Hypothesis RM : row <> inner_bound.
Hypothesis CM : column <> inner_bound.
Hypothesis BODY : flatten_region body = [memory_cut_statement d array row column condition].
Hypothesis OUTER : flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column inner_bound body].

Lemma memory_cut_source_clight_iterations fe ge locals le memory le' final rows columns :
  le ! row = Some (Vint Int.zero) -> le ! bound = Some (Vint (Int.repr (Z.of_nat rows))) ->
  le ! inner_bound = Some (Vint (Int.repr (Z.of_nat columns))) ->
  signed_range (Z.of_nat rows) -> signed_range (Z.of_nat columns) ->
  0 < Z.of_nat rows <= rectangle_outer_limit d -> 0 < Z.of_nat columns <= rectangle_stride d ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 le' final Out_normal ->
  rectangular_iterations (memory_cut_physical_any d ge locals array a b c) rows columns memory final /\
  le' = PTree.set row (Vint (Int.repr (Z.of_nat rows)))
    (PTree.set column (Vint (Int.repr (Z.of_nat columns))) le).
Proof.
  intros ZERO BOUND INNER NS MS NB MB SOURCE.
  assert (POS : rows <> O) by (intro EQ; rewrite EQ in NB; cbn in NB; lia).
  apply (@rectangle_source_decode fe ge locals row bound column inner_bound body outer_body
    (memory_cut_physical_any d ge locals array a b c) rows columns RN RC NC RM CM POS NS MS
    (@memory_cut_body_normal d array row column condition body BODY)
    (@memory_cut_body_quiet d array row column condition body BODY)
    (@memory_cut_body_writes d array row column condition body BODY) OUTER).
  - intros i j temps before after' final' I J ROW COLUMN RUN.
    apply (@flattened_singleton_execution fe ge locals body (memory_cut_statement d array row column condition)
      temps before after' final' BODY) in RUN.
    exact (@memory_cut_statement_inverse d array row column condition a b c i j fe ge locals temps before after' final'
      VALID COMPILE ltac:(lia) ltac:(lia)
      ltac:(apply rectangle_point_bound with (N := Z.of_nat rows) (M := Z.of_nat columns); assumption)
      ROW COLUMN RUN).
  - exact ZERO.
  - exact BOUND.
  - exact INNER.
  - exact SOURCE.
Qed.

Theorem memory_cut_source_clight_decode fe ge locals le memory le' final rows columns logical_array :
  0 <= c ->
  le ! row = Some (Vint Int.zero) -> le ! bound = Some (Vint (Int.repr (Z.of_nat rows))) ->
  le ! inner_bound = Some (Vint (Int.repr (Z.of_nat columns))) ->
  signed_range (Z.of_nat rows) -> signed_range (Z.of_nat columns) ->
  0 < Z.of_nat rows <= rectangle_outer_limit d -> 0 < Z.of_nat columns <= rectangle_stride d ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 le' final Out_normal ->
  exists block, rect_array_binding d ge locals array block /\
    L.loop_semantics (memory_cut_source_loop (rect_memory_write d logical_array) a b c)
      [Z.of_nat rows;Z.of_nat columns]
      (RuntimeState (flat_array_locations logical_array block (rectangle_extent d)) memory)
      (RuntimeState (flat_array_locations logical_array block (rectangle_extent d)) final) /\
    le' = PTree.set row (Vint (Int.repr (Z.of_nat rows)))
      (PTree.set column (Vint (Int.repr (Z.of_nat columns))) le).
Proof.
  intros C ZERO BOUND INNER NS MS NB MB SOURCE.
  destruct (@memory_cut_source_clight_iterations fe ge locals le memory le' final rows columns
    ZERO BOUND INNER NS MS NB MB SOURCE) as [ITER EXIT].
  assert (POS : rows <> O) by (intro EQ; rewrite EQ in NB; cbn in NB; lia).
  assert (POS' : columns <> O) by (intro EQ; rewrite EQ in MB; cbn in MB; lia).
  destruct (@rectangular_first mem (memory_cut_physical_any d ge locals array a b c)
    rows columns memory final POS POS' ITER) as [first FIRST].
  unfold memory_cut_physical_any,memory_cut_flag in FIRST.
  replace (a*0+b*0 <=? c) with true in FIRST by (symmetry; apply Z.leb_le; lia).
  destruct FIRST as [block [ARRAY STORE]].
  exists block; split; [exact ARRAY|split; [|exact EXIT]].
  apply (proj1 (@memory_cut_rectangle_lift (flat_array_locations logical_array block (rectangle_extent d))
    (rect_memory_write d logical_array) (memory_cut_physical d block a b c) a b c rows columns memory final
    ltac:(intros i j before after I J; unfold memory_cut_physical,memory_cut_point,memory_cut_flag;
      destruct (a*i+b*j <=? c); [symmetry; apply rect_memory_write_execution;
        apply rectangle_point_bound with (N := Z.of_nat rows) (M := Z.of_nat columns); assumption|
        split; intro EQ; [subst; reflexivity|inversion EQ; reflexivity]]))).
  eapply rectangular_iterations_map; [|exact ITER].
  intros i j before after STEP; unfold memory_cut_physical_any,memory_cut_physical in *.
  destruct (memory_cut_flag a b c i j); [|exact STEP].
  destruct STEP as [other [BINDING RUN]].
  assert (SAME : other = block) by (eapply rect_array_binding_unique; eauto); subst other; exact RUN.
Qed.
End CUT_SOURCE.
Print Assumptions memory_cut_source_clight_decode.
