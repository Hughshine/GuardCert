From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import CompCertStoreSchedule RectangularSchedule RectangularIteration
  ClightCondition ClightNoWrap ClightTempFrame ClightFiniteRegion ClightStraightLine
  ClightLoopSyntax ClightFrontendLoopProtocol ClightRectangularStore ClightRectangularGuard
  ClightRectangularLoops ClightRectangularRegion ClightRegionProgress ClightCountedLoop
  ClightFrontendRegion ClightZeroTrip ClightFramedLoop ClightLoopExecution.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles
  GuardMemoryPolyhedral GuardMemoryLoops GuardMemoryArrayBackend GuardMemoryArrayFamilyBackend
  GuardMemorySequenceLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Inductive array_family_physical ge locals array i j : list rectangle_shape -> mem -> mem -> Prop :=
| array_family_physical_nil : forall memory, array_family_physical ge locals array i j [] memory memory
| array_family_physical_cons : forall shape shapes before middle final block,
    rect_array_binding shape ge locals array block ->
    store_action_run (rectangle_action block (rectangle_stride shape) (rect_payload shape) (i,j)) before middle ->
    array_family_physical ge locals array i j shapes middle final ->
    array_family_physical ge locals array i j (shape::shapes) before final.

Lemma array_family_body_normal shapes array row column body :
  flatten_region body = map (fun shape => rect_store shape array row column) shapes -> normal_statement body = true.
Proof. intro FLAT; apply flatten_normal_certificate; rewrite FLAT; apply Forall_map,Forall_forall; intros; reflexivity. Qed.
Lemma array_family_body_quiet shapes array row column body :
  flatten_region body = map (fun shape => rect_store shape array row column) shapes -> quiet_statement body = true.
Proof. intro FLAT; apply flatten_quiet_certificate; rewrite FLAT; apply Forall_map,Forall_forall; intros; reflexivity. Qed.
Lemma array_family_body_writes shapes array row column body :
  flatten_region body = map (fun shape => rect_store shape array row column) shapes -> writes_only [] body.
Proof. intro FLAT; apply flatten_writes_certificate; rewrite FLAT; apply Forall_map,Forall_forall; intros; constructor. Qed.
Lemma array_family_tail_inverse base shapes array row column fe ge locals i j temps memory after final :
  rectangle_layout_valid base -> Forall (same_array_layout base) shapes ->
  0 <= i*rectangle_stride base+j < rectangle_extent base ->
  temps ! row = Some (Vint (Int.repr i)) -> temps ! column = Some (Vint (Int.repr j)) ->
  tail_execution fe ge locals (map (fun shape => rect_store shape array row column) shapes)
    temps memory after final -> array_family_physical ge locals array i j shapes memory final /\ after = temps.
Proof.
  intros VALID LAYOUTS INDEX ROW COLUMN.
  revert temps memory after final ROW COLUMN; induction LAYOUTS as [|shape shapes LAYOUT LAYOUTS IH];
    intros temps memory after final ROW COLUMN RUN; cbn in RUN; inversion RUN; subst.
  - split; [constructor|reflexivity].
  - destruct LAYOUT as [EXTENT STRIDE].
    match goal with HEAD : exec_stmt _ _ _ _ _ (rect_store _ _ _ _) _ _ _ _ |- _ =>
      destruct (@rect_store_inverse shape ltac:(eapply same_array_layout_valid; [exact VALID|split; assumption])
        fe ge locals temps memory array row column i j E0 _ _ Out_normal ROW COLUMN
        ltac:(rewrite EXTENT,STRIDE; exact INDEX) HEAD)
        as [block [ARRAY [_ [TEMPS [_ STORE]]]]]; subst end.
    match goal with TAIL : tail_execution _ _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ _ _ ROW COLUMN TAIL) as [REST EXIT] end.
    split; [econstructor; eauto|exact EXIT].
Qed.
Lemma array_family_binding base shapes ge locals array i j before after :
  Forall (same_array_layout base) shapes -> shapes <> [] ->
  array_family_physical ge locals array i j shapes before after -> exists block, rect_array_binding base ge locals array block.
Proof.
  intros LAYOUTS NONEMPTY RUN; inversion RUN; subst; [contradiction|].
  inversion LAYOUTS; subst.
  match goal with LAYOUT : same_array_layout base ?shape,ARRAY : rect_array_binding ?shape _ _ _ ?block |- _ =>
    destruct LAYOUT as [EXTENT STRIDE]; exists block;
    unfold rect_array_binding,rect_array_type in *; rewrite EXTENT in ARRAY; exact ARRAY end.
Qed.


Lemma array_family_point_execution base shapes ge locals array logical_array block i j :
  Forall (same_array_layout base) shapes -> rect_array_binding base ge locals array block ->
  0 <= i*rectangle_stride base+j < rectangle_extent base ->
  forall before after,
  (array_family_physical ge locals array i j shapes before after <->
   memory_sequence_point (map (fun shape => rect_memory_write shape logical_array) shapes) i j
     (RuntimeState (flat_array_locations logical_array block (rectangle_extent base)) before)
     (RuntimeState (flat_array_locations logical_array block (rectangle_extent base)) after)).
Proof.
  intros LAYOUTS ARRAY INDEX; induction LAYOUTS as [|shape shapes LAYOUT LAYOUTS IH];
    intros before after; unfold memory_sequence_point; cbn [map]; split; intro RUN.
  - inversion RUN; subst; constructor.
  - inversion RUN; subst; constructor.
  - inversion RUN; subst; destruct LAYOUT as [EXTENT STRIDE].
    match goal with BINDING : rect_array_binding shape _ _ _ ?other |- _ =>
      assert (SAME : other = block) by
        (unfold rect_array_binding,rect_array_type in BINDING; rewrite EXTENT in BINDING;
         eapply rect_array_binding_unique; [exact BINDING|exact ARRAY]); subst other end.
    eapply Iter.IProgress with (st2 := RuntimeState
      (flat_array_locations logical_array block (rectangle_extent base)) middle).
    + pose proof (@rect_memory_write_execution shape logical_array block i j before middle
        ltac:(rewrite EXTENT,STRIDE; exact INDEX)) as POINT.
      rewrite EXTENT in POINT; apply (proj2 POINT); eassumption.
    + apply IH; eassumption.
  - inversion RUN; subst; destruct LAYOUT as [EXTENT STRIDE].
    match goal with POINT : memory_point _ _ _ _ ?middle |- _ =>
      destruct middle as [locations middle_memory];
      assert (LOCATIONS : locations = flat_array_locations logical_array block (rectangle_extent base))
        by (exact (@memory_point_locations _ i j _ _ POINT)); subst locations end.
    eapply array_family_physical_cons with (block := block) (middle := middle_memory).
    + unfold rect_array_binding,rect_array_type; rewrite EXTENT; exact ARRAY.
    + pose proof (@rect_memory_write_execution shape logical_array block i j before middle_memory
        ltac:(rewrite EXTENT,STRIDE; exact INDEX)) as POINT.
      rewrite EXTENT in POINT; apply (proj1 POINT); eassumption.
    + apply IH; eassumption.
Qed.

Lemma array_family_source_guard_domain shapes fe ge locals le memory array row bound column inner_bound body outer_body le' final :
  row <> bound -> row <> column -> bound <> column -> column <> inner_bound ->
  flatten_region body = map (fun shape => rect_store shape array row column) shapes ->
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
    (@array_family_body_writes shapes array row column body BODY) OUTER).
  assert (FRAME : forall before mem tr after mem',
    exec_stmt fe ge locals before mem outer_body tr after mem' Out_normal -> temp_agree [row;bound] before after).
  { intros; eapply structured_temp_frame; [exact WRITES|cbn; intros id LIVE WRITE; intuition congruence|eassumption]. }
  destruct (@frontend_iteration_decode fe ge locals le memory row bound outer_body le' final TEST0
    (@normal_statement_execution fe ge locals outer_body
      (@rectangle_outer_normal column inner_bound body outer_body (@array_family_body_quiet shapes array row column body BODY) OUTER)) FRAME RUN)
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

Section SOURCE.
Variable base : rectangle_shape.
Hypothesis VALID : rectangle_layout_valid base.
Variable shapes : list rectangle_shape.
Hypothesis LAYOUTS : Forall (same_array_layout base) shapes.
Hypothesis NONEMPTY : shapes <> [].
Variable array row bound column inner_bound : ident.
Variable body outer_body : statement.
Hypothesis RN : row <> bound.
Hypothesis RC : row <> column.
Hypothesis NC : bound <> column.
Hypothesis RM : row <> inner_bound.
Hypothesis CM : column <> inner_bound.
Hypothesis BODY : flatten_region body = map (fun shape => rect_store shape array row column) shapes.
Hypothesis OUTER : flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column inner_bound body].

Lemma array_family_source_clight_iterations fe ge locals le memory after final rows columns :
  le ! row = Some (Vint Int.zero) -> le ! bound = Some (Vint (Int.repr (Z.of_nat rows))) ->
  le ! inner_bound = Some (Vint (Int.repr (Z.of_nat columns))) ->
  signed_range (Z.of_nat rows) -> signed_range (Z.of_nat columns) ->
  0 < Z.of_nat rows <= rectangle_outer_limit base -> 0 < Z.of_nat columns <= rectangle_stride base ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 after final Out_normal ->
  rectangular_iterations (fun i j => array_family_physical ge locals array i j shapes) rows columns memory final /\
  after = PTree.set row (Vint (Int.repr (Z.of_nat rows)))
    (PTree.set column (Vint (Int.repr (Z.of_nat columns))) le).
Proof.
  intros ZERO BOUND INNER NS MS NB MB SOURCE.
  assert (POS : rows <> O) by (intro EQ; rewrite EQ in NB; cbn in NB; lia).
  apply (@rectangle_source_decode fe ge locals row bound column inner_bound body outer_body
    (fun i j => array_family_physical ge locals array i j shapes) rows columns RN RC NC RM CM POS NS MS
    (@array_family_body_normal shapes array row column body BODY)
    (@array_family_body_quiet shapes array row column body BODY)
    (@array_family_body_writes shapes array row column body BODY) OUTER).
  - intros i j temps before after' final' I J ROW COLUMN RUN.
    apply flatten_region_execution in RUN; rewrite BODY in RUN.
    exact (@array_family_tail_inverse base shapes array row column fe ge locals i j temps before after' final'
      VALID LAYOUTS ltac:(apply rectangle_point_bound with (N := Z.of_nat rows) (M := Z.of_nat columns); assumption)
      ROW COLUMN RUN).
  - exact ZERO.
  - exact BOUND.
  - exact INNER.
  - exact SOURCE.
Qed.

Theorem array_family_source_clight_decode fe ge locals le memory after final rows columns logical_array :
  le ! row = Some (Vint Int.zero) -> le ! bound = Some (Vint (Int.repr (Z.of_nat rows))) ->
  le ! inner_bound = Some (Vint (Int.repr (Z.of_nat columns))) ->
  signed_range (Z.of_nat rows) -> signed_range (Z.of_nat columns) ->
  0 < Z.of_nat rows <= rectangle_outer_limit base -> 0 < Z.of_nat columns <= rectangle_stride base ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 after final Out_normal ->
  exists block, rect_array_binding base ge locals array block /\
    L.loop_semantics (memory_rectangle_sequence (map (fun shape => rect_memory_write shape logical_array) shapes))
      [Z.of_nat rows;Z.of_nat columns]
      (RuntimeState (flat_array_locations logical_array block (rectangle_extent base)) memory)
      (RuntimeState (flat_array_locations logical_array block (rectangle_extent base)) final) /\
    after = PTree.set row (Vint (Int.repr (Z.of_nat rows)))
      (PTree.set column (Vint (Int.repr (Z.of_nat columns))) le).
Proof.
  intros ZERO BOUND INNER NS MS NB MB RUN.
  destruct (@array_family_source_clight_iterations fe ge locals le memory after final rows columns
    ZERO BOUND INNER NS MS NB MB RUN) as [ITER EXIT].
  assert (POS : rows <> O) by (intro EQ; rewrite EQ in NB; cbn in NB; lia).
  assert (POS' : columns <> O) by (intro EQ; rewrite EQ in MB; cbn in MB; lia).
  destruct (@rectangular_first mem (fun i j => array_family_physical ge locals array i j shapes)
    rows columns memory final POS POS' ITER) as [first HEAD].
  destruct (@array_family_binding base shapes ge locals array 0 0 memory first LAYOUTS NONEMPTY HEAD) as [block ARRAY].
  exists block; split; [exact ARRAY|split; [|exact EXIT]].
  apply (proj1 (@memory_rectangle_sequence_lift
    (flat_array_locations logical_array block (rectangle_extent base))
    (map (fun shape => rect_memory_write shape logical_array) shapes)
    (fun i j => array_family_physical ge locals array i j shapes) rows columns memory final
    ltac:(intros i j before after' I J; apply array_family_point_execution; [exact LAYOUTS|exact ARRAY|];
      apply rectangle_point_bound with (N := Z.of_nat rows) (M := Z.of_nat columns); assumption))).
  exact ITER.
Qed.
End SOURCE.
Print Assumptions array_family_source_clight_iterations.
Print Assumptions array_family_source_clight_decode.
