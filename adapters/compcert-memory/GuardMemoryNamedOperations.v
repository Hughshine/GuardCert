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
  GuardMemorySequenceLoops GuardMemoryClightRectangles GuardMemoryValidatedRectangles.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Record named_array_operation := NamedArrayOperation {
  named_operation_mode : rectangle_memory_mode;
  named_operation_shape : rectangle_shape;
  named_operation_array : ident
}.
Definition named_operation_layout base (operation : named_array_operation) := same_array_layout base (named_operation_shape operation).
Definition named_operation_statement row column (operation : named_array_operation) :=
  mode_statement (named_operation_mode operation) (named_operation_shape operation) (named_operation_array operation) row column.
Definition named_operation_instruction (operation : named_array_operation) :=
  mode_instruction (named_operation_mode operation) (named_operation_shape operation) (named_operation_array operation).
Inductive named_array_operations_physical ge locals i j : list named_array_operation -> mem -> mem -> Prop :=
| named_array_operations_physical_nil : forall memory, named_array_operations_physical ge locals i j [] memory memory
| named_array_operations_physical_cons : forall operation operations before middle final block,
    rect_array_binding (named_operation_shape operation) ge locals (named_operation_array operation) block ->
    mode_physical (named_operation_mode operation) (named_operation_shape operation) block i j before middle ->
    named_array_operations_physical ge locals i j operations middle final ->
    named_array_operations_physical ge locals i j (operation::operations) before final.
Lemma named_array_operations_body_normal operations row column body :
  flatten_region body = map (named_operation_statement row column) operations -> normal_statement body = true.
Proof.
  intro FLAT; apply flatten_normal_certificate; rewrite FLAT; apply Forall_map,Forall_forall;
    intros [mode shape array] MEMBER; apply mode_normal.
Qed.
Lemma named_array_operations_body_quiet operations row column body :
  flatten_region body = map (named_operation_statement row column) operations -> quiet_statement body = true.
Proof.
  intro FLAT; apply flatten_quiet_certificate; rewrite FLAT; apply Forall_map,Forall_forall;
    intros [mode shape array] MEMBER; apply mode_quiet.
Qed.
Lemma named_array_operations_body_writes operations row column body :
  flatten_region body = map (named_operation_statement row column) operations -> writes_only [] body.
Proof.
  intro FLAT; apply flatten_writes_certificate; rewrite FLAT; apply Forall_map,Forall_forall;
    intros [mode shape array] MEMBER; apply mode_writes.
Qed.
Lemma named_array_operations_tail_inverse base operations row column fe ge locals i j temps memory after final :
  rectangle_layout_valid base -> Forall (named_operation_layout base) operations ->
  0 <= i*rectangle_stride base+j < rectangle_extent base ->
  0 <= i*rectangle_stride base < rectangle_extent base ->
  temps ! row = Some (Vint (Int.repr i)) -> temps ! column = Some (Vint (Int.repr j)) ->
  tail_execution fe ge locals (map (named_operation_statement row column) operations)
    temps memory after final -> named_array_operations_physical ge locals i j operations memory final /\ after = temps.
Proof.
  intros VALID LAYOUTS INDEX READ_INDEX ROW COLUMN.
  revert temps memory after final ROW COLUMN; induction LAYOUTS as [|[mode shape array] operations LAYOUT LAYOUTS IH];
    intros temps memory after final ROW COLUMN RUN; cbn in RUN; inversion RUN; subst.
  - split; [constructor|reflexivity].
  - destruct LAYOUT as [EXTENT STRIDE]; cbn in EXTENT,STRIDE.
    match goal with HEAD : exec_stmt _ _ _ _ _ (named_operation_statement _ _ _) _ _ _ _ |- _ =>
      destruct (@mode_clight_inverse_any mode shape
        ltac:(eapply same_array_layout_valid; [exact VALID|split; assumption])
        fe ge locals array row column i j temps memory _ _
        ltac:(rewrite EXTENT,STRIDE; exact INDEX) ltac:(rewrite EXTENT,STRIDE; exact READ_INDEX)
        ROW COLUMN HEAD) as [[block [ARRAY POINT]] TEMPS]; subst end.
    match goal with TAIL : tail_execution _ _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ _ _ ROW COLUMN TAIL) as [REST EXIT] end.
    split; [econstructor; eauto|exact EXIT].
Qed.
Lemma named_array_operations_source_guard_domain operations fe ge locals le memory row bound column inner_bound body outer_body le' final :
  row <> bound -> row <> column -> bound <> column -> column <> inner_bound ->
  flatten_region body = map (named_operation_statement row column) operations ->
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
    (@named_array_operations_body_writes operations row column body BODY) OUTER).
  assert (FRAME : forall before mem tr after mem',
    exec_stmt fe ge locals before mem outer_body tr after mem' Out_normal -> temp_agree [row;bound] before after).
  { intros; eapply structured_temp_frame; [exact WRITES|cbn; intros id LIVE WRITE; intuition congruence|eassumption]. }
  destruct (@frontend_iteration_decode fe ge locals le memory row bound outer_body le' final TEST0
    (@normal_statement_execution fe ge locals outer_body
      (@rectangle_outer_normal column inner_bound body outer_body (@named_array_operations_body_quiet operations row column body BODY) OUTER)) FRAME RUN)
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
Variable operations : list named_array_operation.
Hypothesis LAYOUTS : Forall (named_operation_layout base) operations.
Hypothesis NONEMPTY : operations <> [].
Variable row bound column inner_bound : ident.
Variable body outer_body : statement.
Hypothesis RN : row <> bound.
Hypothesis RC : row <> column.
Hypothesis NC : bound <> column.
Hypothesis RM : row <> inner_bound.
Hypothesis CM : column <> inner_bound.
Hypothesis BODY : flatten_region body = map (named_operation_statement row column) operations.
Hypothesis OUTER : flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column inner_bound body].

Lemma named_array_operations_source_clight_iterations fe ge locals le memory after final rows columns :
  le ! row = Some (Vint Int.zero) -> le ! bound = Some (Vint (Int.repr (Z.of_nat rows))) ->
  le ! inner_bound = Some (Vint (Int.repr (Z.of_nat columns))) ->
  signed_range (Z.of_nat rows) -> signed_range (Z.of_nat columns) ->
  0 < Z.of_nat rows <= rectangle_outer_limit base -> 0 < Z.of_nat columns <= rectangle_stride base ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 after final Out_normal ->
  rectangular_iterations (fun i j => named_array_operations_physical ge locals i j operations) rows columns memory final /\
  after = PTree.set row (Vint (Int.repr (Z.of_nat rows)))
    (PTree.set column (Vint (Int.repr (Z.of_nat columns))) le).
Proof.
  intros ZERO BOUND INNER NS MS NB MB SOURCE.
  assert (POS : rows <> O) by (intro EQ; rewrite EQ in NB; cbn in NB; lia).
  apply (@rectangle_source_decode fe ge locals row bound column inner_bound body outer_body
    (fun i j => named_array_operations_physical ge locals i j operations) rows columns RN RC NC RM CM POS NS MS
    (@named_array_operations_body_normal operations row column body BODY)
    (@named_array_operations_body_quiet operations row column body BODY)
    (@named_array_operations_body_writes operations row column body BODY) OUTER).
  - intros i j temps before after' final' I J ROW COLUMN RUN.
    apply flatten_region_execution in RUN; rewrite BODY in RUN.
    exact (@named_array_operations_tail_inverse base operations row column fe ge locals i j temps before after' final'
      VALID LAYOUTS ltac:(apply rectangle_point_bound with (N := Z.of_nat rows) (M := Z.of_nat columns); assumption)
      ltac:(replace (i*rectangle_stride base) with (i*rectangle_stride base+0) by lia;
        apply rectangle_point_bound with (N := Z.of_nat rows) (M := Z.of_nat columns); auto; lia)
      ROW COLUMN RUN).
  - exact ZERO.
  - exact BOUND.
  - exact INNER.
  - exact SOURCE.
Qed.

End SOURCE.
Print Assumptions named_array_operations_source_clight_iterations.
