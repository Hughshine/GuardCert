From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightStraightLine ClightLoopSyntax ClightRegionProgress
  ClightRectangularStore ClightRectangularGuard ClightRectangularLoops ClightFrontendLoopProtocol.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemorySequenceLoops
  GuardMemoryMultipleArrays GuardMemoryRegistryBackend GuardMemoryNamedOperations GuardMemoryNamedRegistrySource
  GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation GuardMemoryAffineSourceLoop
  GuardMemoryParametricLoops GuardMemoryParametricSourceClight GuardMemoryCommonLayout
  GuardMemoryLayoutCopy GuardMemoryLayoutCopyInstruction GuardMemoryLayoutCopyRegistry.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_layout_copy_singleton_point instruction i j before after :
  memory_sequence_point [instruction] i j before after <-> memory_point instruction i j before after.
Proof.
  unfold memory_sequence_point; split.
  - intro RUN; inversion RUN; subst.
    match goal with REST : Iter.iter_semantics _ [] _ _ |- _ => inversion REST; subst end.
    assumption.
  - intro RUN; econstructor; [exact RUN|constructor].
Qed.

Lemma memory_layout_copy_body_normal write_shape read_shape write_array read_array row column body :
  flatten_region body = [memory_layout_copy_statement write_shape read_shape write_array read_array row column] ->
  normal_statement body = true.
Proof. intro BODY; apply flatten_normal_certificate; rewrite BODY; constructor; [reflexivity|constructor]. Qed.
Lemma memory_layout_copy_body_quiet write_shape read_shape write_array read_array row column body :
  flatten_region body = [memory_layout_copy_statement write_shape read_shape write_array read_array row column] ->
  quiet_statement body = true.
Proof. intro BODY; apply flatten_quiet_certificate; rewrite BODY; constructor; [reflexivity|constructor]. Qed.
Lemma memory_layout_copy_body_writes write_shape read_shape write_array read_array row column body :
  flatten_region body = [memory_layout_copy_statement write_shape read_shape write_array read_array row column] ->
  writes_only [] body.
Proof. intro BODY; apply flatten_writes_certificate; rewrite BODY; constructor; constructor. Qed.

Section SOURCE.
Variable write_shape read_shape : rectangle_shape.
Hypothesis WVALID : rectangle_layout_valid write_shape.
Hypothesis RVALID : rectangle_layout_valid read_shape.
Variable write_array read_array : ident.
Hypothesis DISTINCT : write_array <> read_array.
Let base := memory_common_layout write_shape read_shape.
Let VALID : rectangle_layout_valid base := memory_common_layout_valid WVALID RVALID.
Let instruction := memory_layout_copy_instruction write_shape read_shape write_array read_array.
Variable row bound column inner_bound : ident.
Variable expression : memory_source_affine.
Variable context : list ident.
Variable encoded : L.expr.
Hypothesis ENCODE : memory_source_loop_expression row context expression = Some encoded.
Variable body outer_body : statement.
Hypothesis RN : row <> bound.
Hypothesis RC : row <> column.
Hypothesis NC : bound <> column.
Hypothesis RK : row <> inner_bound.
Hypothesis NK : bound <> inner_bound.
Hypothesis CK : column <> inner_bound.
Hypothesis SC : ~ In column (memory_source_affine_parameters row expression).
Hypothesis SK : ~ In inner_bound (memory_source_affine_parameters row expression).
Hypothesis BODY : flatten_region body = [memory_layout_copy_statement write_shape read_shape write_array read_array row column].
Hypothesis OUTER : flatten_region outer_body =
  [memory_parametric_setup inner_bound (memory_source_affine_code expression); rectangle_reset column;
    frontend_counted_loop column inner_bound body].

Theorem memory_layout_copy_source_decode fe ge locals le memory after final rows parameters valuation :
  le ! row = Some (Vint Int.zero) -> le ! bound = Some (Vint (Int.repr (Z.of_nat rows))) ->
  (forall identifier, In identifier (memory_source_affine_parameters row expression) ->
    le ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  map valuation context = Z.of_nat rows::parameters ->
  signed_range (Z.of_nat rows) -> 0 < Z.of_nat rows <= rectangle_outer_limit base ->
  (forall i, 0 <= i < Z.of_nat rows -> 0 <= L.eval_expr (i::Z.of_nat rows::parameters) encoded <= rectangle_stride base) ->
  0 < L.eval_expr (0::Z.of_nat rows::parameters) encoded ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 after final Out_normal ->
  exists entries,
    Forall2 (memory_descriptor_binding ge locals) (memory_layout_copy_descriptors write_shape read_shape write_array read_array) entries /\
    NoDup (map memory_array_id entries) /\
    Forall (fun entry => Mem.valid_pointer memory (memory_array_block entry) 0 = true) entries /\
    L.loop_semantics (memory_parametric_sequence encoded [instruction])
      (Z.of_nat rows::parameters)
      (RuntimeState (memory_array_registry entries) memory) (RuntimeState (memory_array_registry entries) final) /\
    after = PTree.set row (Vint (Int.repr (Z.of_nat rows)))
      (memory_parametric_settle column inner_bound
        (fun i => L.eval_expr (i::Z.of_nat rows::parameters) encoded) (Z.of_nat rows-1) le).
Proof.
  intros ZERO BOUND WORDS CONTEXT NS NB WIDTH FIRST SOURCE.
  assert (RP : rows <> O) by (intro SAME; rewrite SAME in NB; cbn in NB; lia).
  pose proof (rectangle_limits VALID) as [NL [ML LIMITS]].
  set (upper := fun i => L.eval_expr (i::Z.of_nat rows::parameters) encoded).
  assert (VALUE : forall i temps before, 0 <= i < Z.of_nat rows ->
    temps ! row = Some (Vint (Int.repr i)) ->
    temp_agree (memory_source_affine_parameters row expression) le temps ->
    eval_expr ge locals temps before (memory_source_affine_code expression) (Vint (Int.repr (upper i)))).
  { intros i temps before RANGE ROW FRAME.
    pose proof (@memory_source_loop_expression_value expression row context encoded valuation i ENCODE) as SAME.
    rewrite CONTEXT in SAME; unfold upper; rewrite SAME.
    eapply memory_source_affine_iteration_value; eassumption. }
  assert (INDEX : forall i j, 0 <= i < Z.of_nat rows -> 0 <= j < upper i ->
    0 <= i*rectangle_stride write_shape+j < rectangle_extent write_shape /\
    0 <= i*rectangle_stride read_shape+j < rectangle_extent read_shape).
  { intros i j I J; specialize (WIDTH i I).
    apply (@memory_common_layout_points write_shape read_shape (Z.of_nat rows) i j WVALID RVALID NB I).
    change (0 <= j < rectangle_stride base); unfold upper in J; lia. }
  assert (NORMAL : normal_statement body = true).
  { apply flatten_normal_certificate; rewrite BODY; constructor; [reflexivity|constructor]. }
  assert (QUIET : quiet_statement body = true).
  { apply flatten_quiet_certificate; rewrite BODY; constructor; [reflexivity|constructor]. }
  assert (WRITES : writes_only [] body).
  { apply flatten_writes_certificate; rewrite BODY; constructor; constructor. }
  destruct (@memory_parametric_source_decode fe ge locals row bound column inner_bound
    (memory_source_affine_code expression) upper body outer_body
    (fun i j => memory_layout_copy_point ge locals write_shape read_shape write_array read_array i j) rows
    (memory_source_affine_parameters row expression) le RN RC NC RK NK CK
    ltac:(intro MEMBER; apply memory_source_affine_parameter_member in MEMBER; tauto) SC SK RP NS
    ltac:(intros i I; specialize (WIDTH i I); unfold upper,signed_range; unfold signed_range in ML;
      change Int.min_signed with (-2147483648) in *; lia)
    (memory_source_affine_pure expression) VALUE
    NORMAL QUIET WRITES OUTER
    ltac:(intros i j temps before next final' I J ROW COLUMN RUN;
      destruct (INDEX i j I J) as [WRITE_INDEX READ_INDEX];
      apply (@flattened_singleton_execution fe ge locals body
        (memory_layout_copy_statement write_shape read_shape write_array read_array row column)
        temps before next final' BODY) in RUN;
      destruct (@memory_layout_copy_statement_inverse write_shape read_shape WVALID RVALID
        fe ge locals temps before write_array read_array row column i j E0 next final' Out_normal
        ROW COLUMN WRITE_INDEX READ_INDEX RUN) as [wb [rb [WB [RB [TRACE [TEMPS [OUT ACT]]]]]]];
      split; [exists wb,rb; auto|exact TEMPS])
    le memory after final ZERO BOUND (temp_agree_refl _ _) SOURCE) as [ITER EXIT].
  change (memory_parametric_iterations (fun i j => memory_layout_copy_point ge locals write_shape read_shape write_array read_array i j)
    rows parameters encoded memory final) in ITER.
  destruct (@memory_parametric_first mem (fun i j => memory_layout_copy_point ge locals write_shape read_shape write_array read_array i j)
    rows parameters encoded memory final RP FIRST ITER) as [first HEAD].
  destruct (@memory_layout_copy_registry write_shape read_shape write_array read_array ge locals memory first WVALID RVALID DISTINCT HEAD)
    as [entries [ARRAYS [UNIQUE POINTERS]]].
  exists entries; split; [exact ARRAYS|]; split; [exact UNIQUE|]; split; [exact POINTERS|]; split; [|exact EXIT].
  apply (proj1 (@memory_parametric_sequence_lift (memory_array_registry entries)
    [instruction] (fun i j => memory_layout_copy_point ge locals write_shape read_shape write_array read_array i j)
    rows parameters encoded memory final
    ltac:(intros; apply (proj1 (WIDTH _ H)))
    ltac:(intros i j before next I J;
      destruct (INDEX i j I J) as [WRITE_INDEX READ_INDEX];
      rewrite memory_layout_copy_singleton_point;
      apply memory_layout_copy_point_execution; assumption))).
  exact ITER.
Qed.
End SOURCE.
Print Assumptions memory_layout_copy_source_decode.
