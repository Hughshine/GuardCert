From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightStraightLine
  ClightRectangularStore ClightRectangularGuard ClightRectangularLoops ClightFrontendLoopProtocol.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemorySequenceLoops
  GuardMemoryMultipleArrays GuardMemoryRegistryBackend GuardMemoryNamedOperations GuardMemoryNamedRegistrySource
  GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation GuardMemoryAffineSourceLoop
  GuardMemoryParametricLoops GuardMemoryParametricSourceClight.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section SOURCE.
Variable base : rectangle_shape.
Hypothesis VALID : rectangle_layout_valid base.
Variable operations : list named_array_operation.
Hypothesis LAYOUTS : Forall (named_operation_layout base) operations.
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
Hypothesis BODY : flatten_region body = map (named_operation_statement row column) operations.
Hypothesis OUTER : flatten_region outer_body =
  [memory_parametric_setup inner_bound (memory_source_affine_code expression); rectangle_reset column;
    frontend_counted_loop column inner_bound body].

Theorem named_array_operations_parametric_source_decode fe ge locals le memory after final rows parameters valuation :
  le ! row = Some (Vint Int.zero) -> le ! bound = Some (Vint (Int.repr (Z.of_nat rows))) ->
  (forall identifier, In identifier (memory_source_affine_parameters row expression) ->
    le ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  map valuation context = Z.of_nat rows::parameters ->
  signed_range (Z.of_nat rows) -> 0 < Z.of_nat rows <= rectangle_outer_limit base ->
  (forall i, 0 <= i < Z.of_nat rows -> 0 <= L.eval_expr (i::Z.of_nat rows::parameters) encoded <= rectangle_stride base) ->
  0 < L.eval_expr (0::Z.of_nat rows::parameters) encoded ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 after final Out_normal ->
  exists entries,
    Forall2 (memory_descriptor_binding ge locals) (named_array_descriptors base operations) entries /\
    NoDup (map memory_array_id entries) /\
    Forall (fun entry => Mem.valid_pointer memory (memory_array_block entry) 0 = true) entries /\
    L.loop_semantics (memory_parametric_sequence encoded (map named_operation_instruction operations))
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
    0 <= i*rectangle_stride base+j < rectangle_extent base /\ 0 <= i*rectangle_stride base < rectangle_extent base).
  { intros i j I J; specialize (WIDTH i I); unfold upper in J; split.
    - apply rectangle_point_bound with (N := Z.of_nat rows) (M := rectangle_stride base); auto; lia.
    - replace (i*rectangle_stride base) with (i*rectangle_stride base+0) by lia.
      apply rectangle_point_bound with (N := Z.of_nat rows) (M := rectangle_stride base); auto; lia. }
  destruct (@memory_parametric_source_decode fe ge locals row bound column inner_bound
    (memory_source_affine_code expression) upper body outer_body
    (fun i j => named_array_operations_physical ge locals i j operations) rows
    (memory_source_affine_parameters row expression) le RN RC NC RK NK CK
    ltac:(intro MEMBER; apply memory_source_affine_parameter_member in MEMBER; tauto) SC SK RP NS
    ltac:(intros i I; specialize (WIDTH i I); unfold upper,signed_range; unfold signed_range in ML;
      change Int.min_signed with (-2147483648) in *; lia)
    (memory_source_affine_pure expression) VALUE
    (@named_array_operations_body_normal operations row column body BODY)
    (@named_array_operations_body_quiet operations row column body BODY)
    (@named_array_operations_body_writes operations row column body BODY) OUTER
    ltac:(intros i j temps before next final' I J ROW COLUMN RUN;
      destruct (INDEX i j I J) as [WRITE_INDEX READ_INDEX];
      apply flatten_region_execution in RUN; rewrite BODY in RUN;
      exact (@named_array_operations_tail_inverse base operations row column fe ge locals i j temps before next final'
        VALID LAYOUTS WRITE_INDEX READ_INDEX ROW COLUMN RUN))
    le memory after final ZERO BOUND (temp_agree_refl _ _) SOURCE) as [ITER EXIT].
  change (memory_parametric_iterations (fun i j => named_array_operations_physical ge locals i j operations)
    rows parameters encoded memory final) in ITER.
  destruct (@memory_parametric_first mem (fun i j => named_array_operations_physical ge locals i j operations)
    rows parameters encoded memory final RP FIRST ITER) as [first HEAD].
  destruct (@named_array_operations_registry base operations ge locals memory first VALID LAYOUTS HEAD)
    as [entries [ARRAYS [UNIQUE POINTERS]]].
  exists entries; split; [exact ARRAYS|]; split; [exact UNIQUE|]; split; [exact POINTERS|]; split; [|exact EXIT].
  apply (proj1 (@memory_parametric_sequence_lift (memory_array_registry entries)
    (map named_operation_instruction operations) (fun i j => named_array_operations_physical ge locals i j operations)
    rows parameters encoded memory final
    ltac:(intros; apply (proj1 (WIDTH _ H)))
    ltac:(intros i j before next I J;
      destruct (INDEX i j I J) as [WRITE_INDEX READ_INDEX];
      apply named_array_operations_point_execution with (base := base) (universe := operations);
      [exact ARRAYS|exact UNIQUE|exact LAYOUTS|apply Forall_forall; auto|exact WRITE_INDEX|exact READ_INDEX]))).
  exact ITER.
Qed.
End SOURCE.
Print Assumptions named_array_operations_parametric_source_decode.
