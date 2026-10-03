From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightStraightLine ClightLoopSyntax ClightRegionProgress
  ClightRectangularStore ClightRectangularGuard ClightRectangularLoops ClightFrontendLoopProtocol.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemorySequenceLoops
  GuardMemoryMultipleArrays GuardMemoryRegistryBackend GuardMemoryAffineSourceExpressions
  GuardMemoryAffineSourceValuation GuardMemoryAffineSourceLoop GuardMemoryParametricLoops GuardMemoryParametricSourceClight.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The source language supplies point execution and its correspondence with
    memory instructions. Parameter guards and scheduling need no knowledge of
    the concrete point syntax or the arrays' address formulas. *)
Record memory_parametric_body_model (base : rectangle_shape) (row column : ident) (body : statement) := MemoryParametricBodyModel {
  parametric_body_descriptors : list memory_array_descriptor;
  parametric_body_instructions : list memory_instruction;
  parametric_body_point : genv -> env -> Z -> Z -> mem -> mem -> Prop;
  parametric_body_normal : normal_statement body = true;
  parametric_body_quiet : quiet_statement body = true;
  parametric_body_writes : writes_only [] body;
  parametric_body_decode : forall fe ge locals le before after final i j,
    0 <= i < rectangle_outer_limit base -> 0 <= j < rectangle_stride base ->
    le ! row = Some (Vint (Int.repr i)) -> le ! column = Some (Vint (Int.repr j)) ->
    exec_stmt fe ge locals le before body E0 after final Out_normal ->
    parametric_body_point ge locals i j before final /\ after = le;
  parametric_body_registry : forall ge locals before after,
    parametric_body_point ge locals 0 0 before after ->
    exists entries, Forall2 (memory_descriptor_binding ge locals) parametric_body_descriptors entries /\
      NoDup (map memory_array_id entries) /\
      Forall (fun entry => Mem.valid_pointer before (memory_array_block entry) 0 = true) entries;
  parametric_body_correspondence : forall entries ge locals i j before after,
    Forall2 (memory_descriptor_binding ge locals) parametric_body_descriptors entries ->
    NoDup (map memory_array_id entries) ->
    0 <= i < rectangle_outer_limit base -> 0 <= j < rectangle_stride base ->
    (parametric_body_point ge locals i j before after <->
      memory_sequence_point parametric_body_instructions i j
        (RuntimeState (memory_array_registry entries) before)
        (RuntimeState (memory_array_registry entries) after))
}.

Lemma parametric_body_singleton_point instruction i j before after :
  memory_sequence_point [instruction] i j before after <-> memory_point instruction i j before after.
Proof.
  unfold memory_sequence_point; split.
  - intro RUN; inversion RUN; subst.
    match goal with REST : Iter.iter_semantics _ [] _ _ |- _ => inversion REST; subst end.
    assumption.
  - intro RUN; econstructor; [exact RUN|constructor].
Qed.

Section SOURCE.
Variable base : rectangle_shape.
Hypothesis VALID : rectangle_layout_valid base.
Variable row bound column inner_bound : ident.
Variable expression : memory_source_affine.
Variable context : list ident.
Variable encoded : L.expr.
Hypothesis ENCODE : memory_source_loop_expression row context expression = Some encoded.
Variable body outer_body : statement.
Variable model : memory_parametric_body_model base row column body.
Hypothesis RN : row <> bound.
Hypothesis RC : row <> column.
Hypothesis NC : bound <> column.
Hypothesis RK : row <> inner_bound.
Hypothesis NK : bound <> inner_bound.
Hypothesis CK : column <> inner_bound.
Hypothesis SC : ~ In column (memory_source_affine_parameters row expression).
Hypothesis SK : ~ In inner_bound (memory_source_affine_parameters row expression).
Hypothesis OUTER : flatten_region outer_body =
  [memory_parametric_setup inner_bound (memory_source_affine_code expression); rectangle_reset column;
    frontend_counted_loop column inner_bound body].

Theorem memory_parametric_body_source_decode fe ge locals le memory after final rows parameters valuation :
  le ! row = Some (Vint Int.zero) -> le ! bound = Some (Vint (Int.repr (Z.of_nat rows))) ->
  (forall identifier, In identifier (memory_source_affine_parameters row expression) ->
    le ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  map valuation context = Z.of_nat rows::parameters ->
  signed_range (Z.of_nat rows) -> 0 < Z.of_nat rows <= rectangle_outer_limit base ->
  (forall i, 0 <= i < Z.of_nat rows -> 0 <= L.eval_expr (i::Z.of_nat rows::parameters) encoded <= rectangle_stride base) ->
  0 < L.eval_expr (0::Z.of_nat rows::parameters) encoded ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 after final Out_normal ->
  exists entries,
    Forall2 (memory_descriptor_binding ge locals) (parametric_body_descriptors model) entries /\
    NoDup (map memory_array_id entries) /\
    Forall (fun entry => Mem.valid_pointer memory (memory_array_block entry) 0 = true) entries /\
    L.loop_semantics (memory_parametric_sequence encoded (parametric_body_instructions model))
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
    0 <= i < rectangle_outer_limit base /\ 0 <= j < rectangle_stride base).
  { intros i j I J; specialize (WIDTH i I); unfold upper in J; split; lia. }
  destruct (@memory_parametric_source_decode fe ge locals row bound column inner_bound
    (memory_source_affine_code expression) upper body outer_body
    (parametric_body_point model ge locals) rows
    (memory_source_affine_parameters row expression) le RN RC NC RK NK CK
    ltac:(intro MEMBER; apply memory_source_affine_parameter_member in MEMBER; tauto) SC SK RP NS
    ltac:(intros i I; specialize (WIDTH i I); unfold upper,signed_range; unfold signed_range in ML;
      change Int.min_signed with (-2147483648) in *; lia)
    (memory_source_affine_pure expression) VALUE
    (parametric_body_normal model) (parametric_body_quiet model) (parametric_body_writes model) OUTER
    ltac:(intros i j temps before next final' I J ROW COLUMN RUN;
      destruct (INDEX i j I J) as [ROW_RANGE COLUMN_RANGE];
      eapply parametric_body_decode; eassumption)
    le memory after final ZERO BOUND (temp_agree_refl _ _) SOURCE) as [ITER EXIT].
  change (memory_parametric_iterations (parametric_body_point model ge locals)
    rows parameters encoded memory final) in ITER.
  destruct (@memory_parametric_first mem (parametric_body_point model ge locals)
    rows parameters encoded memory final RP FIRST ITER) as [first HEAD].
  destruct (@parametric_body_registry base row column body model ge locals memory first HEAD)
    as [entries [ARRAYS [UNIQUE POINTERS]]].
  exists entries; split; [exact ARRAYS|]; split; [exact UNIQUE|]; split; [exact POINTERS|]; split; [|exact EXIT].
  apply (proj1 (@memory_parametric_sequence_lift (memory_array_registry entries)
    (parametric_body_instructions model) (parametric_body_point model ge locals)
    rows parameters encoded memory final
    ltac:(intros; apply (proj1 (WIDTH _ H)))
    ltac:(intros i j before next I J;
      destruct (INDEX i j I J) as [ROW_RANGE COLUMN_RANGE];
      apply parametric_body_correspondence; assumption))).
  exact ITER.
Qed.
End SOURCE.
Print Assumptions memory_parametric_body_source_decode.
