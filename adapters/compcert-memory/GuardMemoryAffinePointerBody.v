From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCountedLoop ClightTempFrame ClightNoWrap ClightStraightLine
  ClightPureExpr ClightRectangularStore ClightRectangularLoops ClightFrontendLoopProtocol.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops
  GuardMemoryNaryCompute GuardMemoryNaryRanges GuardMemoryNaryLoops
  GuardMemoryRecursiveSource GuardMemoryRecursiveBody GuardMemoryPointerSequence GuardMemoryPointerCompute
  GuardMemoryMultiPointerCompute GuardMemoryMultiPointerSequence GuardMemoryMultiPointerIdentifiers
  GuardMemoryMultiPointerCells GuardMemoryBufferOffsets GuardMemoryInstructionPadding GuardMemoryScalarPointerBody
  GuardMemoryParametricSourceClight GuardMemoryParametricFirstBody GuardMemoryPointerSourceWords
  GuardMemorySourceParameters GuardMemoryParametricLoops GuardMemoryAffineParameterLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section SOURCE.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable row bound column inner_bound : ident.
Variable expression : expr.
Variable encoded : L.expr.
Variable body outer_body : statement.
Variable geometry scalars pointers : list ident.
Variable geometry_limits : list Z.
Variable row_limit column_limit extent : Z.
Variable operations : list memory_nary_compute.
Let layout := [row;column]++(bound::geometry).
Let limits := [row_limit;column_limit]++geometry_limits.
Let stable := pointers++((bound::geometry)++scalars).
Let instructions := memory_pad_instructions (length scalars) (map memory_nary_compute_instruction operations).
Hypothesis RN : row <> bound.
Hypothesis RC : row <> column.
Hypothesis NC : bound <> column.
Hypothesis RK : row <> inner_bound.
Hypothesis NK : bound <> inner_bound.
Hypothesis CK : column <> inner_bound.
Hypothesis PROTECTED : forall identifier, In identifier stable ->
  identifier <> row /\ identifier <> column /\ identifier <> inner_bound.
Hypothesis UNIQUE : NoDup (layout++scalars).
Hypothesis VALID : Forall (memory_multi_pointer_compute_valid limits layout scalars extent) operations.
Hypothesis COVER : Forall (memory_multi_pointer_operation_covered pointers) operations.
Hypothesis BODY : flatten_region body = map memory_pointer_compute_statement operations.
Hypothesis OUTER : flatten_region outer_body =
  [memory_parametric_setup inner_bound expression; rectangle_reset column;
    frontend_counted_loop column inner_bound body].
Variable rows : nat.
Variable geometry_values scalar_values : list Z.
Variable base : temp_env.
Let parameter_values := Z.of_nat rows::geometry_values.
Let context_values := parameter_values++scalar_values.
Let upper := fun i => L.eval_expr (i::context_values) encoded.
Let physical := fun i j => memory_multi_pointer_sequence_physical base
  (([i;j]++parameter_values)++scalar_values) operations.
Hypothesis ROWS : rows <> O.
Hypothesis NS : signed_range (Z.of_nat rows).
Hypothesis ROW_RANGE : Z.of_nat rows <= row_limit.
Hypothesis INNER : forall i, 0 <= i < Z.of_nat rows ->
  0 <= upper i <= column_limit /\ signed_range (upper i).
Hypothesis GEOMETRY_RANGE : memory_nary_ranges geometry_limits parameter_values.
Hypothesis GEOMETRY_WORDS : memory_nest_bindings (bound::geometry) parameter_values base.
Hypothesis SCALAR_WORDS : memory_nest_bindings scalars scalar_values base.
Hypothesis PURE : pure_scalar expression.
Hypothesis VALUE : forall i temps memory, 0 <= i < Z.of_nat rows ->
  temps ! row = Some (Vint (Int.repr i)) -> temp_agree stable base temps ->
  eval_expr ge locals temps memory expression (Vint (Int.repr (upper i))).

Lemma memory_affine_pointer_point_ranges i j :
  0 <= i < Z.of_nat rows -> 0 <= j < upper i ->
  memory_nary_ranges limits ([i;j]++parameter_values).
Proof.
  intros I J; specialize (@INNER i I) as [[LOW HIGH] SIGNED].
  unfold limits,memory_nary_ranges; cbn; constructor; [lia|].
  constructor; [lia|exact GEOMETRY_RANGE].
Qed.

Lemma memory_affine_pointer_body_decode i j temps memory after final :
  0 <= i < Z.of_nat rows -> 0 <= j < upper i ->
  temps ! row = Some (Vint (Int.repr i)) -> temps ! column = Some (Vint (Int.repr j)) ->
  temp_agree stable base temps ->
  exec_stmt fe ge locals temps memory body E0 after final Out_normal ->
  physical i j memory final /\ after = temps.
Proof.
  intros I J ROW COLUMN FRAME RUN.
  assert (COORDINATES : memory_nest_bindings [row;column] [i;j] temps)
    by (constructor; [exact ROW|constructor; [exact COLUMN|constructor]]).
  assert (GEOMETRY : memory_nest_bindings (bound::geometry) parameter_values temps).
  { eapply memory_nest_bindings_frame_from; [|exact FRAME|exact GEOMETRY_WORDS].
    intros identifier MEMBER; unfold stable; apply in_or_app; right; apply in_or_app; left; exact MEMBER. }
  assert (SCALARS : memory_nest_bindings scalars scalar_values temps).
  { eapply memory_nest_bindings_frame_from; [|exact FRAME|exact SCALAR_WORDS].
    intros identifier MEMBER; unfold stable; apply in_or_app; right; apply in_or_app; right; exact MEMBER. }
  assert (POINT_WORDS : memory_nest_bindings layout ([i;j]++parameter_values) temps)
    by (unfold layout; apply memory_nest_bindings_append; assumption).
  assert (ALL_WORDS : memory_nest_bindings (layout++scalars)
    (([i;j]++parameter_values)++scalar_values) temps)
    by (apply memory_nest_bindings_append; assumption).
  destruct (memory_nest_bindings_valuation UNIQUE ALL_WORDS) as [valuation [VALUES BINDINGS]].
  assert (GEOMETRY_VALUES : map valuation layout = [i;j]++parameter_values).
  { apply memory_list_prefix_equal with (trailing := map valuation scalars) (other := scalar_values).
    - rewrite length_map; apply Forall2_length in POINT_WORDS; exact POINT_WORDS.
    - rewrite <-map_app; exact VALUES. }
  apply flatten_region_execution in RUN; rewrite BODY in RUN.
  destruct (@memory_multi_pointer_sequence_tail_inverse limits operations layout scalars extent fe ge locals
    valuation temps memory after final VALID
    ltac:(rewrite GEOMETRY_VALUES; apply memory_affine_pointer_point_ranges; assumption) BINDINGS RUN)
    as [ACTION EXIT].
  split; [|exact EXIT]; unfold physical; rewrite <-VALUES.
  apply memory_multi_pointer_sequence_frame with (pointers := pointers) (initial := temps).
  - exact COVER.
  - intros identifier MEMBER; symmetry; apply FRAME; unfold stable; apply in_or_app; left; exact MEMBER.
  - exact ACTION.
Qed.

Theorem memory_affine_pointer_source_decode temps memory after final :
  temps ! row = Some (Vint Int.zero) -> temp_agree stable base temps ->
  exec_stmt fe ge locals temps memory (frontend_counted_loop row bound outer_body) E0 after final Out_normal ->
  L.loop_semantics (memory_affine_parameter_sequence (length context_values) encoded instructions)
    context_values (RuntimeState (memory_multi_pointer_locations base extent) memory)
    (RuntimeState (memory_multi_pointer_locations base extent) final) /\
  after = PTree.set row (Vint (Int.repr (Z.of_nat rows)))
    (memory_parametric_settle column inner_bound upper (Z.of_nat rows-1) temps).
Proof.
  intros ZERO FRAME SOURCE.
  assert (BOUND : temps ! bound = Some (Vint (Int.repr (Z.of_nat rows)))).
  { rewrite FRAME by (unfold stable; apply in_or_app; right; apply in_or_app; left; cbn; auto).
    inversion GEOMETRY_WORDS; subst; assumption. }
  assert (FRESH : ~ In row stable /\ ~ In column stable /\ ~ In inner_bound stable).
  { repeat split; intro MEMBER; specialize (PROTECTED _ MEMBER); tauto. }
  destruct (@memory_parametric_source_decode_framed fe ge locals row bound column inner_bound expression
    upper body outer_body physical rows stable base RN RC NC RK NK CK (proj1 FRESH) (proj1 (proj2 FRESH))
    (proj2 (proj2 FRESH)) ROWS NS
    ltac:(intros i I; destruct (@INNER i I) as [[LOW HIGH] SIGNED]; auto) PURE VALUE
    (@memory_pointer_sequence_normal operations body BODY) (@memory_pointer_sequence_quiet operations body BODY)
    (@memory_pointer_sequence_writes operations body BODY) OUTER memory_affine_pointer_body_decode
    temps memory after final ZERO BOUND FRAME SOURCE) as [ITER EXIT].
  split; [|exact EXIT].
  assert (NONNEGATIVE : forall i, 0 <= i < Z.of_nat rows ->
    0 <= L.eval_expr (i::Z.of_nat rows::(geometry_values++scalar_values)) encoded).
  { intros i I; pose proof (@INNER i I); unfold upper,context_values,parameter_values in H; tauto. }
  assert (POINT : forall i j before target, 0 <= i < Z.of_nat rows ->
    0 <= j < L.eval_expr (i::Z.of_nat rows::(geometry_values++scalar_values)) encoded ->
    (physical i j before target <->
      memory_affine_parameter_point instructions (Z.of_nat rows::(geometry_values++scalar_values)) i j
        (RuntimeState (memory_multi_pointer_locations base extent) before)
        (RuntimeState (memory_multi_pointer_locations base extent) target))).
  { intros i j before target I J; unfold physical,memory_affine_parameter_point,instructions.
    rewrite memory_pad_sequence_point.
    change (memory_multi_pointer_sequence_physical base (([i;j]++parameter_values)++scalar_values) operations before target <->
      memory_nary_sequence_point (map memory_nary_compute_instruction operations)
        (([i;j]++parameter_values)++scalar_values)
        (RuntimeState (memory_multi_pointer_locations base extent) before)
        (RuntimeState (memory_multi_pointer_locations base extent) target)).
    apply (@memory_multi_pointer_sequence_point_execution limits layout scalars extent base
      ([i;j]++parameter_values) scalar_values operations).
    - exact VALID.
    - apply memory_affine_pointer_point_ranges; assumption.
    - apply Forall2_length in GEOMETRY_WORDS; unfold layout,parameter_values in *; rewrite !length_app; cbn in *;
      exact (f_equal S (f_equal S (eq_sym GEOMETRY_WORDS))). }
  apply (proj1 (@memory_affine_parameter_sequence_lift (memory_multi_pointer_locations base extent)
    instructions physical rows (geometry_values++scalar_values) encoded memory final NONNEGATIVE POINT)).
  exact ITER.
Qed.
End SOURCE.
Print Assumptions memory_affine_pointer_body_decode.
Print Assumptions memory_affine_pointer_source_decode.

(** Body-only register words are learned from an actual first source body,
    after the active headers have been justified. Header-only parameters are
    obtained separately from memory_parametric_source_words. *)
Theorem memory_affine_pointer_source_first_words fe ge locals temps memory row bound column inner_bound expression
  rows upper body outer_body after final geometry scalars limits layout extent operations :
  row <> bound -> row <> column -> row <> inner_bound -> bound <> column -> bound <> inner_bound ->
  column <> inner_bound ->
  pure_scalar expression ->
  temps ! row = Some (Vint Int.zero) -> temps ! bound = Some (Vint (Int.repr rows)) ->
  0 < rows -> signed_range rows ->
  eval_expr ge locals temps memory expression (Vint (Int.repr upper)) ->
  0 < upper -> signed_range upper ->
  (forall identifier, In identifier (geometry++scalars) -> identifier <> column /\ identifier <> inner_bound) ->
  flatten_region outer_body = [memory_parametric_setup inner_bound expression;
    rectangle_reset column;frontend_counted_loop column inner_bound body] ->
  flatten_region body = map memory_pointer_compute_statement operations ->
  Forall (memory_multi_pointer_compute_valid limits layout scalars extent) operations ->
  (forall identifier, In identifier geometry -> exists operation,
    In operation operations /\ In identifier (memory_pointer_operation_address_reads operation)) ->
  (forall identifier, In identifier scalars -> exists operation index,
    In operation operations /\ nth_error (layout++scalars) index = Some identifier /\
    In index (memory_source_parameter_positions (memory_nary_compute_value operation))) ->
  exec_stmt fe ge locals temps memory (frontend_counted_loop row bound outer_body) E0 after final Out_normal ->
  forall identifier, In identifier (geometry++scalars) -> exists word, temps ! identifier = Some (Vint word).
Proof.
  intros RN RC RK NC NK CK PURE ZERO BOUND POSITIVE SAFE VALUE INNER_POSITIVE INNER_SAFE
    PROTECTED OUTER BODY VALID ADDRESS_USED SCALAR_USED SOURCE.
  destruct (@memory_parametric_source_first_body fe ge locals temps memory row bound column inner_bound expression
    rows upper body outer_body after final (geometry++scalars) RN RC RK NC NK CK
    (@memory_pointer_sequence_normal operations body BODY) (@memory_pointer_sequence_quiet operations body BODY)
    (@memory_pointer_sequence_writes operations body BODY) PURE ZERO BOUND POSITIVE SAFE VALUE INNER_POSITIVE
    INNER_SAFE PROTECTED OUTER SOURCE) as [leaf [next [last [FRAME RUN]]]].
  apply flatten_region_execution in RUN; rewrite BODY in RUN.
  intros identifier MEMBER; apply in_app_iff in MEMBER as [ADDRESS|SCALAR].
  - destruct (ADDRESS_USED identifier ADDRESS) as [operation [MEMBER USED]].
    destruct (@memory_pointer_sequence_address_words limits operations layout scalars extent fe ge locals identifier
      VALID leaf memory next last RUN operation MEMBER USED) as [word WORD].
    exists word; rewrite FRAME in WORD by (apply in_or_app; left; exact ADDRESS); exact WORD.
  - destruct (SCALAR_USED identifier SCALAR) as [operation [index [MEMBER [LOOKUP USED]]]].
    destruct (@memory_multi_pointer_sequence_used_register limits operations layout scalars extent fe ge locals
      identifier index VALID LOOKUP leaf memory next last RUN operation MEMBER USED) as [word WORD].
    exists word; rewrite FRAME in WORD by (apply in_or_app; right; exact SCALAR); exact WORD.
Qed.
Print Assumptions memory_affine_pointer_source_first_words.
