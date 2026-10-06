From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightTempFrame ClightCountedLoop
  ClightFrontendLoopProtocol ClightPureExpr ClightLoopSyntax ClightRegionProgress ClightStraightLine
  ClightRectangularLoops CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryNaryCompute
  GuardMemoryNaryRanges GuardMemoryRecursiveSource GuardMemoryPointerCompute GuardMemoryPointerSequence
  GuardMemoryMultiPointerCompute GuardMemoryMultiPointerSequence GuardMemoryMultiPointerIdentifiers
  GuardMemoryMultiPointerCells GuardMemoryPointerSourceWords GuardMemorySourceParameters GuardMemoryParametricSourceClight
  GuardMemoryParametricFirstBody GuardMemoryAffinePointerBody GuardMemoryObservationStability.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightStrictIteration
  ClightAffineLoadedBoundTransport.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The domain adapter consumes the existing actual pointer-body decoder and
    supplies the language bridge with physical write separation. It does not
    assume that a mathematical Loop trace already describes the loaded source. *)
Section CACHE.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variables row cache column inner_bound parameter : ident.
Variables expression : expr.
Variable encoded : L.expr.
Variables body outer_body : statement.
Variables geometry scalars pointers : list ident.
Variable geometry_limits : list Z.
Variables row_limit column_limit extent : Z.
Variable operations : list memory_nary_compute.
Let layout := [row;column]++(cache::geometry).
Let limits := [row_limit;column_limit]++geometry_limits.
Let stable := pointers++((cache::geometry)++scalars).
Hypotheses (RC : row <> column) (RN : row <> cache) (NC : cache <> column)
  (RK : row <> inner_bound) (NK : cache <> inner_bound) (CK : column <> inner_bound).
Hypothesis PROTECTED : forall identifier, In identifier stable ->
  identifier <> row /\ identifier <> column /\ identifier <> inner_bound.
Hypothesis UNIQUE : NoDup (layout++scalars).
Hypothesis VALID : Forall (memory_multi_pointer_compute_valid limits layout scalars extent) operations.
Hypothesis COVER : Forall (memory_multi_pointer_operation_covered pointers) operations.
Hypothesis BODY : flatten_region body = map memory_pointer_compute_statement operations.
Hypothesis OUTER : flatten_region outer_body =
  [memory_parametric_setup inner_bound expression;rectangle_reset column;frontend_counted_loop column inner_bound body].
Variable rows : nat.
Variables geometry_values scalar_values : list Z.
Variable base : temp_env.
Let parameters := Z.of_nat rows::geometry_values.
Let values := parameters++scalar_values.
Let upper := fun i => L.eval_expr (i::values) encoded.
Let point := fun i j => memory_multi_pointer_sequence_physical base (([i;j]++parameters)++scalar_values) operations.
Hypothesis ROWS : rows <> O.
Hypothesis SIGNED : signed_range (Z.of_nat rows).
Hypothesis ROW_RANGE : Z.of_nat rows <= row_limit.
Hypothesis INNER : forall i, 0 <= i < Z.of_nat rows ->
  0 <= upper i <= column_limit /\ signed_range (upper i).
Hypothesis GEOMETRY_RANGE : memory_nary_ranges geometry_limits parameters.
Hypothesis GEOMETRY_WORDS : memory_nest_bindings (cache::geometry) parameters base.
Hypothesis SCALAR_WORDS : memory_nest_bindings scalars scalar_values base.
Hypothesis PURE : pure_scalar expression.
Hypothesis VALUE : forall i current memory, 0 <= i < Z.of_nat rows ->
  current ! row = Some (Vint (Int.repr i)) -> temp_agree stable base current ->
  eval_expr ge locals current memory expression (Vint (Int.repr (upper i))).
Variable block : block.
Variable offset : ptrofs.
Hypothesis PARAMETER_MEMBER : In parameter pointers.
Hypothesis POINTER : base ! parameter = Some (Vptr block offset).
Hypothesis APART : forall i j, 0 <= i < Z.of_nat rows -> 0 <= j < upper i ->
  memory_pointer_writes_apart_observation base (([i;j]++parameters)++scalar_values) operations
    (MemoryLocation Mint32 block (Ptrofs.unsigned offset)).

Theorem memory_affine_pointer_loaded_source_cached current memory trace after final outcome :
  current ! row = Some (Vint Int.zero) -> temp_agree stable base current ->
  Mem.loadv Mint32 memory (Vptr block offset) = Some (Vint (Int.repr (Z.of_nat rows))) ->
  exec_stmt fe ge locals current memory (loaded_bound_loop row parameter outer_body) trace after final outcome ->
  exec_stmt fe ge locals current memory (frontend_counted_loop row cache outer_body) trace after final outcome /\
    Mem.loadv Mint32 final (Vptr block offset) = Some (Vint (Int.repr (Z.of_nat rows))).
Proof.
  intros ZERO FRAME READ SOURCE.
  assert (FRESH : ~ In row stable /\ ~ In column stable /\ ~ In inner_bound stable)
    by (repeat split; intro MEMBER; specialize (PROTECTED _ MEMBER); tauto).
  assert (CACHE : base ! cache = Some (Vint (Int.repr (Z.of_nat rows))))
    by (inversion GEOMETRY_WORDS; subst; assumption).
  destruct (@affine_loaded_bound_cached fe ge locals row cache parameter column inner_bound outer_body point upper
    stable base block offset (Z.of_nat rows)
    ltac:(pose proof Nat2Z.is_nonneg rows; unfold signed_range in SIGNED; split; lia)
    RC RK (proj1 (proj2 FRESH)) (proj2 (proj2 FRESH)) (proj1 FRESH)
    ltac:(unfold stable; apply in_or_app; right; apply in_or_app; left; cbn; auto)
    ltac:(unfold stable; apply in_or_app; left; exact PARAMETER_MEMBER) CACHE POINTER
    ltac:(apply flatten_quiet_certificate; rewrite OUTER; constructor; [reflexivity|];
      constructor; [reflexivity|constructor; [|constructor]];
      cbn [quiet_statement frontend_counted_loop counter_increment];
      rewrite (@memory_pointer_sequence_quiet operations body BODY); reflexivity)
    (@memory_parametric_outer_normal column inner_bound expression body outer_body
      (@memory_pointer_sequence_quiet operations body BODY) OUTER)
    ltac:(intros i I; exact (proj1 (proj1 (@INNER i I))))
    ltac:(intros i le before next last I ROW AGREEMENT RUN;
      eapply (@memory_parametric_row_decode_framed fe ge locals row cache column inner_bound expression upper body outer_body
        point rows stable base RN RC NC RK NK CK (proj1 (proj2 FRESH)) (proj2 (proj2 FRESH)) ROWS
        (fun i I => conj (proj1 (proj1 (@INNER i I))) (proj2 (@INNER i I))) PURE VALUE
        (@memory_pointer_sequence_normal operations body BODY) (@memory_pointer_sequence_writes operations body BODY) OUTER);
      [|exact I|exact ROW|exact AGREEMENT|exact RUN];
      exact (@memory_affine_pointer_body_decode fe ge locals row cache column inner_bound encoded body geometry scalars pointers
        geometry_limits row_limit column_limit extent operations RN RC NC RK NK CK UNIQUE VALID COVER BODY rows geometry_values
        scalar_values base ROWS ROW_RANGE INNER GEOMETRY_RANGE GEOMETRY_WORDS SCALAR_WORDS))
    ltac:(intros i j before last I J STEP;
      exact (@memory_pointer_sequence_observation_preserved base (([i;j]++parameters)++scalar_values) operations
        (MemoryLocation Mint32 block (Ptrofs.unsigned offset)) before last (@APART i j I J) STEP))
    current memory trace after final outcome
    ltac:(exists 0; split; [pose proof Nat2Z.is_nonneg rows; lia|split; [exact ZERO|split; assumption]]) SOURCE)
    as [TARGET [i [IR [ROW [AGREEMENT LOAD]]]]].
  split; assumption.
Qed.
End CACHE.

(** Readiness before stability: the first actual source row supports body-only
    register observations. This theorem has no write-separation assumption and
    does not manufacture a cached-source execution. *)
Theorem memory_affine_pointer_loaded_first_words fe ge locals temps memory row parameter column inner_bound expression
  upper body outer_body after final geometry scalars limits layout extent operations :
  column <> inner_bound -> pure_scalar expression ->
  expression_test (loaded_bound_test row parameter) (Entry ge locals temps memory) true ->
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
  exec_stmt fe ge locals temps memory (loaded_bound_loop row parameter outer_body) E0 after final Out_normal ->
  forall identifier, In identifier (geometry++scalars) -> exists word, temps ! identifier = Some (Vint word).
Proof.
  intros CK PURE ACTIVE VALUE POSITIVE SAFE PROTECTED OUTER BODY VALID ADDRESS_USED SCALAR_USED SOURCE.
  assert (OUTER_NORMAL : normal_statement outer_body = true)
    by (exact (@memory_parametric_outer_normal column inner_bound expression body outer_body
      (@memory_pointer_sequence_quiet operations body BODY) OUTER)).
  assert (OUTER_QUIET : quiet_statement outer_body = true).
  { apply flatten_quiet_certificate; rewrite OUTER; constructor; [reflexivity|].
    constructor; [reflexivity|constructor; [|constructor]].
    cbn [quiet_statement frontend_counted_loop counter_increment]; rewrite (@memory_pointer_sequence_quiet operations body BODY); reflexivity. }
  destruct (@strict_active_iteration fe ge locals row (loaded_bound_test row parameter) outer_body temps memory after final
    OUTER_NORMAL OUTER_QUIET ACTIVE SOURCE) as [next [last [incremented [rest [ROW _]]]]].
  destruct (@memory_parametric_first_inner_body fe ge locals temps memory column inner_bound expression upper body outer_body
    next last (geometry++scalars) CK (@memory_pointer_sequence_normal operations body BODY)
    (@memory_pointer_sequence_writes operations body BODY) PURE VALUE POSITIVE SAFE PROTECTED OUTER ROW)
    as [leaf [body_after [body_final [FRAME RUN]]]].
  apply flatten_region_execution in RUN; rewrite BODY in RUN.
  intros identifier MEMBER; apply in_app_iff in MEMBER as [ADDRESS|SCALAR].
  - destruct (ADDRESS_USED identifier ADDRESS) as [operation [MEMBER USED]].
    destruct (@memory_pointer_sequence_address_words limits operations layout scalars extent fe ge locals identifier
      VALID leaf memory body_after body_final RUN operation MEMBER USED) as [word WORD].
    exists word; rewrite FRAME in WORD by (apply in_or_app; left; exact ADDRESS); exact WORD.
  - destruct (SCALAR_USED identifier SCALAR) as [operation [index [MEMBER [LOOKUP USED]]]].
    destruct (@memory_multi_pointer_sequence_used_register limits operations layout scalars extent fe ge locals
      identifier index VALID LOOKUP leaf memory body_after body_final RUN operation MEMBER USED) as [word WORD].
    exists word; rewrite FRAME in WORD by (apply in_or_app; right; exact SCALAR); exact WORD.
Qed.

Print Assumptions memory_affine_pointer_loaded_source_cached.
Print Assumptions memory_affine_pointer_loaded_first_words.
