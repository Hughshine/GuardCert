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
From GuardMemory Require Import GuardMemoryWriteReceipts.
From GuardInterface Require Import ClightStorePermissions.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightStrictIteration
  ClightAffineLoadedBoundTransport.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The observed bound may be outside every modeled body buffer. The extended
    frame protects its pointer binding; a domain check supplies physical write
    separation. No membership of this pointer in the array model is needed. *)
Section EXTERNAL.
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
Let body_stable := pointers++((cache::geometry)++scalars).
Let stable := parameter::body_stable.
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
Hypothesis POINTER : base ! parameter = Some (Vptr block offset).
Hypothesis APART : forall i j, 0 <= i < Z.of_nat rows -> 0 <= j < upper i ->
  memory_pointer_writes_apart_observation base (([i;j]++parameters)++scalar_values) operations
    (MemoryLocation Mint32 block (Ptrofs.unsigned offset)).

Lemma memory_affine_pointer_external_body_decode i j temps memory after final :
  0 <= i < Z.of_nat rows -> 0 <= j < upper i ->
  temps ! row = Some (Vint (Int.repr i)) -> temps ! column = Some (Vint (Int.repr j)) ->
  temp_agree stable base temps ->
  exec_stmt fe ge locals temps memory body E0 after final Out_normal ->
  point i j memory final /\ after = temps.
Proof.
  intros I J ROW COLUMN FRAME RUN.
  eapply (@memory_affine_pointer_body_decode fe ge locals row cache column inner_bound encoded body geometry scalars pointers
    geometry_limits row_limit column_limit extent operations RN RC NC RK NK CK UNIQUE VALID COVER BODY rows geometry_values
    scalar_values base ROWS ROW_RANGE INNER GEOMETRY_RANGE GEOMETRY_WORDS SCALAR_WORDS);
    [exact I|exact J|exact ROW|exact COLUMN| |exact RUN].
  eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER; unfold stable,body_stable; right; exact MEMBER.
Qed.

Lemma memory_affine_pointer_external_row_decode i current before after final :
  0 <= i < Z.of_nat rows -> current ! row = Some (Vint (Int.repr i)) ->
  temp_agree stable base current ->
  exec_stmt fe ge locals current before outer_body E0 after final Out_normal ->
  counted_iterations (point i) (Z.to_nat (upper i)) 0 before final /\
    after = memory_parametric_settle column inner_bound upper i current.
Proof.
  intros I ROW FRAME RUN.
  assert (FRESH : ~ In column stable /\ ~ In inner_bound stable)
    by (split; intro MEMBER; specialize (@PROTECTED _ MEMBER); tauto).
  eapply (@memory_parametric_row_decode_framed fe ge locals row cache column inner_bound expression upper body outer_body
    point rows stable base RN RC NC RK NK CK (proj1 FRESH) (proj2 FRESH) ROWS
    (fun i I => conj (proj1 (proj1 (@INNER i I))) (proj2 (@INNER i I))) PURE VALUE
    (@memory_pointer_sequence_normal operations body BODY) (@memory_pointer_sequence_writes operations body BODY) OUTER
    memory_affine_pointer_external_body_decode); eassumption.
Qed.

(** Actual source execution yields every write receipt in this row at the
    original guard memory. No separation from the observed bound is assumed.
    The bound can even be changed by this row's last store. *)
Theorem memory_affine_pointer_external_row_write_receipts i current original before after final :
  0 <= i < Z.of_nat rows -> current ! row = Some (Vint (Int.repr i)) ->
  temp_agree stable base current -> memory_accesses_back original before ->
  exec_stmt fe ge locals current before outer_body E0 after final Out_normal ->
  forall j, 0 <= j < upper i ->
    Forall (memory_write_receipt base (([i;j]++parameters)++scalar_values) original) operations.
Proof.
  intros I ROW FRAME BACK RUN j J.
  destruct (memory_affine_pointer_external_row_decode I ROW FRAME RUN) as [ITER EXIT].
  pose proof (@counted_pointer_sequence_write_receipts base (fun j => (([i;j]++parameters)++scalar_values)) operations
    (Z.to_nat (upper i)) 0 before final ITER j
    ltac:(rewrite Z2Nat.id by (pose proof (@INNER i I); lia); lia)) as RECEIPTS.
  eapply Forall_impl; [|exact RECEIPTS].
  intros item RECEIPT; eapply memory_write_receipt_back; [exact BACK|exact RECEIPT].
Qed.

Theorem memory_affine_pointer_loaded_external_cached current memory trace after final outcome :
  current ! row = Some (Vint Int.zero) -> temp_agree stable base current ->
  Mem.loadv Mint32 memory (Vptr block offset) = Some (Vint (Int.repr (Z.of_nat rows))) ->
  exec_stmt fe ge locals current memory (loaded_bound_loop row parameter outer_body) trace after final outcome ->
  exec_stmt fe ge locals current memory (frontend_counted_loop row cache outer_body) trace after final outcome /\
    Mem.loadv Mint32 final (Vptr block offset) = Some (Vint (Int.repr (Z.of_nat rows))).
Proof.
  intros ZERO FRAME READ SOURCE.
  assert (FRESH : ~ In row stable /\ ~ In column stable /\ ~ In inner_bound stable)
    by (repeat split; intro MEMBER; specialize (@PROTECTED _ MEMBER); tauto).
  assert (CACHE : base ! cache = Some (Vint (Int.repr (Z.of_nat rows))))
    by (inversion GEOMETRY_WORDS; subst; assumption).
  destruct (@affine_loaded_bound_cached fe ge locals row cache parameter column inner_bound outer_body point upper
    stable base block offset (Z.of_nat rows)
    ltac:(pose proof Nat2Z.is_nonneg rows; unfold signed_range in SIGNED; split; lia)
    RC RK (proj1 (proj2 FRESH)) (proj2 (proj2 FRESH)) (proj1 FRESH)
    ltac:(unfold stable,body_stable; right; apply in_or_app; right; apply in_or_app; left; cbn; auto)
    ltac:(unfold stable; left; reflexivity) CACHE POINTER
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
      exact memory_affine_pointer_external_body_decode)
    ltac:(intros i j before last I J STEP;
      exact (@memory_pointer_sequence_observation_preserved base (([i;j]++parameters)++scalar_values) operations
        (MemoryLocation Mint32 block (Ptrofs.unsigned offset)) before last (@APART i j I J) STEP))
    current memory trace after final outcome
    ltac:(exists 0; split; [pose proof Nat2Z.is_nonneg rows; lia|split; [exact ZERO|split; assumption]]) SOURCE)
    as [TARGET [i [IR [ROW [AGREEMENT LOAD]]]]].
  split; assumption.
Qed.
End EXTERNAL.

Print Assumptions memory_affine_pointer_external_row_decode.
Print Assumptions memory_affine_pointer_external_row_write_receipts.
Print Assumptions memory_affine_pointer_loaded_external_cached.
