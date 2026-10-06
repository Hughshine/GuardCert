From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightCondition ClightPureExpr ClightRectangularStore ClightTempFootprint.
From GuardMemory Require Import GuardMemoryArrayBackend GuardMemoryAffineSourceExpressions GuardMemoryAffineAddressSpecialization
  GuardMemoryAffineCursorProbes GuardMemoryAffineWriteSeparation GuardMemoryNaryCompute GuardMemoryNaryAffineAccess
  GuardMemoryNaryAffineExpressions GuardMemoryAffineChunkWriteSeparation GuardMemoryAffineRowSeparation.
From GuardInterface Require Import ClightCursorSpecialization ClightNestedCursorScan ClightDependentBoundSyntax
  ClightDependentHeaderObservations ClightLoadedBoundSyntax ClightWordChunkSeparation.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Runtime addresses retain both private coordinates. Logical substitution
    recovers the previous constant-coordinate write probes exactly. *)
Fixpoint memory_affine_nested_cursor_form row column outer inner expression :=
  match expression with
  | MemorySourceTemp identifier => if peq identifier row then MemorySourceTemp outer else
      if peq identifier column then MemorySourceTemp inner else expression
  | MemorySourceConstant _ => expression
  | MemorySourceAdd first second => MemorySourceAdd
      (memory_affine_nested_cursor_form row column outer inner first) (memory_affine_nested_cursor_form row column outer inner second)
  | MemorySourceSub first second => MemorySourceSub
      (memory_affine_nested_cursor_form row column outer inner first) (memory_affine_nested_cursor_form row column outer inner second)
  | MemorySourceScale factor value => MemorySourceScale factor (memory_affine_nested_cursor_form row column outer inner value)
  | MemorySourceScaleLeft factor value => MemorySourceScaleLeft factor (memory_affine_nested_cursor_form row column outer inner value)
  end.

Theorem memory_affine_nested_outer_specialized row column outer inner expression i :
  0 <= i -> outer <> inner ->
  (forall identifier, In identifier (memory_source_affine_reads expression) ->
    identifier <> row -> identifier <> column -> identifier <> outer) ->
  cursor_expression_at outer i (memory_source_affine_code (memory_affine_nested_cursor_form row column outer inner expression)) =
    memory_source_affine_code (memory_affine_cursor_form row column i inner expression).
Proof.
  intros I DISTINCT; induction expression; intros FRESH;
    cbn [memory_affine_nested_cursor_form memory_affine_cursor_form memory_source_affine_code].
  - destruct (peq identifier row) as [ROW|ROW].
    + cbn [memory_source_affine_code cursor_expression_at]; destruct (peq outer outer); [|congruence].
      unfold rect_constant; assert (FLAG : (i <? 0)=false) by (apply Z.ltb_ge; lia); rewrite FLAG; reflexivity.
    + destruct (peq identifier column) as [COLUMN|COLUMN]; cbn [memory_source_affine_code cursor_expression_at].
      * destruct (peq inner outer); [congruence|reflexivity].
      * destruct (peq identifier outer) as [SAME|OTHER]; [|reflexivity].
        exfalso; apply (@FRESH identifier ltac:(cbn; auto) ROW COLUMN); exact SAME.
  - apply cursor_expression_constant.
  - cbn [operand_sum cursor_expression_at]; rewrite IHexpression1,IHexpression2; [reflexivity| |].
    all: intros identifier MEMBER; apply FRESH; apply in_or_app; auto.
  - cbn [cursor_expression_at]; rewrite IHexpression1,IHexpression2; [reflexivity| |].
    all: intros identifier MEMBER; apply FRESH; apply in_or_app; auto.
  - cbn [operand_product cursor_expression_at]; rewrite cursor_expression_constant,IHexpression;
      [reflexivity|exact FRESH].
  - cbn [cursor_expression_at]; rewrite cursor_expression_constant,IHexpression; [reflexivity|exact FRESH].
Qed.

Definition memory_affine_nested_cursor_operation_fresh row column outer inner operation :=
  memory_affine_cursor_operation_fresh row column outer operation /\
  memory_affine_cursor_operation_fresh row column inner operation.
Definition memory_affine_nested_cursor_write_address row column outer inner operation :=
  Ebinop Oadd (Etempvar (memory_nary_access_array (memory_nary_compute_write operation)) (Tpointer type_int32s noattr))
    (memory_source_affine_code (memory_affine_nested_cursor_form row column outer inner
      (memory_nary_access_expression (memory_nary_compute_write operation)))) (Tpointer type_int32s noattr).

Lemma memory_affine_nested_cursor_write_outer row column outer inner operation i :
  0 <= i -> outer <> inner -> memory_affine_nested_cursor_operation_fresh row column outer inner operation ->
  cursor_expression_at outer i (memory_affine_nested_cursor_write_address row column outer inner operation) =
    memory_affine_cursor_write_address row column i inner operation.
Proof.
  intros I DISTINCT [[POINTER WORDS] REST]; unfold memory_affine_nested_cursor_write_address,memory_affine_cursor_write_address.
  cbn [cursor_expression_at]; destruct (peq (memory_nary_access_array (memory_nary_compute_write operation)) outer);
    [contradiction|].
  rewrite memory_affine_nested_outer_specialized by assumption; reflexivity.
Qed.

Fixpoint memory_affine_nested_cursor_chunk_probe row column outer inner address wide operations :=
  match operations with
  | [] => Decision true
  | operation::rest => decision_bind
      (word_chunk_separation (memory_affine_nested_cursor_write_address row column outer inner operation) address wide)
      (memory_affine_nested_cursor_chunk_probe row column outer inner address wide rest) (Decision false)
  end.
Definition memory_affine_nested_cursor_dependent_probe row column outer inner root pointer_cache operations :=
  decision_bind (memory_affine_nested_cursor_chunk_probe row column outer inner (dependent_pointer_cell_address root) Archi.ptr64 operations)
    (memory_affine_nested_cursor_chunk_probe row column outer inner (signed_pointer_temp pointer_cache) false operations) (Decision false).

Theorem memory_affine_nested_cursor_chunk_outer row column outer inner address wide operations i :
  0 <= i -> outer <> inner -> Forall (memory_affine_nested_cursor_operation_fresh row column outer inner) operations ->
  cursor_expression_at outer i address=address ->
  cursor_tree_at outer i (memory_affine_nested_cursor_chunk_probe row column outer inner address wide operations) =
    memory_affine_cursor_chunk_probe row column i inner address wide operations.
Proof.
  intros I DISTINCT FRESH ADDRESS; induction FRESH; cbn [memory_affine_nested_cursor_chunk_probe memory_affine_cursor_chunk_probe cursor_tree_at].
  - reflexivity.
  - rewrite cursor_tree_at_bind,cursor_word_chunk_separation,ADDRESS,memory_affine_nested_cursor_write_outer by assumption.
    rewrite IHFRESH; reflexivity.
Qed.

Theorem memory_affine_nested_cursor_dependent_outer row column outer inner root pointer_cache operations i :
  0 <= i -> outer <> inner -> root <> outer -> pointer_cache <> outer ->
  Forall (memory_affine_nested_cursor_operation_fresh row column outer inner) operations ->
  cursor_tree_at outer i (memory_affine_nested_cursor_dependent_probe row column outer inner root pointer_cache operations) =
    memory_affine_cursor_dependent_probe row column i inner root pointer_cache operations.
Proof.
  intros I DISTINCT ROOT POINTER FRESH; unfold memory_affine_nested_cursor_dependent_probe,memory_affine_cursor_dependent_probe.
  rewrite cursor_tree_at_bind.
  rewrite !memory_affine_nested_cursor_chunk_outer by
    (try assumption; unfold dependent_pointer_cell_address,signed_pointer_cell_temp,signed_pointer_temp;
      cbn [cursor_expression_at]; destruct (peq root outer); destruct (peq pointer_cache outer); congruence).
  reflexivity.
Qed.

Definition memory_affine_nested_cursor_bound row column outer inner expression :=
  cursor_expression_at inner 0 (memory_source_affine_code (memory_affine_nested_cursor_form row column outer inner expression)).
Definition memory_affine_nested_cursor_activity row column outer inner expression :=
  Ebinop Olt (Etempvar inner type_int32s) (memory_affine_nested_cursor_bound row column outer inner expression) type_int32s.

Theorem memory_affine_nested_cursor_bound_outer row column outer inner expression i :
  0 <= i -> outer <> inner ->
  (forall identifier, In identifier (memory_source_affine_reads expression) ->
    identifier <> row -> identifier <> column -> identifier <> outer /\ identifier <> inner) ->
  cursor_expression_at outer i (memory_affine_nested_cursor_bound row column outer inner expression) =
    memory_affine_row_bound row column i expression.
Proof.
  intros I DISTINCT FRESH; unfold memory_affine_nested_cursor_bound,memory_affine_row_bound.
  rewrite cursor_expression_at_commute by exact DISTINCT.
  rewrite memory_affine_nested_outer_specialized by
    (try assumption; intros identifier READ ROW COLUMN; exact (proj1 (@FRESH identifier READ ROW COLUMN))).
  rewrite memory_affine_cursor_form_specialized by
    (try lia; intros identifier READ ROW COLUMN; exact (proj2 (@FRESH identifier READ ROW COLUMN))).
  reflexivity.
Qed.

Lemma memory_affine_nested_cursor_bound_inner row column outer inner expression j :
  cursor_expression_at inner j (memory_affine_nested_cursor_bound row column outer inner expression) =
    memory_affine_nested_cursor_bound row column outer inner expression.
Proof.
  apply cursor_expression_at_fresh; unfold memory_affine_nested_cursor_bound; intro MEMBER.
  destruct (@cursor_expression_at_reads inner 0 _ inner MEMBER) as [READ OTHER]; apply OTHER; reflexivity.
Qed.

Print Assumptions memory_affine_nested_outer_specialized.
Print Assumptions memory_affine_nested_cursor_write_outer.
Print Assumptions memory_affine_nested_cursor_chunk_outer.
Print Assumptions memory_affine_nested_cursor_dependent_outer.
Print Assumptions memory_affine_nested_cursor_bound_outer.
Print Assumptions memory_affine_nested_cursor_bound_inner.
