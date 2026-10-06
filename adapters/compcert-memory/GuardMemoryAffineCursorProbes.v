From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightCondition ClightPureExpr ClightRectangularStore ClightTempFootprint.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions GuardMemoryAffineAddressSpecialization
  GuardMemoryArrayBackend GuardMemoryAffineWriteSeparation GuardMemoryNaryCompute GuardMemoryNaryAffineAccess
  GuardMemoryNaryAffineExpressions GuardMemoryAffineChunkWriteSeparation.
From GuardInterface Require Import ClightCursorSpecialization ClightDependentBoundSyntax
  ClightDependentHeaderObservations ClightLoadedBoundSyntax ClightWordChunkSeparation.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A single symbolic column cursor replaces the generated per-column
    constants. The row remains a parameter here, ready for outer-loop lowering. *)
Fixpoint memory_affine_cursor_form row column i cursor expression :=
  match expression with
  | MemorySourceTemp identifier => if peq identifier row then MemorySourceConstant i else
      if peq identifier column then MemorySourceTemp cursor else expression
  | MemorySourceConstant _ => expression
  | MemorySourceAdd first second => MemorySourceAdd
      (memory_affine_cursor_form row column i cursor first) (memory_affine_cursor_form row column i cursor second)
  | MemorySourceSub first second => MemorySourceSub
      (memory_affine_cursor_form row column i cursor first) (memory_affine_cursor_form row column i cursor second)
  | MemorySourceScale factor value => MemorySourceScale factor (memory_affine_cursor_form row column i cursor value)
  | MemorySourceScaleLeft factor value => MemorySourceScaleLeft factor (memory_affine_cursor_form row column i cursor value)
  end.

Lemma cursor_expression_constant cursor index value :
  cursor_expression_at cursor index (rect_constant value)=rect_constant value.
Proof. unfold rect_constant; destruct (value <? 0); reflexivity. Qed.

Theorem memory_affine_cursor_form_specialized row column i cursor expression j :
  0 <= j ->
  (forall identifier, In identifier (memory_source_affine_reads expression) ->
    identifier <> row -> identifier <> column -> identifier <> cursor) ->
  cursor_expression_at cursor j (memory_source_affine_code (memory_affine_cursor_form row column i cursor expression)) =
    memory_source_affine_code (memory_affine_at row column i j expression).
Proof.
  intros J; induction expression; intros FRESH;
    cbn [memory_affine_cursor_form memory_affine_at memory_source_affine_code].
  - destruct (peq identifier row) as [SAME|ROW]; [apply cursor_expression_constant|].
    destruct (peq identifier column) as [SAME|COLUMN].
    + cbn [memory_source_affine_code cursor_expression_at]; destruct (peq cursor cursor); [|congruence].
      unfold rect_constant;
        assert (FLAG : (j <? 0)=false) by (apply Z.ltb_ge; lia); rewrite FLAG; reflexivity.
    + cbn [memory_source_affine_code cursor_expression_at]; destruct (peq identifier cursor) as [SAME|OTHER]; [|reflexivity].
      exfalso; apply (FRESH identifier ltac:(cbn; auto) ROW COLUMN); exact SAME.
  - apply cursor_expression_constant.
  - cbn [operand_sum cursor_expression_at]; rewrite IHexpression1,IHexpression2; [reflexivity| |].
    all: intros identifier MEMBER; apply FRESH; apply in_or_app; auto.
  - cbn [cursor_expression_at]; rewrite IHexpression1,IHexpression2; [reflexivity| |].
    all: intros identifier MEMBER; apply FRESH; apply in_or_app; auto.
  - cbn [operand_product cursor_expression_at]; rewrite cursor_expression_constant,IHexpression;
      [reflexivity|exact FRESH].
  - cbn [cursor_expression_at]; rewrite cursor_expression_constant,IHexpression; [reflexivity|exact FRESH].
Qed.

Definition memory_affine_cursor_write_address row column i cursor operation :=
  Ebinop Oadd (Etempvar (memory_nary_access_array (memory_nary_compute_write operation)) (Tpointer type_int32s noattr))
    (memory_source_affine_code (memory_affine_cursor_form row column i cursor
      (memory_nary_access_expression (memory_nary_compute_write operation)))) (Tpointer type_int32s noattr).
Definition memory_affine_cursor_operation_fresh row column cursor operation :=
  memory_nary_access_array (memory_nary_compute_write operation) <> cursor /\
  forall identifier, In identifier (memory_source_affine_reads
    (memory_nary_access_expression (memory_nary_compute_write operation))) ->
    identifier <> row -> identifier <> column -> identifier <> cursor.

Lemma memory_affine_cursor_write_address_specialized row column i cursor operation j :
  0 <= j -> memory_affine_cursor_operation_fresh row column cursor operation ->
  cursor_expression_at cursor j (memory_affine_cursor_write_address row column i cursor operation) =
    memory_affine_write_address row column i j operation.
Proof.
  intros J [POINTER WORDS]; unfold memory_affine_cursor_write_address,memory_affine_write_address,memory_affine_address_at.
  cbn [cursor_expression_at]; destruct (peq (memory_nary_access_array (memory_nary_compute_write operation)) cursor);
    [contradiction|].
  rewrite memory_affine_cursor_form_specialized; [reflexivity|exact J|exact WORDS].
Qed.

Fixpoint memory_affine_cursor_chunk_probe row column i cursor address wide operations :=
  match operations with
  | [] => Decision true
  | operation::rest => decision_bind
      (word_chunk_separation (memory_affine_cursor_write_address row column i cursor operation) address wide)
      (memory_affine_cursor_chunk_probe row column i cursor address wide rest) (Decision false)
  end.
Definition memory_affine_cursor_dependent_probe row column i cursor root pointer_cache operations :=
  decision_bind (memory_affine_cursor_chunk_probe row column i cursor (dependent_pointer_cell_address root) Archi.ptr64 operations)
    (memory_affine_cursor_chunk_probe row column i cursor (signed_pointer_temp pointer_cache) false operations) (Decision false).

Lemma cursor_word_chunk_separation cursor index code address wide :
  cursor_tree_at cursor index (word_chunk_separation code address wide) =
  word_chunk_separation (cursor_expression_at cursor index code)
    (cursor_expression_at cursor index address) wide.
Proof. destruct wide; reflexivity. Qed.

Theorem memory_affine_cursor_chunk_probe_specialized row column i cursor address wide operations j :
  0 <= j -> Forall (memory_affine_cursor_operation_fresh row column cursor) operations ->
  cursor_expression_at cursor j address = address ->
  cursor_tree_at cursor j (memory_affine_cursor_chunk_probe row column i cursor address wide operations) =
    memory_affine_chunk_probe row column i j address wide operations.
Proof.
  intros J FRESH ADDRESS; induction FRESH; cbn [memory_affine_cursor_chunk_probe memory_affine_chunk_probe cursor_tree_at].
  - reflexivity.
  - rewrite cursor_tree_at_bind,cursor_word_chunk_separation,ADDRESS,
      memory_affine_cursor_write_address_specialized by assumption.
    rewrite IHFRESH; reflexivity.
Qed.

Theorem memory_affine_cursor_dependent_probe_specialized row column i cursor root pointer_cache operations j :
  0 <= j -> root <> cursor -> pointer_cache <> cursor ->
  Forall (memory_affine_cursor_operation_fresh row column cursor) operations ->
  cursor_tree_at cursor j (memory_affine_cursor_dependent_probe row column i cursor root pointer_cache operations) =
    memory_affine_dependent_write_probe row column i j root pointer_cache operations.
Proof.
  intros J ROOT POINTER FRESH; unfold memory_affine_cursor_dependent_probe,memory_affine_dependent_write_probe.
  rewrite cursor_tree_at_bind.
  rewrite !memory_affine_cursor_chunk_probe_specialized by
    (try assumption; unfold dependent_pointer_cell_address,signed_pointer_cell_temp,signed_pointer_temp;
      cbn [cursor_expression_at]; destruct (peq root cursor); destruct (peq pointer_cache cursor); congruence).
  reflexivity.
Qed.

Print Assumptions cursor_expression_constant.
Print Assumptions memory_affine_cursor_form_specialized.
Print Assumptions memory_affine_cursor_write_address_specialized.
Print Assumptions cursor_word_chunk_separation.
Print Assumptions memory_affine_cursor_chunk_probe_specialized.
Print Assumptions memory_affine_cursor_dependent_probe_specialized.
