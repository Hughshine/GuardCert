From Stdlib Require Import ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightPureExpr ClightRectangularStore.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition indexed_array_lvalue d array index :=
  Ederef (Ebinop Oadd (Evar array (rect_array_type d)) index (Tpointer type_int32s noattr)) type_int32s.

(** The language exposes typed, pure index evaluation and bounds. Neither
    instruction scheduling nor the guard compiler interprets this expression. *)
Section INDEX.
Variable d : rectangle_shape.
Hypothesis VALID : rectangle_layout_valid d.
Variable index : expr.
Hypothesis INDEX_TYPE : typeof index = type_int32s.
Hypothesis INDEX_PURE : pure_scalar index.

Lemma indexed_array_lvalue_evaluation ge locals le memory array block offset :
  rect_array_binding d ge locals array block ->
  eval_expr ge locals le memory index (Vint (Int.repr offset)) ->
  0 <= offset < rectangle_extent d ->
  eval_lvalue ge locals le memory (indexed_array_lvalue d array index)
    block (Ptrofs.repr (4 * offset)) Full.
Proof.
  intros ARRAY INDEX BOUND; apply eval_Ederef.
  eapply eval_Ebinop with (v1 := Vptr block Ptrofs.zero) (v2 := Vint (Int.repr offset)).
  - apply rect_reference_evaluation; exact ARRAY.
  - exact INDEX.
  - cbn [typeof]; rewrite INDEX_TYPE; apply (@rect_pointer_add d VALID); exact BOUND.
Qed.
Lemma indexed_array_lvalue_inverse ge locals le memory array offset block ofs field :
  eval_expr ge locals le memory index (Vint (Int.repr offset)) ->
  0 <= offset < rectangle_extent d ->
  eval_lvalue ge locals le memory (indexed_array_lvalue d array index) block ofs field ->
  rect_array_binding d ge locals array block /\ ofs = Ptrofs.repr (4 * offset) /\ field = Full.
Proof.
  intros INDEX BOUND RUN; inversion RUN; subst.
  match goal with POINTER : eval_expr _ _ _ _ (Ebinop Oadd _ _ _) _ |- _ => inversion POINTER; subst end;
    try match goal with BAD : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion BAD end.
  match goal with ARRAY : eval_expr _ _ _ _ (Evar _ _) ?v,
    ACTUAL : eval_expr _ _ _ _ index ?idx |- _ =>
    destruct (@rect_reference_inverse d ge locals le memory array v ARRAY) as [actual_block [BINDING SAME]]; subst v;
    pose proof (@pure_scalar_determinate index INDEX_PURE ge locals le memory
      idx (Vint (Int.repr offset)) ACTUAL INDEX) as INDEX_VALUE; subst idx
  end.
  match goal with SEM : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
    cbn [typeof] in SEM; rewrite INDEX_TYPE in SEM;
    rewrite (@rect_pointer_add d VALID ge memory actual_block offset BOUND) in SEM;
    inversion SEM; subst
  end; auto.
Qed.
Lemma indexed_array_load_evaluation ge locals le memory array block offset value :
  rect_array_binding d ge locals array block ->
  eval_expr ge locals le memory index (Vint (Int.repr offset)) ->
  0 <= offset < rectangle_extent d ->
  Mem.load Mint32 memory block (4 * offset) = Some value ->
  eval_expr ge locals le memory (indexed_array_lvalue d array index) value.
Proof.
  intros ARRAY INDEX BOUND LOAD; eapply eval_Elvalue;
    [apply indexed_array_lvalue_evaluation; eauto|].
  apply deref_loc_value with (chunk := Mint32); [reflexivity|].
  cbn [Mem.loadv]; rewrite Ptrofs.unsigned_repr by
    (apply (@rect_small_offset_bound d VALID); lia).
  destruct (zle (4 * offset + size_chunk Mint32) Ptrofs.modulus); [exact LOAD|].
  exfalso; pose proof (@rect_small_offset_bound d VALID (4 * offset + 4) ltac:(lia)) as END.
  unfold Ptrofs.max_unsigned in END; change (size_chunk Mint32) with 4 in *; lia.
Qed.
Lemma indexed_array_load_inverse ge locals le memory array offset value :
  eval_expr ge locals le memory index (Vint (Int.repr offset)) ->
  0 <= offset < rectangle_extent d ->
  eval_expr ge locals le memory (indexed_array_lvalue d array index) value ->
  exists block, rect_array_binding d ge locals array block /\ Mem.load Mint32 memory block (4 * offset) = Some value.
Proof.
  intros INDEX BOUND EVAL; inversion EVAL; subst.
  match goal with LVALUE : eval_lvalue _ _ _ _ (indexed_array_lvalue _ _ _) _ _ _ |- _ =>
    destruct (@indexed_array_lvalue_inverse ge locals le memory array offset _ _ _ INDEX BOUND LVALUE)
      as [ARRAY [OFFSET FIELD]]; subst
  end.
  match goal with DEREF : deref_loc _ _ _ _ _ _ |- _ => inversion DEREF; subst; try discriminate end.
  match goal with MODE : access_mode _ = By_value _ |- _ => inversion MODE; subst end.
  match goal with LOAD : Mem.loadv _ _ _ = Some _ |- _ =>
    cbn [Mem.loadv] in LOAD; rewrite Ptrofs.unsigned_repr in LOAD by
      (apply (@rect_small_offset_bound d VALID); lia);
    destruct (zle (4 * offset + size_chunk Mint32) Ptrofs.modulus); try discriminate LOAD
  end; eauto.
Qed.
End INDEX.
Print Assumptions indexed_array_load_evaluation.
Print Assumptions indexed_array_load_inverse.
