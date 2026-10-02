From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.x86_64 Require Import Archi.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightPureExpr CompCertStoreSchedule.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma matrix_small_offset_bound value : 0 <= value <= 16 -> 0 <= value <= Ptrofs.max_unsigned.
Proof.
  intro RANGE; unfold Ptrofs.max_unsigned, Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize.
  destruct Archi.ptr64;
    [change (0 <= value <= 18446744073709551615)|change (0 <= value <= 4294967295)]; lia.
Qed.

(** A native Clight instance for the first affine scheduling example. Every
    memory operation below is an actual CompCert operation. *)
Definition matrix_array_type := Tarray type_int32s 4 noattr.
Definition matrix_constant z := Econst_int (Int.repr z) type_int32s.
Definition matrix_index iterator inner :=
  Ebinop Oadd (Ebinop Omul (Etempvar iterator type_int32s) (matrix_constant 2) type_int32s)
    (Etempvar inner type_int32s) type_int32s.
Definition matrix_value iterator inner :=
  Ebinop Oadd
    (Ebinop Oadd (Ebinop Omul (Etempvar iterator type_int32s) (matrix_constant 10) type_int32s)
      (Etempvar inner type_int32s) type_int32s) (matrix_constant 1) type_int32s.
Definition matrix_lvalue array iterator inner :=
  Ederef (Ebinop Oadd (Evar array matrix_array_type) (matrix_index iterator inner)
    (Tpointer type_int32s noattr)) type_int32s.
Definition matrix_store array iterator inner :=
  Sassign (matrix_lvalue array iterator inner) (matrix_value iterator inner).
Definition matrix_array_binding (ge : genv) locals array block :=
  locals ! array = Some (block, matrix_array_type) \/
  (locals ! array = None /\ Genv.find_symbol ge array = Some block).

Lemma matrix_array_binding_unique ge locals array first second :
  matrix_array_binding ge locals array first -> matrix_array_binding ge locals array second -> first = second.
Proof. intros [FIRST|[ABSENT FIRST]] [SECOND|[ABSENT' SECOND]]; congruence. Qed.

Lemma matrix_index_pure iterator inner : pure_scalar (matrix_index iterator inner).
Proof. repeat constructor. Qed.
Lemma matrix_value_pure iterator inner : pure_scalar (matrix_value iterator inner).
Proof. repeat constructor. Qed.

Lemma matrix_integer_multiply x y :
  Int.mul (Int.repr x) (Int.repr y) = Int.repr (x * y).
Proof. unfold Int.mul; apply Int.eqm_samerepr; apply Int.eqm_mult; apply Int.eqm_sym; apply Int.eqm_unsigned_repr. Qed.
Lemma matrix_integer_add x y : Int.add (Int.repr x) (Int.repr y) = Int.repr (x + y).
Proof. unfold Int.add; apply Int.eqm_samerepr; apply Int.eqm_add; apply Int.eqm_sym; apply Int.eqm_unsigned_repr. Qed.

Lemma matrix_index_evaluation ge locals le memory iterator inner i j :
  le ! iterator = Some (Vint (Int.repr i)) -> le ! inner = Some (Vint (Int.repr j)) ->
  eval_expr ge locals le memory (matrix_index iterator inner) (Vint (Int.repr (i * 2 + j))).
Proof.
  intros I J; unfold matrix_index, matrix_constant.
  eapply eval_Ebinop with (v1 := Vint (Int.repr (i * 2))) (v2 := Vint (Int.repr j)).
  - eapply eval_Ebinop with (v1 := Vint (Int.repr i)) (v2 := Vint (Int.repr 2));
      [constructor; exact I|constructor|].
    change (Some (Vint (Int.mul (Int.repr i) (Int.repr 2))) = Some (Vint (Int.repr (i * 2)))).
    rewrite matrix_integer_multiply; reflexivity.
  - constructor; exact J.
  - change (Some (Vint (Int.add (Int.repr (i * 2)) (Int.repr j))) =
      Some (Vint (Int.repr (i * 2 + j)))). rewrite matrix_integer_add; reflexivity.
Qed.
Lemma matrix_value_evaluation ge locals le memory iterator inner i j :
  le ! iterator = Some (Vint (Int.repr i)) -> le ! inner = Some (Vint (Int.repr j)) ->
  eval_expr ge locals le memory (matrix_value iterator inner) (Vint (Int.repr (i * 10 + j + 1))).
Proof.
  intros I J; unfold matrix_value, matrix_constant.
  eapply eval_Ebinop with (v1 := Vint (Int.repr (i * 10 + j))) (v2 := Vint (Int.repr 1)).
  - eapply eval_Ebinop with (v1 := Vint (Int.repr (i * 10))) (v2 := Vint (Int.repr j)).
    + eapply eval_Ebinop with (v1 := Vint (Int.repr i)) (v2 := Vint (Int.repr 10));
        [constructor; exact I|constructor|].
      change (Some (Vint (Int.mul (Int.repr i) (Int.repr 10))) = Some (Vint (Int.repr (i * 10)))).
      rewrite matrix_integer_multiply; reflexivity.
    + constructor; exact J.
    + change (Some (Vint (Int.add (Int.repr (i * 10)) (Int.repr j))) =
        Some (Vint (Int.repr (i * 10 + j)))). rewrite matrix_integer_add; reflexivity.
  - constructor.
  - change (Some (Vint (Int.add (Int.repr (i * 10 + j)) (Int.repr 1))) =
      Some (Vint (Int.repr (i * 10 + j + 1)))). rewrite matrix_integer_add; reflexivity.
Qed.

Lemma matrix_pointer_add ge memory block index : 0 <= index <= 3 ->
  sem_binary_operation ge Oadd (Vptr block Ptrofs.zero) matrix_array_type
    (Vint (Int.repr index)) type_int32s memory = Some (Vptr block (Ptrofs.repr (4 * index))).
Proof.
  intro RANGE.
  change (Some (Vptr block (Ptrofs.add Ptrofs.zero
    (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.repr (Int.signed (Int.repr index)))))) =
    Some (Vptr block (Ptrofs.repr (4 * index)))).
  rewrite Int.signed_repr by (change (-2147483648 <= index <= 2147483647); lia).
  rewrite Ptrofs.add_zero_l; unfold Ptrofs.mul.
  rewrite (Ptrofs.unsigned_repr 4) by (apply matrix_small_offset_bound; lia).
  rewrite (Ptrofs.unsigned_repr index) by (apply matrix_small_offset_bound; lia).
  reflexivity.
Qed.

Lemma matrix_reference_evaluation ge locals le memory array block :
  matrix_array_binding ge locals array block ->
  eval_expr ge locals le memory (Evar array matrix_array_type) (Vptr block Ptrofs.zero).
Proof.
  intros [LOCAL|[ABSENT GLOBAL]].
  - eapply eval_Elvalue; [apply eval_Evar_local; exact LOCAL|apply deref_loc_reference; reflexivity].
  - eapply eval_Elvalue with (loc := block) (ofs := Ptrofs.zero) (bf := Full).
    + apply eval_Evar_global; assumption.
    + apply deref_loc_reference; reflexivity.
Qed.

Lemma matrix_reference_inverse ge locals le memory array value :
  eval_expr ge locals le memory (Evar array matrix_array_type) value ->
  exists block, matrix_array_binding ge locals array block /\ value = Vptr block Ptrofs.zero.
Proof.
  intro EVAL; inversion EVAL; subst.
  match goal with DEREF : deref_loc _ _ _ _ _ _ |- _ => inversion DEREF; subst; try discriminate end.
  all: match goal with LVALUE : eval_lvalue _ _ _ _ (Evar _ _) _ _ _ |- _ => inversion LVALUE; subst end.
  - eexists; split; [left; eassumption|reflexivity].
  - eexists; split; [right; split; eassumption|reflexivity].
Qed.

Lemma matrix_lvalue_evaluation ge locals le memory array iterator inner block i j :
  matrix_array_binding ge locals array block ->
  le ! iterator = Some (Vint (Int.repr i)) -> le ! inner = Some (Vint (Int.repr j)) ->
  0 <= i <= 1 -> 0 <= j <= 1 ->
  eval_lvalue ge locals le memory (matrix_lvalue array iterator inner)
    block (Ptrofs.repr (4 * (i * 2 + j))) Full.
Proof.
  intros ARRAY I J RI RJ; apply eval_Ederef.
  eapply eval_Ebinop with (v1 := Vptr block Ptrofs.zero) (v2 := Vint (Int.repr (i * 2 + j)));
    [apply matrix_reference_evaluation; exact ARRAY|
    apply matrix_index_evaluation; assumption|apply matrix_pointer_add; lia].
Qed.

Lemma matrix_lvalue_inverse ge locals le memory array iterator inner i j block offset bitfield :
  le ! iterator = Some (Vint (Int.repr i)) -> le ! inner = Some (Vint (Int.repr j)) ->
  0 <= i <= 1 -> 0 <= j <= 1 ->
  eval_lvalue ge locals le memory (matrix_lvalue array iterator inner) block offset bitfield ->
  matrix_array_binding ge locals array block /\ offset = Ptrofs.repr (4 * (i * 2 + j)) /\ bitfield = Full.
Proof.
  intros I J RI RJ RUN; inversion RUN; subst.
  match goal with POINTER : eval_expr _ _ _ _ (Ebinop Oadd _ _ _) _ |- _ => inversion POINTER; subst end;
    try match goal with BAD : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion BAD end.
  match goal with ARRAY : eval_expr _ _ _ _ (Evar _ _) ?v,
    INDEX : eval_expr _ _ _ _ (matrix_index _ _) ?idx |- _ =>
    destruct (@matrix_reference_inverse ge locals le memory array v ARRAY) as [actual_block [BINDING SAME]]; subst v;
    pose proof (@pure_scalar_determinate _ (matrix_index_pure iterator inner) ge locals le memory
      idx (Vint (Int.repr (i * 2 + j))) INDEX
      (@matrix_index_evaluation ge locals le memory iterator inner i j I J)) as INDEX_VALUE; subst idx
  end.
  match goal with SEM : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
    cbn [typeof matrix_index] in SEM;
    rewrite (@matrix_pointer_add ge memory actual_block (i * 2 + j) ltac:(lia)) in SEM;
    inversion SEM; subst
  end; auto.
Qed.

Lemma matrix_store_evaluation fe ge locals le memory array iterator inner block i j memory' :
  matrix_array_binding ge locals array block ->
  le ! iterator = Some (Vint (Int.repr i)) -> le ! inner = Some (Vint (Int.repr j)) ->
  0 <= i <= 1 -> 0 <= j <= 1 ->
  Mem.store Mint32 memory block (4 * (i * 2 + j)) (Vint (Int.repr (i * 10 + j + 1))) = Some memory' ->
  exec_stmt fe ge locals le memory (matrix_store array iterator inner) E0 le memory' Out_normal.
Proof.
  intros ARRAY I J RI RJ STORE; eapply exec_Sassign with
    (loc := block) (ofs := Ptrofs.repr (4 * (i * 2 + j))) (bf := Full)
    (v := Vint (Int.repr (i * 10 + j + 1))) (v2 := Vint (Int.repr (i * 10 + j + 1))).
  - apply matrix_lvalue_evaluation; eauto.
  - apply matrix_value_evaluation; assumption.
  - reflexivity.
  - apply assign_loc_value with (chunk := Mint32); [reflexivity|].
    cbn [Mem.storev]. rewrite Ptrofs.unsigned_repr by (apply matrix_small_offset_bound; lia).
    destruct (zle (4 * (i * 2 + j) + size_chunk Mint32) Ptrofs.modulus); [exact STORE|].
    exfalso; pose proof (@matrix_small_offset_bound (4 * (i * 2 + j) + 4) ltac:(lia)) as END.
    unfold Ptrofs.max_unsigned in END; change (size_chunk Mint32) with 4 in *; lia.
Qed.

Lemma matrix_store_inverse fe ge locals le memory array iterator inner i j trace le' memory' outcome :
  le ! iterator = Some (Vint (Int.repr i)) -> le ! inner = Some (Vint (Int.repr j)) ->
  0 <= i <= 1 -> 0 <= j <= 1 ->
  exec_stmt fe ge locals le memory (matrix_store array iterator inner) trace le' memory' outcome ->
  exists block, matrix_array_binding ge locals array block /\ trace = E0 /\ le' = le /\ outcome = Out_normal /\
    Mem.store Mint32 memory block (4 * (i * 2 + j)) (Vint (Int.repr (i * 10 + j + 1))) = Some memory'.
Proof.
  intros I J RI RJ RUN; inversion RUN; subst.
  match goal with LVALUE : eval_lvalue _ _ ?current _ (matrix_lvalue _ _ _) _ _ _ |- _ =>
    destruct (@matrix_lvalue_inverse ge locals current memory array iterator inner i j _ _ _
      I J RI RJ LVALUE) as [ARRAY [OFFSET FIELD]]; subst
  end.
  match goal with VALUE : eval_expr _ _ ?current _ (matrix_value _ _) ?value |- _ =>
    pose proof (@pure_scalar_determinate _ (matrix_value_pure iterator inner) ge locals current memory
      value (Vint (Int.repr (i * 10 + j + 1))) VALUE
      (@matrix_value_evaluation ge locals current memory iterator inner i j I J)) as SAME; subst value
  end.
  match goal with CAST : sem_cast _ _ _ _ = Some _ |- _ => inversion CAST; subst end.
  match goal with ASSIGN : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    inversion ASSIGN; subst; try discriminate
  end.
  match goal with MODE : access_mode _ = By_value _ |- _ => inversion MODE; subst end.
  match goal with STORE : Mem.storev _ _ _ _ = Some _ |- _ =>
    cbn [Mem.storev] in STORE; rewrite Ptrofs.unsigned_repr in STORE by
      (apply matrix_small_offset_bound; lia);
    destruct (zle (4 * (i * 2 + j) + size_chunk Mint32) Ptrofs.modulus); try discriminate STORE
  end.
  eexists; repeat split; eauto.
Qed.

Print Assumptions matrix_store_inverse.
Print Assumptions matrix_store_evaluation.
