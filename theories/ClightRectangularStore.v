From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.x86_64 Require Import Archi.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightPureExpr CompCertStoreSchedule RectangularSchedule.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Record rectangle_shape := RectangleShape {
  rectangle_extent : Z;
  rectangle_stride : Z;
  rectangle_coefficient : Z;
  rectangle_bias : Z
}.
Definition rectangle_layout_valid d :=
  0 < rectangle_extent d /\ rectangle_extent d <= Int.max_signed /\
  0 < rectangle_stride d /\ rectangle_stride d <= rectangle_extent d /\
  4 * rectangle_extent d <= Ptrofs.max_unsigned.
Definition rectangle_layout_check d :=
  (0 <? rectangle_extent d) && (rectangle_extent d <=? Int.max_signed) &&
  (0 <? rectangle_stride d) && (rectangle_stride d <=? rectangle_extent d) &&
  (4 * rectangle_extent d <=? Ptrofs.max_unsigned).
Lemma rectangle_layout_check_sound d : rectangle_layout_check d = true -> rectangle_layout_valid d.
Proof. unfold rectangle_layout_check, rectangle_layout_valid; rewrite !andb_true_iff, !Z.ltb_lt, !Z.leb_le; tauto. Qed.

Section SHAPE.
Variable d : rectangle_shape.
Hypothesis VALID : rectangle_layout_valid d.

Lemma rect_small_offset_bound value : 0 <= value <= 4 * rectangle_extent d ->
  0 <= value <= Ptrofs.max_unsigned.
Proof. unfold rectangle_layout_valid in VALID; lia. Qed.
Lemma rect_index_signed index : 0 <= index < rectangle_extent d ->
  Int.min_signed <= index <= Int.max_signed.
Proof. unfold rectangle_layout_valid in VALID; change Int.min_signed with (-2147483648); lia. Qed.

(** A native Clight instance for the first affine scheduling example. Every
    memory operation below is an actual CompCert operation. *)
Definition rect_array_type := Tarray type_int32s (rectangle_extent d) noattr.
Definition rect_constant z := if z <? 0 then
  Eunop Oneg (Econst_int (Int.repr (-z)) type_int32s) type_int32s
  else Econst_int (Int.repr z) type_int32s.
Lemma rect_constant_type z : typeof (rect_constant z) = type_int32s.
Proof. unfold rect_constant; destruct (z <? 0); reflexivity. Qed.
Lemma rect_constant_evaluation ge locals le memory z :
  eval_expr ge locals le memory (rect_constant z) (Vint (Int.repr z)).
Proof.
  unfold rect_constant; destruct (z <? 0); [|constructor].
  eapply eval_Eunop; [constructor|].
  change (Some (Vint (Int.neg (Int.repr (-z)))) = Some (Vint (Int.repr z))).
  rewrite Int.neg_repr, Z.opp_involutive; reflexivity.
Qed.
Definition rect_index iterator inner :=
  Ebinop Oadd (Ebinop Omul (Etempvar iterator type_int32s) (rect_constant (rectangle_stride d)) type_int32s)
    (Etempvar inner type_int32s) type_int32s.
Definition rect_value iterator inner :=
  Ebinop Oadd
    (Ebinop Oadd (Ebinop Omul (Etempvar iterator type_int32s) (rect_constant (rectangle_coefficient d)) type_int32s)
      (Etempvar inner type_int32s) type_int32s) (rect_constant (rectangle_bias d)) type_int32s.
Definition rect_lvalue array iterator inner :=
  Ederef (Ebinop Oadd (Evar array rect_array_type) (rect_index iterator inner)
    (Tpointer type_int32s noattr)) type_int32s.
Definition rect_store array iterator inner :=
  Sassign (rect_lvalue array iterator inner) (rect_value iterator inner).
Definition rect_array_binding (ge : genv) locals array block :=
  locals ! array = Some (block, rect_array_type) \/
  (locals ! array = None /\ Genv.find_symbol ge array = Some block).

Lemma rect_array_binding_unique ge locals array first second :
  rect_array_binding ge locals array first -> rect_array_binding ge locals array second -> first = second.
Proof. intros [FIRST|[ABSENT FIRST]] [SECOND|[ABSENT' SECOND]]; congruence. Qed.

Lemma rect_index_pure iterator inner : pure_scalar (rect_index iterator inner).
Proof. unfold rect_index, rect_constant; destruct (rectangle_stride d <? 0); repeat constructor. Qed.
Lemma rect_value_pure iterator inner : pure_scalar (rect_value iterator inner).
Proof.
  unfold rect_value, rect_constant; destruct (rectangle_coefficient d <? 0), (rectangle_bias d <? 0); repeat constructor.
Qed.

Lemma rect_integer_multiply x y :
  Int.mul (Int.repr x) (Int.repr y) = Int.repr (x * y).
Proof. unfold Int.mul; apply Int.eqm_samerepr; apply Int.eqm_mult; apply Int.eqm_sym; apply Int.eqm_unsigned_repr. Qed.
Lemma rect_integer_add x y : Int.add (Int.repr x) (Int.repr y) = Int.repr (x + y).
Proof. unfold Int.add; apply Int.eqm_samerepr; apply Int.eqm_add; apply Int.eqm_sym; apply Int.eqm_unsigned_repr. Qed.

Lemma rect_index_evaluation ge locals le memory iterator inner i j :
  le ! iterator = Some (Vint (Int.repr i)) -> le ! inner = Some (Vint (Int.repr j)) ->
  eval_expr ge locals le memory (rect_index iterator inner) (Vint (Int.repr (i * rectangle_stride d + j))).
Proof.
  intros I J; unfold rect_index.
  eapply eval_Ebinop with (v1 := Vint (Int.repr (i * rectangle_stride d))) (v2 := Vint (Int.repr j)).
  - eapply eval_Ebinop with (v1 := Vint (Int.repr i)) (v2 := Vint (Int.repr (rectangle_stride d)));
      [constructor; exact I|apply rect_constant_evaluation|].
    rewrite rect_constant_type.
    change (Some (Vint (Int.mul (Int.repr i) (Int.repr (rectangle_stride d)))) = Some (Vint (Int.repr (i * rectangle_stride d)))).
    rewrite rect_integer_multiply; reflexivity.
  - constructor; exact J.
  - change (Some (Vint (Int.add (Int.repr (i * rectangle_stride d)) (Int.repr j))) =
      Some (Vint (Int.repr (i * rectangle_stride d + j)))). rewrite rect_integer_add; reflexivity.
Qed.
Lemma rect_value_evaluation ge locals le memory iterator inner i j :
  le ! iterator = Some (Vint (Int.repr i)) -> le ! inner = Some (Vint (Int.repr j)) ->
  eval_expr ge locals le memory (rect_value iterator inner) (Vint (Int.repr (i * rectangle_coefficient d + j + rectangle_bias d))).
Proof.
  intros I J; unfold rect_value.
  eapply eval_Ebinop with (v1 := Vint (Int.repr (i * rectangle_coefficient d + j))) (v2 := Vint (Int.repr (rectangle_bias d))).
  - eapply eval_Ebinop with (v1 := Vint (Int.repr (i * rectangle_coefficient d))) (v2 := Vint (Int.repr j)).
    + eapply eval_Ebinop with (v1 := Vint (Int.repr i)) (v2 := Vint (Int.repr (rectangle_coefficient d)));
        [constructor; exact I|apply rect_constant_evaluation|].
      rewrite rect_constant_type.
      change (Some (Vint (Int.mul (Int.repr i) (Int.repr (rectangle_coefficient d)))) = Some (Vint (Int.repr (i * rectangle_coefficient d)))).
      rewrite rect_integer_multiply; reflexivity.
    + constructor; exact J.
    + change (Some (Vint (Int.add (Int.repr (i * rectangle_coefficient d)) (Int.repr j))) =
        Some (Vint (Int.repr (i * rectangle_coefficient d + j)))). rewrite rect_integer_add; reflexivity.
  - apply rect_constant_evaluation.
  - rewrite rect_constant_type.
    change (Some (Vint (Int.add (Int.repr (i * rectangle_coefficient d + j)) (Int.repr (rectangle_bias d)))) =
      Some (Vint (Int.repr (i * rectangle_coefficient d + j + rectangle_bias d)))). rewrite rect_integer_add; reflexivity.
Qed.

Lemma rect_pointer_add ge memory block index : 0 <= index < rectangle_extent d ->
  sem_binary_operation ge Oadd (Vptr block Ptrofs.zero) rect_array_type
    (Vint (Int.repr index)) type_int32s memory = Some (Vptr block (Ptrofs.repr (4 * index))).
Proof.
  intro RANGE.
  change (Some (Vptr block (Ptrofs.add Ptrofs.zero
    (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.repr (Int.signed (Int.repr index)))))) =
    Some (Vptr block (Ptrofs.repr (4 * index)))).
  rewrite Int.signed_repr by (apply rect_index_signed; exact RANGE).
  rewrite Ptrofs.add_zero_l; unfold Ptrofs.mul.
  rewrite (Ptrofs.unsigned_repr 4) by (apply rect_small_offset_bound; unfold rectangle_layout_valid in VALID; lia).
  rewrite (Ptrofs.unsigned_repr index) by (apply rect_small_offset_bound; unfold rectangle_layout_valid in VALID; lia).
  reflexivity.
Qed.

Lemma rect_reference_evaluation ge locals le memory array block :
  rect_array_binding ge locals array block ->
  eval_expr ge locals le memory (Evar array rect_array_type) (Vptr block Ptrofs.zero).
Proof.
  intros [LOCAL|[ABSENT GLOBAL]].
  - eapply eval_Elvalue; [apply eval_Evar_local; exact LOCAL|apply deref_loc_reference; reflexivity].
  - eapply eval_Elvalue with (loc := block) (ofs := Ptrofs.zero) (bf := Full).
    + apply eval_Evar_global; assumption.
    + apply deref_loc_reference; reflexivity.
Qed.

Lemma rect_reference_inverse ge locals le memory array value :
  eval_expr ge locals le memory (Evar array rect_array_type) value ->
  exists block, rect_array_binding ge locals array block /\ value = Vptr block Ptrofs.zero.
Proof.
  intro EVAL; inversion EVAL; subst.
  match goal with DEREF : deref_loc _ _ _ _ _ _ |- _ => inversion DEREF; subst; try discriminate end.
  all: match goal with LVALUE : eval_lvalue _ _ _ _ (Evar _ _) _ _ _ |- _ => inversion LVALUE; subst end.
  - eexists; split; [left; eassumption|reflexivity].
  - eexists; split; [right; split; eassumption|reflexivity].
Qed.

Lemma rect_lvalue_evaluation ge locals le memory array iterator inner block i j :
  rect_array_binding ge locals array block ->
  le ! iterator = Some (Vint (Int.repr i)) -> le ! inner = Some (Vint (Int.repr j)) ->
  0 <= i * rectangle_stride d + j < rectangle_extent d ->
  eval_lvalue ge locals le memory (rect_lvalue array iterator inner)
    block (Ptrofs.repr (4 * (i * rectangle_stride d + j))) Full.
Proof.
  intros ARRAY I J INDEX; apply eval_Ederef.
  eapply eval_Ebinop with (v1 := Vptr block Ptrofs.zero) (v2 := Vint (Int.repr (i * rectangle_stride d + j)));
    [apply rect_reference_evaluation; exact ARRAY|
    apply rect_index_evaluation; assumption|apply rect_pointer_add; lia].
Qed.

Lemma rect_lvalue_inverse ge locals le memory array iterator inner i j block offset bitfield :
  le ! iterator = Some (Vint (Int.repr i)) -> le ! inner = Some (Vint (Int.repr j)) ->
  0 <= i * rectangle_stride d + j < rectangle_extent d ->
  eval_lvalue ge locals le memory (rect_lvalue array iterator inner) block offset bitfield ->
  rect_array_binding ge locals array block /\ offset = Ptrofs.repr (4 * (i * rectangle_stride d + j)) /\ bitfield = Full.
Proof.
  intros I J INDEX RUN; inversion RUN; subst.
  match goal with POINTER : eval_expr _ _ _ _ (Ebinop Oadd _ _ _) _ |- _ => inversion POINTER; subst end;
    try match goal with BAD : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion BAD end.
  match goal with ARRAY : eval_expr _ _ _ _ (Evar _ _) ?v,
    INDEX : eval_expr _ _ _ _ (rect_index _ _) ?idx |- _ =>
    destruct (@rect_reference_inverse ge locals le memory array v ARRAY) as [actual_block [BINDING SAME]]; subst v;
    pose proof (@pure_scalar_determinate _ (rect_index_pure iterator inner) ge locals le memory
      idx (Vint (Int.repr (i * rectangle_stride d + j))) INDEX
      (@rect_index_evaluation ge locals le memory iterator inner i j I J)) as INDEX_VALUE; subst idx
  end.
  match goal with SEM : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
    cbn [typeof rect_index] in SEM;
    rewrite (@rect_pointer_add ge memory actual_block (i * rectangle_stride d + j) ltac:(lia)) in SEM;
    inversion SEM; subst
  end; auto.
Qed.

Lemma rect_store_evaluation fe ge locals le memory array iterator inner block i j memory' :
  rect_array_binding ge locals array block ->
  le ! iterator = Some (Vint (Int.repr i)) -> le ! inner = Some (Vint (Int.repr j)) ->
  0 <= i * rectangle_stride d + j < rectangle_extent d ->
  Mem.store Mint32 memory block (4 * (i * rectangle_stride d + j)) (Vint (Int.repr (i * rectangle_coefficient d + j + rectangle_bias d))) = Some memory' ->
  exec_stmt fe ge locals le memory (rect_store array iterator inner) E0 le memory' Out_normal.
Proof.
  intros ARRAY I J INDEX STORE; eapply exec_Sassign with
    (loc := block) (ofs := Ptrofs.repr (4 * (i * rectangle_stride d + j))) (bf := Full)
    (v := Vint (Int.repr (i * rectangle_coefficient d + j + rectangle_bias d))) (v2 := Vint (Int.repr (i * rectangle_coefficient d + j + rectangle_bias d))).
  - apply rect_lvalue_evaluation; eauto.
  - apply rect_value_evaluation; assumption.
  - reflexivity.
  - apply assign_loc_value with (chunk := Mint32); [reflexivity|].
    cbn [Mem.storev]. rewrite Ptrofs.unsigned_repr by (apply rect_small_offset_bound; unfold rectangle_layout_valid in VALID; lia).
    destruct (zle (4 * (i * rectangle_stride d + j) + size_chunk Mint32) Ptrofs.modulus); [exact STORE|].
    exfalso; pose proof (@rect_small_offset_bound (4 * (i * rectangle_stride d + j) + 4) ltac:(lia)) as END.
    unfold Ptrofs.max_unsigned in END; change (size_chunk Mint32) with 4 in *; lia.
Qed.

Lemma rect_store_inverse fe ge locals le memory array iterator inner i j trace le' memory' outcome :
  le ! iterator = Some (Vint (Int.repr i)) -> le ! inner = Some (Vint (Int.repr j)) ->
  0 <= i * rectangle_stride d + j < rectangle_extent d ->
  exec_stmt fe ge locals le memory (rect_store array iterator inner) trace le' memory' outcome ->
  exists block, rect_array_binding ge locals array block /\ trace = E0 /\ le' = le /\ outcome = Out_normal /\
    Mem.store Mint32 memory block (4 * (i * rectangle_stride d + j)) (Vint (Int.repr (i * rectangle_coefficient d + j + rectangle_bias d))) = Some memory'.
Proof.
  intros I J INDEX RUN; inversion RUN; subst.
  match goal with LVALUE : eval_lvalue _ _ ?current _ (rect_lvalue _ _ _) _ _ _ |- _ =>
    destruct (@rect_lvalue_inverse ge locals current memory array iterator inner i j _ _ _
      I J INDEX LVALUE) as [ARRAY [OFFSET FIELD]]; subst
  end.
  match goal with VALUE : eval_expr _ _ ?current _ (rect_value _ _) ?value |- _ =>
    pose proof (@pure_scalar_determinate _ (rect_value_pure iterator inner) ge locals current memory
      value (Vint (Int.repr (i * rectangle_coefficient d + j + rectangle_bias d))) VALUE
      (@rect_value_evaluation ge locals current memory iterator inner i j I J)) as SAME; subst value
  end.
  match goal with CAST : sem_cast _ _ _ _ = Some _ |- _ => inversion CAST; subst end.
  match goal with ASSIGN : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    inversion ASSIGN; subst; try discriminate
  end.
  match goal with MODE : access_mode _ = By_value _ |- _ => inversion MODE; subst end.
  match goal with STORE : Mem.storev _ _ _ _ = Some _ |- _ =>
    cbn [Mem.storev] in STORE; rewrite Ptrofs.unsigned_repr in STORE by
      (apply rect_small_offset_bound; lia);
    destruct (zle (4 * (i * rectangle_stride d + j) + size_chunk Mint32) Ptrofs.modulus); try discriminate STORE
  end.
  eexists; repeat split; eauto.
Qed.

End SHAPE.

Print Assumptions rect_store_inverse.
Print Assumptions rect_store_evaluation.
