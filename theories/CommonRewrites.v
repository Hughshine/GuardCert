From Stdlib Require Import ZArith Bool Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import Presumption Synthesis ClightNoWrap ClightExprRewrite ClightExprRule.
Open Scope Z_scope.
Module P := Presumption.
Module G := Synthesis.

Definition uint_temp (id : ident) := Etempvar id type_int32u.
Definition uint_const (z : Z) := Econst_int (Int.repr z) type_int32u.
Definition snapshot_word (id : ident) (s : snapshot) := temp_word id (snd (fst s)).
Definition snapshot_view (id : ident) (s : snapshot) := word_view (snapshot_word id s).

(** Runtime divisor specialization: variable division/modulus becomes a shift
    or mask only when the divisor equals two. *)
Definition divisor_source (remainder : bool) (x y : ident) :=
  Ebinop (if remainder then Omod else Odiv) (uint_temp x) (uint_temp y) type_int32u.
Definition divisor_candidate (remainder : bool) (x : ident) :=
  Ebinop (if remainder then Oand else Oshr) (uint_temp x) (uint_const 1) type_int32u.
Definition divisor_guard (y : ident) :=
  Ebinop Oeq (uint_temp y) (uint_const 2) type_int32s.
Definition divisor_presumption := P.Atomic (P.Equal (P.Scalar 0) (P.Literal 2)).
Definition divisor_obligation (y : ident) (s : snapshot) :=
  Int.unsigned (snapshot_word y s) = 2.

Definition divisor_encoding (y : ident) :
  @G.presumption_encoding snapshot Int.modulus (snapshot_view y) (divisor_obligation y).
Proof.
  refine {| G.encoded_presumption := divisor_presumption |}.
  intro s. unfold P.holds, divisor_presumption, divisor_obligation, snapshot_view.
  change ((Int.unsigned (snapshot_word y s) =? 2) = true <->
    Int.unsigned (snapshot_word y s) = 2).
  apply Z.eqb_eq.
Defined.

Lemma divisor_synthesis_value : forall y,
  G.execute Int.modulus (word_view y) (G.synthesize divisor_presumption) =
  Some (Int.eq y (Int.repr 2)).
Proof.
  intro y. change
    ((if P.word_range Int.modulus (Int.unsigned y) && P.word_range Int.modulus 2
      then Some ((Int.unsigned y mod Int.modulus) =? (2 mod Int.modulus)) else None)
      = Some (Int.eq y (Int.repr 2))).
  assert (RANGE : P.word_range Int.modulus (Int.unsigned y) = true).
  { apply P.word_range_spec; apply Int.unsigned_range. }
  rewrite RANGE. change (P.word_range Int.modulus 2) with true. simpl andb.
  rewrite ! Z.mod_small by (try apply Int.unsigned_range; unfold Int.modulus; simpl; lia).
  f_equal. unfold Int.eq. change (Int.unsigned (Int.repr 2)) with 2.
  destruct (zeq (Int.unsigned y) 2).
  - apply Z.eqb_eq; auto.
  - apply Z.eqb_neq; auto.
Qed.

Lemma divisor_source_inv : forall rem ge e le m x y v,
  eval_expr ge e le m (divisor_source rem x y) v ->
  exists nx ny, le!x = Some (Vint nx) /\ le!y = Some (Vint ny) /\
    (if Int.eq ny Int.zero then None
     else Some (Vint (if rem then Int.modu nx ny else Int.divu nx ny))) = Some v.
Proof.
  intros rem ge e le m x y v EV. apply eval_binop_inv in EV.
  destruct EV as [vx [vy [EX [EY OP]]]].
  apply eval_temp_inv in EX. apply eval_temp_inv in EY.
  destruct rem; destruct vx; destruct vy; try discriminate OP;
    eexists; eexists; repeat split; eauto.
Qed.

Lemma divisor_guard_eval : forall ge e le m y ny,
  le!y = Some (Vint ny) ->
  eval_expr ge e le m (divisor_guard y) (Val.of_bool (Int.eq ny (Int.repr 2))).
Proof. intros. eapply eval_Ebinop; [apply eval_Etempvar; eauto|constructor|reflexivity]. Qed.

Lemma divisor_candidate_eval : forall rem ge e le m x nx,
  le!x = Some (Vint nx) ->
  eval_expr ge e le m (divisor_candidate rem x)
    (Vint (if rem then Int.modu nx (Int.repr 2) else Int.divu nx (Int.repr 2))).
Proof.
  intros. destruct rem; unfold divisor_candidate.
  - rewrite (Int.modu_and nx (Int.repr 2) Int.one ltac:(reflexivity)).
    change (Int.sub (Int.repr 2) Int.one) with Int.one.
    eapply eval_Ebinop; [apply eval_Etempvar; eauto|constructor|reflexivity].
  - rewrite (Int.divu_pow2 nx (Int.repr 2) Int.one ltac:(reflexivity)).
    eapply eval_Ebinop; [apply eval_Etempvar; eauto|constructor|reflexivity].
Qed.

Definition divisor_rule (rem : bool) (x y : ident) :
  encoded_expression_rule (divisor_source rem x y) (divisor_guard y) (divisor_candidate rem x).
Proof.
  refine {| expression_modulus := Int.modulus; expression_view := snapshot_view y;
    expression_obligation := divisor_obligation y; expression_encoding := divisor_encoding y |}.
  - destruct rem; reflexivity.
  - intros ge e le m v EV. apply divisor_source_inv in EV as [nx [ny [EX [EY VALUE]]]].
    exists (Val.of_bool (Int.eq ny (Int.repr 2))), (Int.eq ny (Int.repr 2)).
    split; [apply divisor_guard_eval; exact EY|]. split; [apply bool_of_bool|].
    unfold snapshot_view, snapshot_word, temp_word; simpl fst; simpl snd; rewrite EY.
    apply divisor_synthesis_value.
  - intros ge e le m v EV Q. apply divisor_source_inv in EV as [nx [ny [EX [EY VALUE]]]].
    unfold divisor_obligation, snapshot_word, temp_word in Q; simpl fst in Q; simpl snd in Q.
    rewrite EY in Q. assert (ny = Int.repr 2).
    { rewrite <- (Int.repr_unsigned ny). f_equal; exact Q. }
    subst ny. change (Int.eq (Int.repr 2) Int.zero) with false in VALUE.
    injection VALUE as VALUE; subst v. apply divisor_candidate_eval; exact EX.
Defined.

(** Arithmetic cancellation needs a no-overflow presumption even for unsigned
    C, whose source addition wraps rather than becoming undefined. *)
Definition cancel_source (x : ident) :=
  Ebinop Odiv (Ebinop Oadd (uint_temp x) (uint_temp x) type_int32u)
    (uint_const 2) type_int32u.
Definition cancel_guard (x : ident) :=
  Ebinop Ole (uint_temp x) (uint_const 2147483647) type_int32s.
Definition cancel_presumption := P.Atomic (P.NoOverflow (P.Sum (P.Scalar 0) (P.Scalar 0))).
Definition cancel_obligation (x : ident) (s : snapshot) :=
  Int.unsigned (snapshot_word x s) + Int.unsigned (snapshot_word x s) < Int.modulus.
Definition cancel_flag (x : Int.int) := negb (Int.ltu (Int.repr 2147483647) x).

Definition cancel_encoding (x : ident) :
  @G.presumption_encoding snapshot Int.modulus (snapshot_view x) (cancel_obligation x).
Proof.
  refine {| G.encoded_presumption := cancel_presumption |}.
  intro s. unfold P.holds, cancel_presumption, cancel_obligation, snapshot_view; simpl.
  repeat rewrite andb_true_iff. repeat rewrite P.word_range_spec.
  pose proof (Int.unsigned_range (snapshot_word x s)). lia.
Defined.

Lemma cancel_synthesis_value : forall x,
  G.execute Int.modulus (word_view x) (G.synthesize cancel_presumption) = Some (cancel_flag x).
Proof.
  intro x. change (Some (G.arithmetic_ok (G.evaluate Int.modulus (word_view x)
    (P.Sum (P.Scalar 0) (P.Scalar 0)))) = Some (cancel_flag x)).
  rewrite G.evaluate_flag_correct. simpl.
  assert (RANGE : P.word_range Int.modulus (Int.unsigned x) = true).
  { apply P.word_range_spec; apply Int.unsigned_range. }
  rewrite RANGE. simpl. f_equal.
  apply Bool.eq_true_iff_eq. rewrite P.word_range_spec.
  unfold cancel_flag, Int.ltu. change (Int.unsigned (Int.repr 2147483647)) with 2147483647.
  destruct (zlt 2147483647 (Int.unsigned x)); simpl;
    pose proof (Int.unsigned_range x); change Int.modulus with 4294967296; lia.
Qed.

Lemma cancel_source_inv : forall ge e le m id v,
  eval_expr ge e le m (cancel_source id) v ->
  exists x, le!id = Some (Vint x) /\ v = Vint (Int.divu (Int.add x x) (Int.repr 2)).
Proof.
  intros ge e le m id v EV. apply eval_binop_inv in EV.
  destruct EV as [vs [vt [ADD [TWO DIV]]]]. apply eval_const_inv in TWO; subst vt.
  apply eval_binop_inv in ADD. destruct ADD as [vx [vy [EX [EY ADD]]]].
  apply eval_temp_inv in EX. apply eval_temp_inv in EY.
  assert (vy = vx) by congruence; subst vy.
  destruct vx; try discriminate ADD.
  change (Some (Vint (Int.add i i)) = Some vs) in ADD. injection ADD as ADD; subst vs.
  change (Some (Vint (Int.divu (Int.add i i) (Int.repr 2))) = Some v) in DIV.
  injection DIV as DIV; subst v; eauto.
Qed.

Lemma cancel_value_correct : forall x,
  Int.unsigned x + Int.unsigned x < Int.modulus ->
  Int.divu (Int.add x x) (Int.repr 2) = x.
Proof.
  intros x Q. unfold Int.divu, Int.add.
  rewrite Int.unsigned_repr.
  - change (Int.unsigned (Int.repr 2)) with 2.
    replace (Int.unsigned x + Int.unsigned x) with (Int.unsigned x * 2) by lia.
    rewrite Z.div_mul by lia. apply Int.repr_unsigned.
  - pose proof (Int.unsigned_range x). unfold Int.max_unsigned; lia.
Qed.

Definition cancel_rule (x : ident) :
  encoded_expression_rule (cancel_source x) (cancel_guard x) (uint_temp x).
Proof.
  refine {| expression_modulus := Int.modulus; expression_view := snapshot_view x;
    expression_obligation := cancel_obligation x; expression_encoding := cancel_encoding x |}.
  - reflexivity.
  - intros ge e le m v EV. apply cancel_source_inv in EV as [nx [EX VALUE]].
    exists (Val.of_bool (cancel_flag nx)), (cancel_flag nx).
    split.
    + eapply eval_Ebinop; [apply eval_Etempvar; eauto|constructor|reflexivity].
    + split; [apply bool_of_bool|].
      unfold snapshot_view, snapshot_word, temp_word; simpl fst; simpl snd; rewrite EX.
      apply cancel_synthesis_value.
  - intros ge e le m v EV Q. apply cancel_source_inv in EV as [nx [EX VALUE]].
    unfold cancel_obligation, snapshot_word, temp_word in Q; simpl fst in Q; simpl snd in Q.
    rewrite EX in Q. subst v. rewrite cancel_value_correct by exact Q.
    apply eval_Etempvar; exact EX.
Defined.

(** Recognizers below require exact unsigned 32-bit types and no attributes;
    signed integers, volatile reads and wider arithmetic are not matched. *)
Definition uint_type (ty : type) : bool :=
  match ty with
  | Tint I32 Unsigned {| attr_volatile := false; attr_alignas := None |} => true
  | _ => false
  end.
Lemma uint_type_correct : forall ty, uint_type ty = true -> ty = type_int32u.
Proof.
  intros ty H. unfold uint_type in H.
  repeat match type of H with
  | context [match ?x with _ => _ end] => destruct x; cbn beta iota zeta in H; try discriminate
  end; reflexivity.
Qed.

Definition select_divisor (a : expr) : option (expr * expr) :=
  match a with
  | Ebinop op (Etempvar x tx) (Etempvar y ty) tr =>
      if uint_type tx && uint_type ty && uint_type tr then
        match op with
        | Odiv => Some (divisor_guard y, divisor_candidate false x)
        | Omod => Some (divisor_guard y, divisor_candidate true x)
        | _ => None
        end
      else None
  | _ => None
  end.

Theorem select_divisor_sound : forall a g c,
  select_divisor a = Some (g, c) -> expression_contract a g c.
Proof.
  intros a g c SEL. unfold select_divisor in SEL.
  destruct a; try discriminate. destruct a1; try discriminate. destruct a2; try discriminate.
  destruct (uint_type t0 && uint_type t1 && uint_type t) eqn:TYPES; try discriminate.
  repeat rewrite andb_true_iff in TYPES. destruct TYPES as [[TX TY] TR].
  apply uint_type_correct in TX; apply uint_type_correct in TY; apply uint_type_correct in TR.
  subst. destruct b; try discriminate; inversion SEL; subst;
    apply encoded_expression_rule_sound;
    first [exact (divisor_rule false i i0) | exact (divisor_rule true i i0)].
Qed.

Definition select_cancel (a : expr) : option (expr * expr) :=
  match a with
  | Ebinop Odiv (Ebinop Oadd (Etempvar x tx) (Etempvar y ty) tsum)
      (Econst_int two tconst) tr =>
      if uint_type tx && uint_type ty && uint_type tsum && uint_type tconst && uint_type tr then
        if ident_eq x y then
          if Int.eq two (Int.repr 2) then Some (cancel_guard x, uint_temp x) else None
        else None
      else None
  | _ => None
  end.

Theorem select_cancel_sound : forall a g c,
  select_cancel a = Some (g, c) -> expression_contract a g c.
Proof.
  intros a g c SEL. unfold select_cancel in SEL.
  repeat match type of SEL with
  | context [if ?x then _ else _] => destruct x eqn:?; cbn beta iota zeta in SEL; try discriminate
  | context [match ?x with _ => _ end] => destruct x; cbn beta iota zeta in SEL; try discriminate
  end.
  repeat match goal with H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?] end.
  repeat match goal with H : uint_type _ = true |- _ => apply uint_type_correct in H; subst end.
  match goal with H : Int.eq _ _ = true |- _ => apply Int.same_if_eq in H; subst end.
  subst. inversion SEL; subst. apply encoded_expression_rule_sound; apply cancel_rule.
Qed.

(** An unconditional identity uses Truth and the very same certificate API. *)
Definition self_sub_source (x : ident) :=
  Ebinop Osub (uint_temp x) (uint_temp x) type_int32u.
Definition truth_view (_ : snapshot) := word_view Int.zero.
Definition truth_obligation (_ : snapshot) : Prop := True.
Definition truth_encoding :
  @G.presumption_encoding snapshot Int.modulus truth_view truth_obligation.
Proof.
  refine {| G.encoded_presumption := P.Truth |}.
  intro s. unfold P.holds, truth_obligation; simpl; tauto.
Defined.

Definition self_sub_rule (x : ident) : encoded_expression_rule
  (self_sub_source x) (Econst_int Int.one type_int32s) (uint_const 0).
Proof.
  refine {| expression_modulus := Int.modulus; expression_view := truth_view;
    expression_obligation := truth_obligation; expression_encoding := truth_encoding |}.
  - reflexivity.
  - intros. exists (Vint Int.one), true. split; [constructor|].
    split; reflexivity.
  - intros ge e le m v EV Q. apply eval_binop_inv in EV.
    destruct EV as [vx [vy [EX [EY OP]]]]. apply eval_temp_inv in EX; apply eval_temp_inv in EY.
    assert (vy = vx) by congruence; subst vy. destruct vx; try discriminate OP.
    change (Some (Vint (Int.sub i i)) = Some v) in OP.
    rewrite Int.sub_idem in OP. injection OP as OP; subst v; constructor.
Defined.

Definition select_self_sub (a : expr) : option (expr * expr) :=
  match a with
  | Ebinop Osub (Etempvar x tx) (Etempvar y ty) tr =>
      if uint_type tx && uint_type ty && uint_type tr then
        if ident_eq x y then Some (Econst_int Int.one type_int32s, uint_const 0) else None
      else None
  | _ => None
  end.
Theorem select_self_sub_sound : forall a g c,
  select_self_sub a = Some (g, c) -> expression_contract a g c.
Proof.
  intros a g c SEL. unfold select_self_sub in SEL.
  repeat match type of SEL with
  | context [if ?x then _ else _] => destruct x eqn:?; cbn beta iota zeta in SEL; try discriminate
  | context [match ?x with _ => _ end] => destruct x; cbn beta iota zeta in SEL; try discriminate
  end.
  repeat match goal with H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?] end.
  repeat match goal with H : uint_type _ = true |- _ => apply uint_type_correct in H; subst end.
  subst. inversion SEL; subst. apply encoded_expression_rule_sound; apply self_sub_rule.
Qed.

Definition select_common_root (a : expr) :=
  match select_cancel a with
  | Some result => Some result
  | None => match select_divisor a with Some result => Some result | None => select_self_sub a end
  end.
Definition select_common := select_deep select_common_root.

Theorem select_common_sound : forall a g c,
  select_common a = Some (g, c) -> expression_contract a g c.
Proof.
  apply select_deep_sound. intros a g c SEL. unfold select_common_root in SEL.
  destruct (select_cancel a) as [[gg cc]|] eqn:CANCEL.
  - inversion SEL; subst. eapply select_cancel_sound; eauto.
  - destruct (select_divisor a) as [[gg cc]|] eqn:DIVISOR.
    + inversion SEL; subst. eapply select_divisor_sound; eauto.
    + eapply select_self_sub_sound; eauto.
Qed.

Print Assumptions select_common_sound.
