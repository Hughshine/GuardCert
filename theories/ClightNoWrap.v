From Stdlib Require Import ZArith Bool Lia.
From Guard Require Import Presumption Synthesis CompCertArithmetic ClightGuard ClightGuardProof.
From Guard Require Import ClightEncodedRule.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Smallstep.
From compcert.cfrontend Require Import Ctypes Cop Clight.
Open Scope Z_scope.
Module P := Presumption.
Module G := Synthesis.

Definition type_int32u : type := Tint I32 Unsigned noattr.

Definition wrap_test (id : ident) : expr :=
  Ebinop Olt
    (Ebinop Oadd (Etempvar id type_int32u) (Econst_int Int.one type_int32u) type_int32u)
    (Etempvar id type_int32u) type_int32s.

Definition no_wrap_guard (id : ident) : expr :=
  Ebinop Ole (Etempvar id type_int32u)
    (Econst_int (Int.sub Int.mone Int.one) type_int32u) type_int32s.

Definition no_wrap_flag (x : Int.int) : bool :=
  negb (Int.ltu (Int.sub Int.mone Int.one) x).

Definition word_view (x : Int.int) : P.state :=
  P.State (fun _ => Int.unsigned x) (fun _ => P.Pointer 0 0) (fun _ => 0).
Definition no_wrap_presumption : P.presumption :=
  P.Atomic (P.NoOverflow (P.Sum (P.Scalar 0) (P.Literal 1))).
Definition no_wrap_obligation (x : Int.int) : Prop := Int.unsigned x + 1 < Int.modulus.

Lemma no_wrap_encoding :
  @G.presumption_encoding Int.int Int.modulus word_view no_wrap_obligation.
Proof.
  refine {| G.encoded_presumption := no_wrap_presumption |}.
  intro x. unfold P.holds, no_wrap_presumption, no_wrap_obligation; simpl.
  repeat rewrite andb_true_iff. repeat rewrite P.word_range_spec.
  pose proof (Int.unsigned_range x). pose proof Int.modulus_pos. lia.
Defined.

(** The machine expression implements the existing synthesized condition, not
    a second unrelated mathematical check.  Its validity bit is an explicit
    Boolean value; no implicit hardware flag is added to CompCert's state. *)
Theorem no_wrap_synthesis_value : forall x,
  G.execute Int.modulus (word_view x) (G.synthesize no_wrap_presumption) =
  Some (no_wrap_flag x).
Proof.
  intro x.
  change (Some (G.arithmetic_ok (G.evaluate Int.modulus (word_view x)
    (P.Sum (P.Scalar 0) (P.Literal 1)))) = Some (no_wrap_flag x)).
  rewrite G.evaluate_flag_correct. simpl.
  assert (HX : P.word_range Int.modulus (Int.unsigned x) = true).
  { apply P.word_range_spec; apply Int.unsigned_range. }
  assert (H1 : P.word_range Int.modulus 1 = true).
  { reflexivity. }
  rewrite HX, H1. simpl.
  unfold no_wrap_flag. rewrite machine_add_flag_correct, Int.unsigned_one. reflexivity.
Qed.

Theorem no_wrap_flag_encodes_obligation : forall x,
  no_wrap_flag x = true <-> no_wrap_obligation x.
Proof.
  intro x. unfold no_wrap_flag, no_wrap_obligation.
  rewrite machine_add_flag_correct, Int.unsigned_one, P.word_range_spec.
  pose proof (Int.unsigned_range x); lia.
Qed.

Lemma no_wrap_eliminates_test : forall x,
  no_wrap_flag x = true -> Int.ltu (Int.add x Int.one) x = false.
Proof.
  intros x H. apply no_wrap_flag_encodes_obligation in H.
  unfold no_wrap_obligation in H. unfold Int.ltu, Int.add.
  rewrite Int.unsigned_repr, Int.unsigned_one.
  - destruct (zlt (Int.unsigned x + 1) (Int.unsigned x)); [lia|reflexivity].
  - rewrite Int.unsigned_one. pose proof (Int.unsigned_range x).
    unfold Int.max_unsigned; lia.
Qed.

Lemma bool_of_bool : forall b m,
  bool_val (Val.of_bool b) type_int32s m = Some b.
Proof. intros []; reflexivity. Qed.

Lemma eval_temp_inv : forall ge e le m id ty v,
  eval_expr ge e le m (Etempvar id ty) v -> le!id = Some v.
Proof.
  intros ge e le m id ty v H; inversion H; subst; auto.
  match goal with H : eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ => inversion H end.
Qed.

Lemma eval_const_inv : forall ge e le m i ty v,
  eval_expr ge e le m (Econst_int i ty) v -> v = Vint i.
Proof.
  intros ge e le m i ty v H; inversion H; subst; auto.
  match goal with H : eval_lvalue _ _ _ _ (Econst_int _ _) _ _ _ |- _ => inversion H end.
Qed.

Lemma eval_binop_inv : forall ge e le m op l r ty v,
  eval_expr ge e le m (Ebinop op l r ty) v ->
  exists vl vr, eval_expr ge e le m l vl /\ eval_expr ge e le m r vr /\
    sem_binary_operation ge op vl (typeof l) vr (typeof r) m = Some v.
Proof.
  intros ge e le m op l r ty v H; inversion H; subst; eauto.
  match goal with H : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion H end.
Qed.

Lemma wrap_test_eval_inv : forall ge e le m id v,
  eval_expr ge e le m (wrap_test id) v ->
  exists x, le!id = Some (Vint x) /\ v = Val.of_bool (Int.ltu (Int.add x Int.one) x).
Proof.
  intros ge e le m id v H. apply eval_binop_inv in H.
  destruct H as [vs [vx [ADD [EX CMP]]]].
  apply eval_binop_inv in ADD.
  destruct ADD as [vx' [vone [EX' [ONE ADD]]]].
  apply eval_temp_inv in EX. apply eval_temp_inv in EX'.
  apply eval_const_inv in ONE. subst vone.
  assert (vx' = vx) by congruence. subst vx'.
  destruct vx; try (discriminate ADD).
  change (Some (Vint (Int.add i Int.one)) = Some vs) in ADD.
  inversion ADD; subst vs.
  change (Some (Val.of_bool (Int.ltu (Int.add i Int.one) i)) = Some v) in CMP.
  injection CMP as CMP. subst v. exists i; auto.
Qed.

Lemma no_wrap_guard_evaluates : forall ge e le m id x,
  le!id = Some (Vint x) ->
  eval_expr ge e le m (no_wrap_guard id) (Val.of_bool (no_wrap_flag x)).
Proof.
  intros. unfold no_wrap_guard.
  eapply eval_Ebinop; [apply eval_Etempvar; eauto|constructor|reflexivity].
Qed.

(** This is both the lowering theorem and the explicit connection back to the
    condition synthesis interface, for this one supported presumption shape. *)
Theorem no_wrap_lowering_correct : forall ge e le m id x,
  le!id = Some (Vint x) ->
  exists v b, eval_expr ge e le m (no_wrap_guard id) v /\
    bool_val v (typeof (no_wrap_guard id)) m = Some b /\
    G.execute Int.modulus (word_view x) (G.synthesize no_wrap_presumption) = Some b.
Proof.
  intros. exists (Val.of_bool (no_wrap_flag x)), (no_wrap_flag x).
  split; [apply no_wrap_guard_evaluates; auto|].
  split; [apply bool_of_bool|apply no_wrap_synthesis_value].
Qed.

Definition temp_word (id : ident) (le : temp_env) : Int.int :=
  match le!id with Some (Vint x) => x | _ => Int.zero end.
Definition temp_word_view (id : ident) (le : temp_env) : P.state := word_view (temp_word id le).
Definition temp_no_wrap_obligation (id : ident) (le : temp_env) : Prop :=
  no_wrap_obligation (temp_word id le).

Definition temp_no_wrap_encoding (id : ident) :
  @G.presumption_encoding temp_env Int.modulus (temp_word_view id) (temp_no_wrap_obligation id).
Proof.
  refine {| G.encoded_presumption := no_wrap_presumption |}.
  intro le; apply (G.encoding_correct no_wrap_encoding).
Defined.

Definition no_wrap_rule (id : ident) : encoded_branch_rule (wrap_test id) (no_wrap_guard id).
Proof.
  refine {| rule_modulus := Int.modulus; rule_view := temp_word_view id;
    rule_obligation := temp_no_wrap_obligation id;
    rule_encoding := temp_no_wrap_encoding id |}.
  - intros ge e le m v b EVAL BOOL.
    apply wrap_test_eval_inv in EVAL as [x [LOOKUP VALUE]].
    exists (Val.of_bool (no_wrap_flag x)), (no_wrap_flag x).
    split; [apply no_wrap_guard_evaluates; auto|].
    split; [apply bool_of_bool|].
    unfold temp_word_view, temp_word; rewrite LOOKUP.
    apply no_wrap_synthesis_value.
  - intros ge e le m v b EVAL BOOL Q.
    apply wrap_test_eval_inv in EVAL as [x [LOOKUP VALUE]]. subst v.
    rewrite bool_of_bool in BOOL; inversion BOOL; subst b.
    apply no_wrap_eliminates_test. apply no_wrap_flag_encodes_obligation.
    unfold temp_no_wrap_obligation, temp_word in Q; rewrite LOOKUP in Q; exact Q.
Defined.

Theorem no_wrap_guard_contract : forall id, guard_contract (wrap_test id) (no_wrap_guard id).
Proof. intro id; apply encoded_branch_rule_sound; exact (no_wrap_rule id). Qed.

(** The recognizer requires exact 32-bit unsigned operand types, a 32-bit
    signed comparison result, the same temporary, and the literal one. *)
Definition select_no_wrap (a : expr) : option expr :=
  match a with
  | Ebinop Olt
      (Ebinop Oadd
        (Etempvar id (Tint I32 Unsigned {| attr_volatile := false; attr_alignas := None |}))
        (Econst_int one (Tint I32 Unsigned {| attr_volatile := false; attr_alignas := None |}))
        (Tint I32 Unsigned {| attr_volatile := false; attr_alignas := None |}))
      (Etempvar id' (Tint I32 Unsigned {| attr_volatile := false; attr_alignas := None |}))
      (Tint I32 Signed {| attr_volatile := false; attr_alignas := None |}) =>
      if ident_eq id id' then
        if Int.eq one Int.one then Some (no_wrap_guard id) else None
      else None
  | _ => None
  end.

Theorem select_no_wrap_sound : forall a g,
  select_no_wrap a = Some g -> guard_contract a g.
Proof.
  intros a g H. unfold select_no_wrap in H.
  repeat match type of H with
  | context [if ?x then _ else _] =>
      destruct x eqn:?; cbn beta iota zeta in H; try discriminate
  | context [match ?x with _ => _ end] =>
      destruct x; cbn beta iota zeta in H; try discriminate
  end.
  subst.
  match goal with H : Int.eq _ _ = true |- _ => apply Int.same_if_eq in H; subst end.
  inversion H; subst. apply no_wrap_guard_contract.
Qed.

Definition no_wrap_program := ClightGuard.transform_program select_no_wrap.

Theorem no_wrap_program_correct : forall p,
  forward_simulation (semantics2 p) (semantics2 (no_wrap_program p)).
Proof. apply transform_program_correct2. apply select_no_wrap_sound. Qed.

Print Assumptions no_wrap_lowering_correct.
Print Assumptions no_wrap_program_correct.
