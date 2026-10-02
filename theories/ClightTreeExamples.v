From Stdlib Require Import ZArith Bool Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import AbstractGuard SemanticFacts ClightCondition ClightTreeRule
  ClightTreeRewrite ClightExprRule ClightNoWrap CommonRewrites.
Open Scope Z_scope.

Definition cancellation_property (x : ident) (_ : unit) (s : clight_entry) : Prop :=
  Int.unsigned (temp_word x (entry_temps s)) +
  Int.unsigned (temp_word x (entry_temps s)) < Int.modulus.

Lemma cancellation_accept_sound : forall x s,
  cancel_flag (temp_word x (entry_temps s)) = true -> cancellation_property x tt s.
Proof.
  intros x s ACCEPT. unfold cancel_flag, Int.ltu in ACCEPT.
  change (Int.unsigned (Int.repr 2147483647)) with 2147483647 in ACCEPT.
  destruct (zlt 2147483647 (Int.unsigned (temp_word x (entry_temps s))));
    try discriminate. unfold cancellation_property.
  change Int.modulus with 4294967296; lia.
Qed.

(** A one-sided arithmetic dimension. Refusal cannot establish overflow.
    The state layout and machine arithmetic are known only to this instance. *)
Definition cancellation_dimension (x : ident) :=
  @positive_dimension clight_entry unit (source_defined (cancel_source x))
    (cancellation_property x)
    (fun _ s => cancel_flag (temp_word x (entry_temps s)))
    (fun _ s _ ACCEPT => cancellation_accept_sound x s ACCEPT).

Lemma true_test : forall s b,
  expression_test (Econst_int Int.one type_int32s) s b <-> b = true.
Proof.
  intros s b; split.
  - intros [v [EV BOOL]]. apply eval_const_inv in EV; subst v.
    change (Some true = Some b) in BOOL. congruence.
  - intro EQ; subst b. exists (Vint Int.one); split; [constructor|reflexivity].
Qed.

Lemma cancellation_test : forall x s b,
  source_defined (cancel_source x) s ->
  (expression_test (cancel_guard x) s b <->
   b = cancel_flag (temp_word x (entry_temps s))).
Proof.
  intros x [ge e le m] b [v SOURCE]; cbn in *.
  apply cancel_source_inv in SOURCE as [nx [LOOKUP VALUE]].
  unfold temp_word; rewrite LOOKUP.
  split.
  - intros [vg [GUARD BOOL]]. apply eval_binop_inv in GUARD.
    destruct GUARD as [vl [vr [LEFT [RIGHT OP]]]].
    apply eval_temp_inv in LEFT. apply eval_const_inv in RIGHT; subst vr.
    cbn in LEFT.
    assert (vl = Vint nx) by congruence; subst vl.
    change (Some (Val.of_bool (cancel_flag nx)) = Some vg) in OP.
    injection OP as OP; subst vg. rewrite bool_of_bool in BOOL; congruence.
  - intro EQ; subst b. exists (Val.of_bool (cancel_flag nx)); split.
    + eapply eval_Ebinop; [apply eval_Etempvar; exact LOOKUP|constructor|reflexivity].
    + apply bool_of_bool.
Qed.

Definition cancellation_primitives (x : ident) :
  check_primitives decision_language (source_defined (cancel_source x))
    (decide_atom (cancellation_dimension x)).
Proof.
  refine (@CheckPrimitives clight_entry unit decision_language
    (source_defined (cancel_source x)) (decide_atom (cancellation_dimension x))
    (fun _ => cancel_guard x) (fun _ => Econst_int Int.one type_int32s) _ _).
  - intros [] s b INV. cbn [decision_language].
    rewrite cancellation_test by exact INV.
    unfold cancellation_dimension; cbn [positive_dimension decide_atom].
    destruct (cancel_flag (temp_word x (entry_temps s))); reflexivity.
  - intros [] s b v INV EX. cbn [decision_language].
    rewrite true_test. unfold cancellation_dimension in EX.
    cbn [positive_dimension decide_atom] in EX.
    destruct (cancel_flag (temp_word x (entry_temps s))); try discriminate.
    injection EX as EX; subst v; reflexivity.
Defined.

Definition cancellation_tree_rule (x : ident) : encoded_tree_rule (cancel_source x) (uint_temp x).
Proof.
  refine {| rule_atoms := unit; rule_domain := source_defined (cancel_source x);
    rule_dimension := cancellation_dimension x; rule_primitives := cancellation_primitives x;
    rule_formula := Fact tt |}.
  - reflexivity.
  - intros s H; exact H.
  - intros [ge e le m] v EV Q; cbn in *.
    apply cancel_source_inv in EV as [nx [LOOKUP VALUE]].
    change (cancellation_property x tt (Entry ge e le m)) in Q.
    unfold cancellation_property, temp_word in Q; cbn in Q; rewrite LOOKUP in Q.
    subst v. rewrite cancel_value_correct by exact Q.
    apply eval_Etempvar; exact LOOKUP.
Defined.

Definition cancellation_tree (x : ident) := generated_tree (cancellation_tree_rule x).

Example cancellation_tree_code : forall x,
  cancellation_tree x = Test (cancel_guard x)
    (Test (Econst_int Int.one type_int32s) (Decision true) (Decision false))
    (Decision false).
Proof. reflexivity. Qed.

Definition select_tree_cancel (a : expr) : option (decision_tree * expr) :=
  match a with
  | Ebinop Odiv (Ebinop Oadd (Etempvar x tx) (Etempvar y ty) tsum)
      (Econst_int two tconst) tr =>
      if uint_type tx && uint_type ty && uint_type tsum && uint_type tconst && uint_type tr then
        if ident_eq x y then
          if Int.eq two (Int.repr 2) then Some (cancellation_tree x, uint_temp x) else None
        else None
      else None
  | _ => None
  end.

Theorem select_tree_cancel_sound : forall a g c,
  select_tree_cancel a = Some (g, c) -> ClightTreeRewrite.expression_contract a g c.
Proof.
  intros a g c SEL. unfold select_tree_cancel in SEL.
  repeat match type of SEL with
  | context [if ?x then _ else _] => destruct x eqn:?; cbn beta iota zeta in SEL; try discriminate
  | context [match ?x with _ => _ end] => destruct x; cbn beta iota zeta in SEL; try discriminate
  end.
  repeat match goal with H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?] end.
  repeat match goal with H : uint_type _ = true |- _ => apply uint_type_correct in H; subst end.
  match goal with H : Int.eq _ _ = true |- _ => apply Int.same_if_eq in H; subst end.
  subst. inversion SEL; subst. apply encoded_tree_rule_sound.
Qed.

Definition select_tree_common_root (a : expr) : option (decision_tree * expr) :=
  match select_tree_cancel a with
  | Some result => Some result
  | None => match select_common_root a with
            | Some (g, c) => Some (Test g (Decision true) (Decision false), c)
            | None => None end
  end.
Definition select_tree_common := select_tree_deep select_tree_common_root.

Theorem select_tree_common_root_sound : forall a g c,
  select_tree_common_root a = Some (g, c) -> ClightTreeRewrite.expression_contract a g c.
Proof.
  intros a g c SEL. unfold select_tree_common_root in SEL.
  destruct (select_tree_cancel a) as [[t cc]|] eqn:TREE.
  - inversion SEL; subst. eapply select_tree_cancel_sound; eauto.
  - destruct (select_common_root a) as [[gg cc]|] eqn:OLD; try discriminate.
    inversion SEL; subst. apply legacy_rule.
    unfold select_common_root in OLD.
    destruct (select_cancel a) as [[g1 c1]|] eqn:CANCEL.
    + inversion OLD; subst; eapply select_cancel_sound; eauto.
    + destruct (select_divisor a) as [[g1 c1]|] eqn:DIVISOR.
      * inversion OLD; subst; eapply select_divisor_sound; eauto.
      * eapply select_self_sub_sound; eauto.
Qed.

Theorem select_tree_common_sound : forall a g c,
  select_tree_common a = Some (g, c) -> ClightTreeRewrite.expression_contract a g c.
Proof. apply select_tree_deep_sound; exact select_tree_common_root_sound. Qed.

Print Assumptions cancellation_tree_rule.
Print Assumptions select_tree_common_sound.
