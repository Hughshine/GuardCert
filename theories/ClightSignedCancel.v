From Stdlib Require Import Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import AbstractGuard SemanticFacts ClightCondition ClightPureExpr
  ClightWideGuard ClightDecisionRule ClightTreeRule ClightTreeRewrite ClightNoWrap
  ClightSameAddress.
Set Implicit Arguments.
Open Scope Z_scope.

Definition signed_temp x := Etempvar x type_int32s.
Definition signed_two := Econst_int (Int.repr 2) type_int32s.
Definition signed_cancel_source x :=
  Ebinop Odiv (Ebinop Omul (signed_temp x) signed_two type_int32s) signed_two type_int32s.

Lemma signed_cancel_source_inv ge locals le m x v :
  eval_expr ge locals le m (signed_cancel_source x) v ->
  exists nx, le ! x = Some (Vint nx) /\
    v = Vint (Int.divs (Int.mul nx (Int.repr 2)) (Int.repr 2)).
Proof.
  intro SOURCE; apply scalar_binary_inv in SOURCE.
  destruct SOURCE as [product [two [MUL [TWO DIV]]]].
  apply scalar_const_inv in TWO; subst two.
  apply scalar_binary_inv in MUL.
  destruct MUL as [operand [two [TEMP [TWO MUL]]]].
  apply scalar_const_inv in TWO; subst two. apply scalar_temp_inv in TEMP.
  destruct operand; try discriminate MUL.
  change (Some (Vint (Int.mul i (Int.repr 2))) = Some product) in MUL.
  inversion MUL; subst product.
  change ((if Int.eq (Int.mul i (Int.repr 2)) (Int.repr Int.min_signed) && false
    then None else Some (Vint (Int.divs (Int.mul i (Int.repr 2)) (Int.repr 2)))) = Some v) in DIV.
  rewrite andb_false_r in DIV.
  inversion DIV; subst v; eauto.
Qed.

Lemma signed_cancel_value nx : word_range (Int.signed nx * 2) ->
  Int.divs (Int.mul nx (Int.repr 2)) (Int.repr 2) = nx.
Proof.
  intro RANGE. unfold Int.divs. rewrite Int.mul_signed.
  change (Int.signed (Int.repr 2)) with 2.
  rewrite Int.signed_repr by exact RANGE.
  rewrite Z.quot_mul by lia. apply Int.repr_signed.
Qed.

Definition signed_cancel_domain x (s : clight_entry) :=
  exists nx, (entry_temps s) ! x = Some (Vint nx).

Definition signed_cancel_decide x (_ : unit) (s : clight_entry) : option bool :=
  match (entry_temps s) ! x with
  | Some (Vint nx) => Some (word_range_bool (Int.signed nx * 2))
  | _ => None end.

Definition signed_cancel_property x (_ : unit) (s : clight_entry) :=
  exists nx, (entry_temps s) ! x = Some (Vint nx) /\ word_range (Int.signed nx * 2).

Definition signed_cancel_dimension x :
  property_dimension clight_entry unit (signed_cancel_domain x).
Proof.
  refine {| atom_property := signed_cancel_property x; decide_atom := signed_cancel_decide x |}.
  intros [] s result [nx LOOKUP] CHECK.
  unfold signed_cancel_decide in CHECK; rewrite LOOKUP in CHECK.
  inversion CHECK; subst result. destruct (word_range_bool (Int.signed nx * 2)) eqn:RANGE;
    cbn [decision_evidence].
  - exists nx; split; auto. apply word_range_bool_spec; exact RANGE.
  - intros [nx' [LOOKUP' SAFE]]. assert (nx' = nx) by congruence; subst nx'.
    apply word_range_bool_spec in SAFE; congruence.
Defined.

Definition signed_cancel_check x := wide_bounds_tree (wide_mul (signed_temp x) signed_two).

Lemma signed_cancel_check_pure x : pure_tree (signed_cancel_check x).
Proof. apply wide_bounds_pure; repeat constructor. Qed.

Lemma signed_cancel_check_run x s nx : (entry_temps s) ! x = Some (Vint nx) ->
  decision_run s (signed_cancel_check x) (word_range_bool (Int.signed nx * 2)).
Proof.
  intros LOOKUP; destruct s as [ge locals le m]; cbn in *.
  eapply wide_bounds_run.
  - reflexivity.
  - apply word_product_is_long; [apply Int.signed_range |].
    change (-2147483648 <= 2 <= 2147483647); lia.
  - eapply wide_mul_eval; try reflexivity.
    + apply Int.signed_range.
    + change (-2147483648 <= 2 <= 2147483647); lia.
    + rewrite Int.repr_signed; constructor; exact LOOKUP.
    + constructor.
Qed.

Definition signed_cancel_primitives x :
  check_primitives decision_test_language (signed_cancel_domain x)
    (decide_atom (signed_cancel_dimension x)).
Proof.
  refine (@CheckPrimitives clight_entry unit decision_test_language (signed_cancel_domain x)
    (decide_atom (signed_cancel_dimension x)) (fun _ => Decision true)
    (fun _ => signed_cancel_check x) _ _).
  - intros [] s result [nx LOOKUP]. cbn [decision_test_language].
    unfold signed_cancel_dimension; cbn [decide_atom]; unfold signed_cancel_decide.
    rewrite LOOKUP; cbn [checked_valid]. split; intro RUN;
      [inversion RUN; reflexivity | subst; constructor].
  - intros [] s result expected [nx LOOKUP] CHECK. cbn [decision_test_language].
    change (signed_cancel_decide x tt s = Some expected) in CHECK.
    unfold signed_cancel_decide in CHECK; rewrite LOOKUP in CHECK; inversion CHECK; subst expected.
    split.
    + intro RUN. eapply pure_tree_determinate;
        [apply signed_cancel_check_pure | exact RUN | apply signed_cancel_check_run; exact LOOKUP].
    + intro EQ; subst result; apply signed_cancel_check_run; exact LOOKUP.
Defined.

Definition signed_cancel_rule x : encoded_decision_rule (signed_cancel_source x) (signed_temp x).
Proof.
  refine {| decision_rule_atoms := unit; decision_rule_domain := signed_cancel_domain x;
    decision_rule_dimension := signed_cancel_dimension x;
    decision_rule_primitives := signed_cancel_primitives x;
    decision_rule_formula := Fact tt |}.
  - reflexivity.
  - intros [ge locals le m] [v SOURCE]; cbn in *.
    apply signed_cancel_source_inv in SOURCE as [nx [LOOKUP VALUE]].
    unfold signed_cancel_domain; cbn. exists nx; exact LOOKUP.
  - intros [ge locals le m] v SOURCE PROPERTY; cbn in *.
    apply signed_cancel_source_inv in SOURCE as [nx [LOOKUP VALUE]].
    change (signed_cancel_property x tt (Entry ge locals le m)) in PROPERTY.
    destruct PROPERTY as [nx' [LOOKUP' RANGE]]; cbn in LOOKUP'.
    assert (nx' = nx) by congruence; subst nx'.
    subst v. rewrite signed_cancel_value by exact RANGE; constructor; exact LOOKUP.
Defined.

Definition signed_cancel_tree x := generated_decision_tree (signed_cancel_rule x).

Example signed_cancel_tree_code x : signed_cancel_tree x = signed_cancel_check x.
Proof. reflexivity. Qed.

Definition signed_type ty :=
  match ty with Tint I32 Signed {| attr_volatile := false; attr_alignas := None |} => true
  | _ => false end.

Lemma signed_type_correct ty : signed_type ty = true -> ty = type_int32s.
Proof.
  unfold signed_type. repeat match goal with
  | |- context [match ?x with _ => _ end] => destruct x; cbn beta iota zeta; try discriminate
  end; reflexivity.
Qed.

Definition select_signed_cancel a : option (decision_tree * expr) :=
  match a with
  | Ebinop Odiv (Ebinop Omul (Etempvar x tx) (Econst_int k tk) tm)
      (Econst_int d td) tr =>
    if signed_type tx && signed_type tk && signed_type tm && signed_type td && signed_type tr then
      if Int.eq k (Int.repr 2) && Int.eq d (Int.repr 2)
      then Some (signed_cancel_tree x, signed_temp x) else None
    else None
  | _ => None end.

Theorem select_signed_cancel_sound a g c : select_signed_cancel a = Some (g, c) ->
  ClightTreeRewrite.expression_contract a g c.
Proof.
  unfold select_signed_cancel; intro SELECT.
  repeat match type of SELECT with
  | context [if ?x then _ else _] => destruct x eqn:?; cbn beta iota zeta in SELECT; try discriminate
  | context [match ?x with _ => _ end] => destruct x; cbn beta iota zeta in SELECT; try discriminate
  end.
  repeat match goal with H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?] end.
  repeat match goal with H : signed_type _ = true |- _ => apply signed_type_correct in H; subst end.
  repeat match goal with H : Int.eq _ _ = true |- _ => apply Int.same_if_eq in H; subst end.
  inversion SELECT; subst. apply encoded_decision_rule_sound.
Qed.

Definition select_signed_memory_root a :=
  match select_signed_cancel a with Some r => Some r | None => select_memory_root a end.
Definition select_signed_memory_rewrites := select_tree_deep select_signed_memory_root.

Theorem select_signed_memory_root_sound a g c : select_signed_memory_root a = Some (g, c) ->
  ClightTreeRewrite.expression_contract a g c.
Proof.
  unfold select_signed_memory_root; intro SELECT.
  destruct (select_signed_cancel a) as [[gg cc]|] eqn:SIGNED.
  - inversion SELECT; subst; eapply select_signed_cancel_sound; eauto.
  - eapply select_memory_root_sound; eauto.
Qed.

Theorem select_signed_memory_rewrites_sound a g c :
  select_signed_memory_rewrites a = Some (g, c) -> ClightTreeRewrite.expression_contract a g c.
Proof. apply select_tree_deep_sound; exact select_signed_memory_root_sound. Qed.

Example signed_cancellation_safe_boundary : word_range_bool (1073741823 * 2) = true.
Proof. vm_compute; reflexivity. Qed.
Example signed_cancellation_overflow_boundary : word_range_bool (1073741824 * 2) = false.
Proof. vm_compute; reflexivity. Qed.
Example signed_cancellation_negative_boundary : word_range_bool (-1073741824 * 2) = true.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions signed_cancel_rule.
Print Assumptions select_signed_memory_rewrites_sound.
