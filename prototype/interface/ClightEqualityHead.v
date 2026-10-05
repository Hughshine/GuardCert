From Stdlib Require Import Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import Values.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import AbstractGuard SemanticFacts ClightGuard ClightCondition ClightNoWrap ClightPureExpr
  ClightDecisionRule ClightPositiveCheck ClightRedundantSet.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite ClightReadonlyTreeSynthesis
  ClightReadonlyExpression ClightCircularCounter ClightEqualityLoop ClightQuietDeterminacy.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition equality_head_property iterator bound (_ : unit) entry :=
  Int.signed (temp_word iterator (entry_temps entry)) <= Int.signed (temp_word bound (entry_temps entry)).
Definition equality_head_guard_expression iterator bound :=
  Ebinop Ole (signed_word_view iterator) (signed_word_view bound) type_int32s.
Definition equality_head_guard iterator bound :=
  Test (equality_head_guard_expression iterator bound) (Decision true) (Decision false).
Definition equality_head_flag iterator bound (_ : unit) entry :=
  negb (Int.lt (temp_word bound (entry_temps entry)) (temp_word iterator (entry_temps entry))).
Lemma equality_head_guard_test iterator bound entry : equality_domain iterator bound entry ->
  expression_test (equality_head_guard_expression iterator bound) entry (equality_head_flag iterator bound tt entry).
Proof.
  intros [[word ITER] [upper BOUND]]; destruct entry as [ge locals le memory].
  exists (Val.of_bool (negb (Int.lt upper word))); split.
  - eapply eval_Ebinop with (v1 := Vint word) (v2 := Vint upper);
      [apply signed_word_view_evaluation; exact ITER|apply signed_word_view_evaluation; exact BOUND|reflexivity].
  - unfold equality_head_flag, temp_word; rewrite ITER, BOUND; apply bool_of_bool.
Qed.
Lemma equality_head_guard_sound iterator bound a entry : equality_domain iterator bound entry ->
  equality_head_flag iterator bound a entry = true -> equality_head_property iterator bound a entry.
Proof.
  intros DOMAIN ACCEPT; unfold equality_head_property; unfold equality_head_flag, Int.lt in ACCEPT.
  destruct (zlt (Int.signed (temp_word bound (entry_temps entry)))
    (Int.signed (temp_word iterator (entry_temps entry)))); cbn in ACCEPT; [discriminate|lia].
Qed.
Lemma equality_head_guard_run iterator bound entry : equality_domain iterator bound entry ->
  decision_run entry (equality_head_guard iterator bound) (equality_head_flag iterator bound tt entry).
Proof.
  intro DOMAIN; unfold equality_head_guard; eapply run_test; [apply equality_head_guard_test; exact DOMAIN|].
  destruct (equality_head_flag iterator bound tt entry); constructor.
Qed.
Definition equality_head_dimension iterator bound :=
  @positive_dimension clight_entry unit (equality_domain iterator bound)
    (equality_head_property iterator bound) (equality_head_flag iterator bound) (@equality_head_guard_sound iterator bound).
Definition equality_head_primitives iterator bound :=
  @positive_tree_primitives unit (equality_domain iterator bound) (equality_head_property iterator bound)
    (equality_head_flag iterator bound) (@equality_head_guard_sound iterator bound)
    (fun _ => equality_head_guard iterator bound) (fun _ => ltac:(repeat constructor))
    (fun a entry DOMAIN => match a with tt => equality_head_guard_run DOMAIN end).
Definition equality_head_condition iterator bound : readonly_condition readonly_expression_host
  (equality_domain iterator bound) (equality_head_property iterator bound tt)
  (synthesize_decision_tree (equality_head_primitives iterator bound) (Fact tt)).
Proof.
  apply (@fragment_condition_for_expression (adapter_entry true) fragment_observation (@eq fragment_observation)).
  change (readonly_condition (readonly_clight_host (adapter_entry true) (@eq fragment_observation))
    (equality_domain iterator bound)
    (fun entry => formula_property (atom_property (equality_head_dimension iterator bound)) (Fact tt) entry)
    (synthesize_decision_tree (equality_head_primitives iterator bound) (Fact tt))).
  apply synthesized_scalar_tree_condition with (D := equality_head_dimension iterator bound);
    intros []; cbn [equality_head_primitives positive_tree_primitives]; repeat constructor.
Defined.
Lemma equality_head_boolean word upper : Int.signed word <= Int.signed upper ->
  negb (Int.eq word upper) = Int.lt word upper.
Proof.
  intro RANGE; pose proof (Int.eq_spec word upper) as EQ.
  unfold Int.lt; destruct (Int.eq word upper) eqn:SAME;
    destruct (zlt (Int.signed word) (Int.signed upper)); cbn in *; try congruence.
  - subst word; lia.
  - exfalso; apply EQ; rewrite <- (Int.repr_signed word), <- (Int.repr_signed upper); f_equal; lia.
Qed.
Lemma equality_head_source_value ge locals le memory iterator bound value :
  eval_expr ge locals le memory (unsigned_equality_test iterator bound) value ->
  exists word upper, le ! iterator = Some (Vint word) /\ le ! bound = Some (Vint upper) /\
    value = Val.of_bool (negb (Int.eq word upper)).
Proof.
  intro EVAL; apply scalar_binary_inv in EVAL; destruct EVAL as [word [upper [ITER [BOUND OP]]]].
  destruct word, upper; try discriminate OP;
    apply signed_word_view_inverse in ITER; apply signed_word_view_inverse in BOUND.
  change (Some (Val.of_bool (negb (Int.eq i i0))) = Some value) in OP;
    injection OP as SAME; exists i, i0; repeat split; congruence.
Qed.
Lemma equality_head_source_eval ge locals le memory iterator bound word upper :
  le ! iterator = Some (Vint word) -> le ! bound = Some (Vint upper) ->
  eval_expr ge locals le memory (unsigned_equality_test iterator bound) (Val.of_bool (negb (Int.eq word upper))).
Proof.
  intros ITER BOUND; eapply eval_Ebinop with (v1 := Vint word) (v2 := Vint upper);
    [apply signed_word_view_evaluation; exact ITER|apply signed_word_view_evaluation; exact BOUND|reflexivity].
Qed.
Lemma equality_head_candidate_eval ge locals le memory iterator bound word upper :
  le ! iterator = Some (Vint word) -> le ! bound = Some (Vint upper) ->
  eval_expr ge locals le memory (unsigned_order_test iterator bound) (Val.of_bool (Int.lt word upper)).
Proof.
  intros ITER BOUND; eapply eval_Ebinop with (v1 := Vint word) (v2 := Vint upper);
    [apply signed_word_view_evaluation; exact ITER|apply signed_word_view_evaluation; exact BOUND|reflexivity].
Qed.
Lemma equality_head_local iterator bound : conditional_equivalence readonly_expression_host
  (equality_domain iterator bound) (equality_head_property iterator bound tt)
  (Evaluate (unsigned_equality_test iterator bound)) (Evaluate (unsigned_order_test iterator bound)).
Proof.
  intros [ge locals le memory] value [[[word ITER] [upper BOUND]] RANGE].
  unfold equality_head_property, temp_word in RANGE; cbn [entry_temps] in *; rewrite ITER, BOUND in RANGE.
  pose proof (@equality_head_boolean word upper RANGE) as SAME.
  assert (SOURCE := @equality_head_source_eval ge locals le memory iterator bound word upper ITER BOUND).
  assert (CANDIDATE := @equality_head_candidate_eval ge locals le memory iterator bound word upper ITER BOUND).
  rewrite SAME in SOURCE.
  rewrite !readonly_expression_leaf; split; intro RUN.
  - pose proof ((proj1 (expressions_determinate ge locals le memory)) _ _ RUN _ CANDIDATE) as VALUE; subst value; exact SOURCE.
  - pose proof ((proj1 (expressions_determinate ge locals le memory)) _ _ RUN _ SOURCE) as VALUE; subst value; exact CANDIDATE.
Qed.
Definition equality_head_rule iterator bound : readonly_expression_rule (unsigned_equality_test iterator bound).
Proof.
  refine (@ReadonlyExpressionRule (unsigned_equality_test iterator bound) (unsigned_order_test iterator bound)
    (synthesize_decision_tree (equality_head_primitives iterator bound) (Fact tt))
    (equality_domain iterator bound) (equality_head_property iterator bound tt)
    eq_refl (equality_head_condition iterator bound) (@equality_head_local iterator bound) _).
  intros ge locals le memory value EVAL; destruct (equality_head_source_value EVAL) as [word [upper [ITER [BOUND SAME]]]].
  split; [exists word; exact ITER|exists upper; exact BOUND].
Defined.
Print Assumptions equality_head_condition.
Print Assumptions equality_head_local.
Print Assumptions equality_head_rule.

Print Assumptions equality_head_guard_run.
