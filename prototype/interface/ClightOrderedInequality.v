From Stdlib Require Import Bool ZArith Lia.
From compcert.lib Require Import Integers Coqlib.
From compcert.common Require Import Values.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightGuard ClightCondition ClightNoWrap ClightPureExpr.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite ClightQuietDeterminacy
  ClightConditionComposition ClightReadonlyLoadedTreeSynthesis ClightReadonlyExpression ClightEqualityHead.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition comparison_operands left right entry first second :=
  eval_expr (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry) left (Vint first) /\
  eval_expr (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry) right (Vint second).
Definition comparison_domain left right entry := exists first second, comparison_operands left right entry first second.
Definition comparison_ordered left right entry := exists first second,
  comparison_operands left right entry first second /\ Int.signed first <= Int.signed second.
Definition comparison_source left right := Ebinop One left right type_int32s.
Definition comparison_candidate left right := Ebinop Olt left right type_int32s.
Definition comparison_check_expression left right := Ebinop Ole left right type_int32s.
Definition comparison_check left right := Test (comparison_check_expression left right) (Decision true) (Decision false).

Section SIGNED_WORD_OPERANDS.
Variable left right : expr.
Hypothesis LEFT : typeof left = type_int32s.
Hypothesis RIGHT : typeof right = type_int32s.
Lemma comparison_source_values ge locals le memory value :
  eval_expr ge locals le memory (comparison_source left right) value ->
  exists first second, eval_expr ge locals le memory left (Vint first) /\
    eval_expr ge locals le memory right (Vint second) /\ value = Val.of_bool (negb (Int.eq first second)).
Proof.
  intro EVAL; apply scalar_binary_inv in EVAL; destruct EVAL as [first [second [L [R OP]]]].
  rewrite LEFT, RIGHT in OP; destruct first, second; try discriminate OP.
  change (Some (Val.of_bool (negb (Int.eq i i0))) = Some value) in OP;
    injection OP as SAME; exists i, i0; repeat split; congruence.
Qed.
Lemma comparison_source_eval entry first second : comparison_operands left right entry first second ->
  eval_expr (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    (comparison_source left right) (Val.of_bool (negb (Int.eq first second))).
Proof.
  intros [L R]; eapply eval_Ebinop with (v1 := Vint first) (v2 := Vint second);
    [exact L|exact R|rewrite LEFT, RIGHT; reflexivity].
Qed.
Lemma comparison_candidate_eval entry first second : comparison_operands left right entry first second ->
  eval_expr (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    (comparison_candidate left right) (Val.of_bool (Int.lt first second)).
Proof.
  intros [L R]; eapply eval_Ebinop with (v1 := Vint first) (v2 := Vint second);
    [exact L|exact R|rewrite LEFT, RIGHT; reflexivity].
Qed.
Lemma comparison_check_test entry first second : comparison_operands left right entry first second ->
  expression_test (comparison_check_expression left right) entry (negb (Int.lt second first)).
Proof.
  intros [L R]; exists (Val.of_bool (negb (Int.lt second first))); split; [|apply bool_of_bool].
  eapply eval_Ebinop with (v1 := Vint first) (v2 := Vint second);
    [exact L|exact R|rewrite LEFT, RIGHT; reflexivity].
Qed.
Definition comparison_condition : readonly_condition readonly_expression_host
  (comparison_domain left right) (comparison_ordered left right) (comparison_check left right).
Proof.
  apply (@fragment_condition_for_expression (adapter_entry true) fragment_observation (@eq fragment_observation)).
  apply readonly_expression_condition.
  - intros entry [first [second VALUES]]; exists (negb (Int.lt second first)); apply comparison_check_test; exact VALUES.
  - intros entry [first [second VALUES]] TEST.
    pose proof (comparison_check_test VALUES) as KNOWN.
    assert (ACCEPT : negb (Int.lt second first) = true)
      by (eapply readonly_test_determinate; [exact KNOWN|exact TEST]).
    exists first, second; split; [exact VALUES|].
    unfold Int.lt in ACCEPT; destruct (zlt (Int.signed second) (Int.signed first)); cbn in ACCEPT; [discriminate|lia].
Defined.
Lemma comparison_local : conditional_equivalence readonly_expression_host
  (comparison_domain left right) (comparison_ordered left right)
  (Evaluate (comparison_source left right)) (Evaluate (comparison_candidate left right)).
Proof.
  intros entry value [DOMAIN [first [second [VALUES ORDER]]]].
  pose proof (@equality_head_boolean first second ORDER) as SAME.
  pose proof (comparison_source_eval VALUES) as SOURCE; rewrite SAME in SOURCE.
  pose proof (comparison_candidate_eval VALUES) as CANDIDATE.
  rewrite !readonly_expression_leaf; split; intro RUN.
  - pose proof (proj1 (expressions_determinate (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry))
      _ _ RUN _ CANDIDATE) as VALUE; subst value; exact SOURCE.
  - pose proof (proj1 (expressions_determinate (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry))
      _ _ RUN _ SOURCE) as VALUE; subst value; exact CANDIDATE.
Qed.
Definition ordered_inequality_rule : readonly_expression_rule (comparison_source left right).
Proof.
  refine (@ReadonlyExpressionRule (comparison_source left right) (comparison_candidate left right)
    (comparison_check left right) (comparison_domain left right) (comparison_ordered left right)
    eq_refl comparison_condition comparison_local _).
  intros ge locals le memory value EVAL.
  destruct (comparison_source_values EVAL) as [first [second [L [R SAME]]]].
  exists first, second; split; assumption.
Defined.
End SIGNED_WORD_OPERANDS.
Print Assumptions comparison_source_values.
Print Assumptions comparison_condition.
Print Assumptions comparison_local.
Print Assumptions ordered_inequality_rule.
