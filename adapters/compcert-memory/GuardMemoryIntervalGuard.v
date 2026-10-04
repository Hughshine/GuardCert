From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Integers Coqlib.
From compcert.common Require Import AST Values.
From compcert.cfrontend Require Import Clight Ctypes Cop.
From Guard Require Import ClightCondition ClightPureExpr ClightGuard ClightCountedLoop
  ClightRectangularGuard ClightNoWrap ClightRedundantSet.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition signed_interval_lower_flag identifier lower s :=
  negb (Int.lt (temp_word identifier (entry_temps s)) (Int.repr lower)).
Definition signed_interval_lower_expr identifier lower :=
  Ebinop Ole (Econst_int (Int.repr lower) type_int32s) (Etempvar identifier type_int32s) type_int32s.
Definition signed_interval_flag identifier lower upper s :=
  signed_interval_lower_flag identifier lower s && register_at_most identifier (upper-1) s.
Definition signed_interval_tree identifier lower upper :=
  Test (signed_interval_lower_expr identifier lower)
    (Test (register_at_most_expr identifier (upper-1)) (Decision true) (Decision false)) (Decision false).
Lemma signed_interval_lower_test identifier lower s : register_domain identifier s ->
  expression_test (signed_interval_lower_expr identifier lower) s (signed_interval_lower_flag identifier lower s).
Proof.
  intros [word LOOKUP]; exists (Val.of_bool (negb (Int.lt word (Int.repr lower)))); split.
  - eapply eval_Ebinop; [constructor|constructor; exact LOOKUP|reflexivity].
  - unfold signed_interval_lower_flag,temp_word; rewrite LOOKUP; apply bool_of_bool.
Qed.
Lemma signed_interval_run identifier lower upper s : register_domain identifier s ->
  decision_run s (signed_interval_tree identifier lower upper) (signed_interval_flag identifier lower upper s).
Proof.
  intro DOMAIN; unfold signed_interval_tree,signed_interval_flag.
  eapply run_test; [apply signed_interval_lower_test; exact DOMAIN|].
  destruct (signed_interval_lower_flag identifier lower s); cbn; [|constructor].
  eapply run_test; [apply register_at_most_test; exact DOMAIN|].
  destruct (register_at_most identifier (upper-1) s); constructor.
Qed.
Lemma signed_interval_pure identifier lower upper : pure_tree (signed_interval_tree identifier lower upper).
Proof. repeat constructor. Qed.
Lemma signed_interval_encoding_exact identifier lower upper s : register_domain identifier s ->
  forall flag, decision_run s (signed_interval_tree identifier lower upper) flag <->
    flag = signed_interval_flag identifier lower upper s.
Proof.
  intros DOMAIN flag; split.
  - intro RUN; eapply pure_tree_determinate; [apply signed_interval_pure|exact RUN|].
    apply signed_interval_run; exact DOMAIN.
  - intro SAME; subst; apply signed_interval_run; exact DOMAIN.
Qed.
Theorem signed_interval_presumption_exact identifier lower upper s :
  signed_range lower -> signed_range (upper-1) ->
  (signed_interval_flag identifier lower upper s = true <->
    lower <= Int.signed (temp_word identifier (entry_temps s)) < upper).
Proof.
  intros LOW HIGH; unfold signed_interval_flag,signed_interval_lower_flag,register_at_most,Int.lt.
  rewrite !Int.signed_repr by (unfold signed_range in *; assumption).
  destruct (zlt (Int.signed (temp_word identifier (entry_temps s))) lower);
    destruct (zlt (upper-1) (Int.signed (temp_word identifier (entry_temps s)))); cbn;
    split; intro H; try discriminate; try lia; reflexivity.
Qed.
Print Assumptions signed_interval_encoding_exact.
Print Assumptions signed_interval_presumption_exact.
