From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Integers Coqlib.
From compcert.common Require Import AST Values.
From compcert.cfrontend Require Import Clight Ctypes Cop.
From Guard Require Import ClightCondition ClightPureExpr ClightGuard ClightCountedLoop
  ClightRectangularGuard ClightRedundantSet ClightNoWrap.
From GuardMemory Require Import GuardMemoryTripleGuard GuardMemoryRecursiveSource GuardMemoryNaryRanges.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_parameter_nonnegative identifier s :=
  negb (Int.lt (temp_word identifier (entry_temps s)) Int.zero).
Definition memory_parameter_nonnegative_expr identifier :=
  Ebinop Ole (Econst_int Int.zero type_int32s) (Etempvar identifier type_int32s) type_int32s.
Definition memory_parameter_range_flag identifier cap s :=
  memory_parameter_nonnegative identifier s && register_at_most identifier (cap-1) s.
Definition memory_parameter_range_tree identifier cap :=
  Test (memory_parameter_nonnegative_expr identifier)
    (Test (register_at_most_expr identifier (cap-1)) (Decision true) (Decision false)) (Decision false).
Lemma memory_parameter_nonnegative_test identifier s : register_domain identifier s ->
  expression_test (memory_parameter_nonnegative_expr identifier) s (memory_parameter_nonnegative identifier s).
Proof.
  intros [word LOOKUP]; exists (Val.of_bool (negb (Int.lt word Int.zero))); split.
  - eapply eval_Ebinop; [constructor|constructor; exact LOOKUP|reflexivity].
  - unfold memory_parameter_nonnegative,temp_word; rewrite LOOKUP; apply bool_of_bool.
Qed.
Lemma memory_parameter_range_run identifier cap s : register_domain identifier s ->
  decision_run s (memory_parameter_range_tree identifier cap) (memory_parameter_range_flag identifier cap s).
Proof.
  intro DOMAIN; unfold memory_parameter_range_tree,memory_parameter_range_flag.
  eapply run_test; [apply memory_parameter_nonnegative_test; exact DOMAIN|].
  destruct (memory_parameter_nonnegative identifier s); cbn; [|constructor].
  eapply run_test; [apply register_at_most_test; exact DOMAIN|].
  destruct (register_at_most identifier (cap-1) s); constructor.
Qed.
Lemma memory_parameter_range_pure identifier cap : pure_tree (memory_parameter_range_tree identifier cap).
Proof. repeat constructor. Qed.
Lemma memory_parameter_range_exact identifier cap s : register_domain identifier s ->
  forall flag, decision_run s (memory_parameter_range_tree identifier cap) flag <->
    flag = memory_parameter_range_flag identifier cap s.
Proof.
  intros DOMAIN flag; split.
  - intro RUN; eapply pure_tree_determinate; [apply memory_parameter_range_pure|exact RUN|].
    apply memory_parameter_range_run; exact DOMAIN.
  - intro SAME; subst; apply memory_parameter_range_run; exact DOMAIN.
Qed.
Lemma memory_parameter_range_sound identifier cap s :
  0 < cap -> signed_range cap -> memory_parameter_range_flag identifier cap s = true ->
  0 <= Int.signed (temp_word identifier (entry_temps s)) < cap.
Proof.
  intros POSITIVE SIGNED ACCEPT; unfold memory_parameter_range_flag in ACCEPT.
  apply andb_true_iff in ACCEPT as [LOW HIGH].
  unfold memory_parameter_nonnegative,Int.lt in LOW; rewrite Int.signed_zero in LOW.
  unfold register_at_most,Int.lt in HIGH.
  rewrite Int.signed_repr in HIGH by (unfold signed_range in *;
    change Int.min_signed with (-2147483648) in *; lia).
  destruct (zlt (Int.signed (temp_word identifier (entry_temps s))) 0);
    destruct (zlt (cap-1) (Int.signed (temp_word identifier (entry_temps s)))); cbn in LOW,HIGH;
    try discriminate; lia.
Qed.

Fixpoint memory_parameter_ranges_accept caps parameters s :=
  match caps,parameters with
  | [],[] => true
  | cap::rest,identifier::tail => memory_parameter_range_flag identifier cap s && memory_parameter_ranges_accept rest tail s
  | _,_ => false end.
Fixpoint memory_parameter_ranges_tree caps parameters terminal :=
  match caps,parameters with
  | [],[] => terminal
  | cap::rest,identifier::tail => decision_bind (memory_parameter_range_tree identifier cap)
      (memory_parameter_ranges_tree rest tail terminal) (Decision false)
  | _,_ => Decision false end.
Theorem memory_parameter_ranges_exact caps parameters terminal s accepted :
  Forall (fun identifier => register_domain identifier s) parameters ->
  (memory_parameter_ranges_accept caps parameters s = true -> forall flag, decision_run s terminal flag <-> flag = accepted) ->
  forall flag, decision_run s (memory_parameter_ranges_tree caps parameters terminal) flag <->
    flag = memory_parameter_ranges_accept caps parameters s && accepted.
Proof.
  revert parameters; induction caps as [|cap caps IH]; intros [|identifier parameters] DOMAIN TERMINAL flag;
    cbn [memory_parameter_ranges_tree memory_parameter_ranges_accept] in *.
  - apply TERMINAL; reflexivity.
  - split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
  - split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
  - inversion DOMAIN as [|head tail WORD WORDS]; subst.
    rewrite <-andb_assoc; apply memory_guard_gate_exact; [apply memory_parameter_range_exact; exact WORD|].
    intro RANGE; apply IH; [exact WORDS|].
    intro ALL; apply TERMINAL; rewrite RANGE,ALL; reflexivity.
Qed.
Theorem memory_parameter_ranges_sound caps parameters s :
  Forall (fun cap => 0 < cap /\ signed_range cap) caps ->
  memory_parameter_ranges_accept caps parameters s = true ->
  memory_nary_ranges caps (map (fun identifier => Int.signed (temp_word identifier (entry_temps s))) parameters).
Proof.
  intro CAPS; revert parameters; induction CAPS as [|cap caps [POSITIVE SIGNED] CAPS IH];
    intros [|identifier parameters] ACCEPT; cbn in *; try discriminate; constructor.
  - apply andb_true_iff in ACCEPT as [HEAD TAIL]; eapply memory_parameter_range_sound; eassumption.
  - apply andb_true_iff in ACCEPT as [HEAD TAIL]; apply IH; exact TAIL.
Qed.
Print Assumptions memory_parameter_range_exact.
Print Assumptions memory_parameter_ranges_sound.
