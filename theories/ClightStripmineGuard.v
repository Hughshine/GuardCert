From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import Values.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import AbstractGuard SemanticFacts ClightCondition ClightPureExpr
  ClightNoWrap ClightCountedLoop ClightRedundantSet ClightPositiveCheck ClightMatrixGuard ClightRectangularGuard.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition stripmine_guard_domain iterator bound s := register_domain iterator s /\ register_domain bound s.
Definition stripmine_bound_limit width := Int.max_signed - Z.of_nat width.
Definition stripmine_guard_property width iterator bound (_ : unit) s :=
  register_equals iterator Int.zero tt s /\ register_range bound (stripmine_bound_limit width) s.
Definition stripmine_guard_accept width iterator bound (_ : unit) s :=
  register_flag iterator Int.zero s && register_range_flag bound (stripmine_bound_limit width) s.
Definition stripmine_guard_tree width iterator bound :=
  Test (register_guard iterator Int.zero) (register_range_tree bound (stripmine_bound_limit width)) (Decision false).
Lemma stripmine_bound_limit_range width : 0 < Z.of_nat width <= Int.max_signed -> signed_range (stripmine_bound_limit width).
Proof. unfold signed_range, stripmine_bound_limit; change Int.min_signed with (-2147483648); lia. Qed.
Lemma stripmine_guard_accept_sound width iterator bound :
  0 < Z.of_nat width <= Int.max_signed -> forall a s, stripmine_guard_domain iterator bound s ->
  stripmine_guard_accept width iterator bound a s = true -> stripmine_guard_property width iterator bound a s.
Proof.
  intros VALID [] s [I B]; unfold stripmine_guard_accept; rewrite andb_true_iff; intros [ZERO RANGE].
  split; [exact (register_flag_evidence Int.zero I ZERO)|].
  eapply register_range_sound; [apply stripmine_bound_limit_range; exact VALID|exact B|exact RANGE].
Qed.
Lemma stripmine_guard_tree_run width iterator bound s : stripmine_guard_domain iterator bound s ->
  decision_run s (stripmine_guard_tree width iterator bound) (stripmine_guard_accept width iterator bound tt s).
Proof.
  intros [I B]; unfold stripmine_guard_tree, stripmine_guard_accept.
  eapply run_test; [apply register_expression_test; exact I|].
  destruct (register_flag iterator Int.zero s); cbn [andb]; [apply register_range_tree_run; exact B|constructor].
Qed.
Lemma stripmine_guard_tree_pure width iterator bound : pure_tree (stripmine_guard_tree width iterator bound).
Proof. unfold stripmine_guard_tree; constructor; [repeat constructor|apply register_range_tree_pure|constructor]. Qed.
Definition stripmine_guard_dimension width iterator bound (VALID : 0 < Z.of_nat width <= Int.max_signed) :=
  @positive_dimension clight_entry unit (stripmine_guard_domain iterator bound)
    (stripmine_guard_property width iterator bound) (stripmine_guard_accept width iterator bound)
    (@stripmine_guard_accept_sound width iterator bound VALID).
Definition stripmine_guard_primitives width iterator bound (VALID : 0 < Z.of_nat width <= Int.max_signed) :=
  @positive_tree_primitives unit (stripmine_guard_domain iterator bound)
    (stripmine_guard_property width iterator bound) (stripmine_guard_accept width iterator bound)
    (@stripmine_guard_accept_sound width iterator bound VALID)
    (fun _ => stripmine_guard_tree width iterator bound)
    (fun _ => stripmine_guard_tree_pure width iterator bound)
    (fun a s DOMAIN => match a with tt => stripmine_guard_tree_run width DOMAIN end).
Print Assumptions stripmine_guard_primitives.
