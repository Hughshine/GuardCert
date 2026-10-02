From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import Values.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import AbstractGuard SemanticFacts ClightCondition ClightPureExpr
  ClightNoWrap ClightRedundantSet ClightPositiveCheck.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Entry safety is conditional: the source need not read the inner bound on
    an outer zero-trip path. The check may read it only after the first two
    comparisons establish entry into the source body. *)
Definition matrix_guard_domain iterator bound inner_bound s :=
  register_domain iterator s /\ register_domain bound s /\
  (register_equals iterator (Int.repr 0) tt s -> register_equals bound (Int.repr 2) tt s ->
    register_domain inner_bound s).
Definition matrix_guard_property iterator bound inner_bound (_ : unit) s :=
  register_equals iterator (Int.repr 0) tt s /\ register_equals bound (Int.repr 2) tt s /\
  register_equals inner_bound (Int.repr 2) tt s.
Definition matrix_guard_accept iterator bound inner_bound (_ : unit) s :=
  register_flag iterator (Int.repr 0) s && register_flag bound (Int.repr 2) s &&
    register_flag inner_bound (Int.repr 2) s.
Definition matrix_guard_tree iterator bound inner_bound :=
  Test (register_guard iterator (Int.repr 0))
    (Test (register_guard bound (Int.repr 2)) (register_tree inner_bound (Int.repr 2)) (Decision false))
    (Decision false).

Lemma register_flag_evidence x c s : register_domain x s -> register_flag x c s = true ->
  register_equals x c tt s.
Proof.
  intros [n LOOKUP] ACCEPT; unfold register_flag, temp_word in ACCEPT; rewrite LOOKUP in ACCEPT.
  apply Int.same_if_eq in ACCEPT; subst n; exact LOOKUP.
Qed.

Lemma register_expression_test x c s : register_domain x s ->
  expression_test (register_guard x c) s (register_flag x c s).
Proof.
  intros [n LOOKUP]; exists (Val.of_bool (Int.eq n c)); split.
  - eapply eval_Ebinop; [constructor; exact LOOKUP|constructor|reflexivity].
  - unfold register_flag, temp_word; rewrite LOOKUP; apply bool_of_bool.
Qed.

Lemma matrix_guard_accept_sound iterator bound inner_bound :
  forall a s, matrix_guard_domain iterator bound inner_bound s ->
    matrix_guard_accept iterator bound inner_bound a s = true ->
    matrix_guard_property iterator bound inner_bound a s.
Proof.
  intros [] s [I [N M]] ACCEPT; unfold matrix_guard_accept in ACCEPT.
  apply andb_true_iff in ACCEPT as [PREFIX INNER]; apply andb_true_iff in PREFIX as [ITERATOR BOUND].
  pose proof (register_flag_evidence (Int.repr 0) I ITERATOR) as ZERO.
  pose proof (register_flag_evidence (Int.repr 2) N BOUND) as TWO.
  split; [exact ZERO|split; [exact TWO|]]. eapply register_flag_evidence; eauto.
Qed.

Lemma matrix_guard_tree_pure iterator bound inner_bound :
  pure_tree (matrix_guard_tree iterator bound inner_bound).
Proof. repeat constructor. Qed.

Lemma matrix_guard_tree_run iterator bound inner_bound s :
  matrix_guard_domain iterator bound inner_bound s ->
  decision_run s (matrix_guard_tree iterator bound inner_bound)
    (matrix_guard_accept iterator bound inner_bound tt s).
Proof.
  intros [I [N M]]; unfold matrix_guard_tree, matrix_guard_accept.
  eapply run_test; [apply register_expression_test; exact I|].
  destruct (register_flag iterator (Int.repr 0) s) eqn:ITERATOR; cbn; [|constructor].
  eapply run_test; [apply register_expression_test; exact N|].
  destruct (register_flag bound (Int.repr 2) s) eqn:BOUND; cbn; [|constructor].
  apply register_tree_run; apply M; eapply register_flag_evidence; eauto.
Qed.

Definition matrix_guard_dimension iterator bound inner_bound :=
  @positive_dimension clight_entry unit (matrix_guard_domain iterator bound inner_bound)
    (matrix_guard_property iterator bound inner_bound) (matrix_guard_accept iterator bound inner_bound)
    (@matrix_guard_accept_sound iterator bound inner_bound).
Definition matrix_guard_primitives iterator bound inner_bound :=
  @positive_tree_primitives unit (matrix_guard_domain iterator bound inner_bound)
    (matrix_guard_property iterator bound inner_bound) (matrix_guard_accept iterator bound inner_bound)
    (@matrix_guard_accept_sound iterator bound inner_bound)
    (fun _ => matrix_guard_tree iterator bound inner_bound)
    (fun _ => matrix_guard_tree_pure iterator bound inner_bound)
    (fun a s DOMAIN => match a with tt => matrix_guard_tree_run DOMAIN end).

Print Assumptions matrix_guard_tree_run.
Print Assumptions matrix_guard_primitives.
