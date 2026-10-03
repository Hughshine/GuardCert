From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightPureExpr ClightRedundantSet ClightNoWrap ClightCountedLoop ClightRectangularGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint memory_coordinate_activation_flag bounds coordinates s :=
  match bounds,coordinates with
  | [],[] => true
  | bound::rest,coordinate::tail => negb (register_at_most bound coordinate s) &&
      memory_coordinate_activation_flag rest tail s
  | _,_ => false end.
Fixpoint memory_coordinate_activation_tree bounds coordinates :=
  match bounds,coordinates with
  | [],[] => Decision true
  | bound::rest,coordinate::tail => Test (register_at_most_expr bound coordinate)
      (Decision false) (memory_coordinate_activation_tree rest tail)
  | _,_ => Decision false end.
Lemma memory_coordinate_activation_pure bounds : forall coordinates,
  pure_tree (memory_coordinate_activation_tree bounds coordinates).
Proof. induction bounds; intros [|coordinate coordinates]; cbn; repeat constructor; apply IHbounds. Qed.
Lemma memory_coordinate_activation_run bounds coordinates s :
  Forall (fun bound => register_domain bound s) bounds ->
  decision_run s (memory_coordinate_activation_tree bounds coordinates)
    (memory_coordinate_activation_flag bounds coordinates s).
Proof.
  revert coordinates; induction bounds as [|bound bounds IH]; intros [|coordinate coordinates] DOMAIN; cbn; try constructor.
  inversion DOMAIN; subst; eapply run_test; [apply register_at_most_test; eassumption|].
  destruct (register_at_most bound coordinate s); cbn; [constructor|apply IH; assumption].
Qed.
Theorem memory_coordinate_activation_exact bounds coordinates s :
  Forall (fun bound => register_domain bound s) bounds -> forall flag,
  decision_run s (memory_coordinate_activation_tree bounds coordinates) flag <->
  flag = memory_coordinate_activation_flag bounds coordinates s.
Proof.
  intros DOMAIN flag; split.
  - intro RUN; eapply pure_tree_determinate; [apply memory_coordinate_activation_pure|exact RUN|apply memory_coordinate_activation_run; exact DOMAIN].
  - intro SAME; subst; apply memory_coordinate_activation_run; exact DOMAIN.
Qed.
Lemma memory_coordinate_activation_semantics bounds coordinates s :
  Forall signed_range coordinates ->
  (memory_coordinate_activation_flag bounds coordinates s = true <->
   Forall2 (fun coordinate bound => coordinate < Int.signed (temp_word bound (entry_temps s))) coordinates bounds).
Proof.
  revert bounds; induction coordinates as [|coordinate coordinates IH]; intros [|bound bounds] RANGE; cbn.
  - split; intro RUN; constructor.
  - split; intro RUN; [discriminate|inversion RUN].
  - split; intro RUN; [discriminate|inversion RUN].
  - split.
    + intro RUN; inversion RANGE; subst.
    apply andb_true_iff in RUN as [HEAD TAIL]; constructor.
      * unfold register_at_most in HEAD; rewrite negb_involutive in HEAD; unfold Int.lt in HEAD.
      rewrite Int.signed_repr in HEAD by assumption.
      destruct (zlt coordinate (Int.signed (temp_word bound (entry_temps s)))); congruence.
      * apply (proj1 (IH bounds ltac:(assumption))); exact TAIL.
    + intro RUN; inversion RUN; inversion RANGE; subst.
    apply andb_true_iff; split.
      * unfold register_at_most; rewrite negb_involutive; unfold Int.lt; rewrite Int.signed_repr by assumption.
      destruct (zlt coordinate (Int.signed (temp_word bound (entry_temps s)))); [reflexivity|lia].
      * apply (proj2 (IH bounds ltac:(assumption))); assumption.
Qed.
Print Assumptions memory_coordinate_activation_exact.
Print Assumptions memory_coordinate_activation_semantics.
