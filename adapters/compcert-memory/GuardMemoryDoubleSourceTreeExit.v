From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values.
From compcert.cfrontend Require Import Clight.
From GuardMemory Require Import GuardMemoryDoubleSourceTreeData
  GuardMemoryDoubleRectangularNestData GuardMemoryLongLoopSettle GuardMemoryLongRangeSource.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The existing fixed setter gives its head precedence. Consequently sequence
    records the second child's assignments first. Siblings may reuse iterators.
    A range initializes its own iterator even when empty; an unreached child's
    temporaries retain their entry values. Bounds depend on original headers. *)
Fixpoint double_source_tree_exit_assignments valuation tree : list (ident*val) :=
  match tree with
  | DoubleTreeSkip | DoubleTreePoint _ _ => []
  | DoubleTreeSequence first second =>
      double_source_tree_exit_assignments valuation second++double_source_tree_exit_assignments valuation first
  | DoubleTreeRange _ iterator start bound child =>
      let lower := Int.signed start in
      let upper := double_tree_bound_value valuation bound in
      (iterator,Vlong (Int64.repr (Z.max lower upper)))::
        (if lower <? upper then double_source_tree_exit_assignments valuation child else [])
  end.
Definition double_source_tree_exit valuation tree temps :=
  double_rectangular_set_assignments (double_source_tree_exit_assignments valuation tree) temps.

Lemma double_tree_fixed_setters_append first second temps :
  double_rectangular_set_assignments (first++second) temps=
    double_rectangular_set_assignments first (double_rectangular_set_assignments second temps).
Proof.
  induction first as [|[key value] rest IH]; cbn [double_rectangular_set_assignments app];
    [reflexivity|rewrite IH; reflexivity].
Qed.
Theorem double_source_tree_exit_sequence valuation first second temps :
  double_source_tree_exit valuation (DoubleTreeSequence first second) temps=
    double_source_tree_exit valuation second (double_source_tree_exit valuation first temps).
Proof. apply double_tree_fixed_setters_append. Qed.
Lemma double_source_tree_exit_assignments_subset valuation tree key :
  In key (map fst (double_source_tree_exit_assignments valuation tree)) ->
    In key (double_source_tree_writes tree).
Proof.
  induction tree; cbn [double_source_tree_exit_assignments double_source_tree_writes map fst];
    intro MEMBER; try contradiction.
  - rewrite map_app in MEMBER; apply in_app_or in MEMBER as [SECOND|FIRST]; apply in_or_app;
      [right; apply IHtree2|left; apply IHtree1]; assumption.
  - destruct MEMBER as [SAME|MEMBER]; [left; exact SAME|right].
    destruct (Int.signed start <? double_tree_bound_value valuation bound); [apply IHtree; exact MEMBER|contradiction].
Qed.
Theorem double_source_tree_exit_idempotent valuation tree temps :
  double_source_tree_exit valuation tree (double_source_tree_exit valuation tree temps)=
    double_source_tree_exit valuation tree temps.
Proof. apply double_rectangular_set_assignments_idempotent. Qed.
Theorem double_source_tree_exit_frame valuation tree temps key :
  ~ In key (double_source_tree_writes tree) -> (double_source_tree_exit valuation tree temps) ! key=temps ! key.
Proof.
  intro FRESH; apply double_rectangular_set_assignments_frame; intro MEMBER;
    apply FRESH; eapply double_source_tree_exit_assignments_subset; exact MEMBER.
Qed.
Theorem double_source_tree_exit_commute valuation tree temps key word :
  ~ In key (double_source_tree_writes tree) ->
  double_source_tree_exit valuation tree (PTree.set key word temps)=
    PTree.set key word (double_source_tree_exit valuation tree temps).
Proof.
  intro FRESH; apply double_rectangular_set_assignments_commute; intro MEMBER;
    apply FRESH; eapply double_source_tree_exit_assignments_subset; exact MEMBER.
Qed.
Theorem double_source_tree_exit_ancestor_frame p controls tree valuation temps key :
  double_source_tree_checked p controls tree -> In key controls ->
    (double_source_tree_exit valuation tree temps) ! key=temps ! key.
Proof.
  intros CHECK MEMBER; apply double_source_tree_exit_frame;
    eapply double_source_tree_writes_avoid; eassumption.
Qed.

(** The arbitrary signed-start loop service iterates the child's fixed setter.
    Idempotence collapses repeated child completions. Iterator freshness suffices;
    child iterators need not be globally distinct across a sequence. *)
Theorem double_source_tree_range_settled_exit valuation raw iterator start bound child temps :
  ~ In iterator (double_source_tree_writes child) ->
  memory_long_settled_exit iterator (fun _ => double_source_tree_exit valuation child)
    (memory_long_range_count (Int.signed start) (double_tree_bound_value valuation bound))
    (Int.signed start) (PTree.set iterator (Vlong (Int64.repr (Int.signed start))) temps)=
    double_source_tree_exit valuation (DoubleTreeRange raw iterator start bound child) temps.
Proof.
  intro FRESH.
  pose proof (memory_long_range_end (Int.signed start) (double_tree_bound_value valuation bound)) as END.
  destruct (memory_long_range_count (Int.signed start) (double_tree_bound_value valuation bound)) as [|count] eqn:COUNT.
  - cbn [memory_long_settled_exit] in *.
    pose proof (Z.le_max_r (Int.signed start) (double_tree_bound_value valuation bound)).
    assert (EMPTY : (Int.signed start <? double_tree_bound_value valuation bound)=false)
      by (apply Z.ltb_ge; lia).
    unfold double_source_tree_exit; cbn [double_source_tree_exit_assignments]; rewrite EMPTY.
    cbn [double_rectangular_set_assignments]; f_equal; f_equal; f_equal; lia.
  - assert (ACTIVE : Int.signed start < double_tree_bound_value valuation bound).
    { destruct (Z_le_gt_dec (double_tree_bound_value valuation bound) (Int.signed start)); [|lia].
      rewrite Z.max_l in END by lia; rewrite Nat2Z.inj_succ in END.
      pose proof (Nat2Z.is_nonneg count); lia. }
    rewrite (@memory_long_constant_settle_exit iterator (double_source_tree_exit valuation child)
      ltac:(intro le; apply double_source_tree_exit_idempotent)
      ltac:(intros le word; apply double_source_tree_exit_commute; exact FRESH)).
    rewrite double_source_tree_exit_commute by exact FRESH; rewrite PTree.set2,END.
    unfold double_source_tree_exit; cbn [double_source_tree_exit_assignments].
    rewrite (proj2 (Z.ltb_lt _ _) ACTIVE); reflexivity.
Qed.

Print Assumptions double_source_tree_exit_sequence.
Print Assumptions double_source_tree_exit_assignments_subset.
Print Assumptions double_source_tree_exit_idempotent.
Print Assumptions double_source_tree_exit_frame.
Print Assumptions double_source_tree_exit_commute.
Print Assumptions double_source_tree_exit_ancestor_frame.
Print Assumptions double_source_tree_range_settled_exit.
