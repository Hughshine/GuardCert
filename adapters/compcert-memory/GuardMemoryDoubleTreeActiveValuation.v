From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleSourceTreeData
  GuardMemoryDoubleSourceTreeState GuardMemoryDoubleTreeCaptureFacts.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition double_tree_active_values_agree tree first second :=
  forall header, In header (double_source_tree_active_headers first tree) -> second header=first header.
Lemma double_tree_bound_value_agree first second bound :
  second (tree_bound_header bound)=first (tree_bound_header bound) ->
  double_tree_bound_value second bound=double_tree_bound_value first bound.
Proof. intro SAME; unfold double_tree_bound_value; rewrite SAME; reflexivity. Qed.

(** Unread parameters may differ. Only observations reached under the first
    valuation determine the next comparison and hence the complete active path. *)
Theorem double_tree_active_headers_agree tree : forall first second,
  double_tree_active_values_agree tree first second ->
  double_source_tree_active_headers second tree=double_source_tree_active_headers first tree.
Proof.
  induction tree; intros first second AGREE; cbn [double_source_tree_active_headers]; try reflexivity.
  - assert (FIRST : double_source_tree_active_headers second tree1=double_source_tree_active_headers first tree1).
    { apply IHtree1; intros header MEMBER; apply AGREE; cbn; apply in_or_app; left; exact MEMBER. }
    assert (SECOND : double_source_tree_active_headers second tree2=double_source_tree_active_headers first tree2).
    { apply IHtree2; intros header MEMBER; apply AGREE; cbn; apply in_or_app; right; exact MEMBER. }
    rewrite FIRST,SECOND; reflexivity.
  - assert (BOUND : double_tree_bound_value second bound=double_tree_bound_value first bound).
    { apply double_tree_bound_value_agree,AGREE; cbn; left; reflexivity. }
    rewrite BOUND; destruct (Int.signed start <? double_tree_bound_value first bound) eqn:ACTIVE; [|reflexivity].
    rewrite (IHtree first second); [reflexivity|].
    intros header MEMBER; apply AGREE; cbn; rewrite ACTIVE; right; exact MEMBER.
Qed.
Theorem double_tree_active_ranges_agree tree : forall first second,
  double_tree_active_values_agree tree first second -> double_tree_capture_range_facts tree first ->
  double_tree_capture_range_facts tree second.
Proof.
  induction tree; intros first second AGREE FACTS; try exact I.
  - destruct FACTS as [FIRST SECOND]; split; [eapply IHtree1|eapply IHtree2]; try eassumption;
      intros header MEMBER; apply AGREE; cbn; apply in_or_app; [left|right]; exact MEMBER.
  - destruct FACTS as [RANGE CHILD]; cbn [double_tree_capture_range_facts].
    assert (BOUND : double_tree_bound_value second bound=double_tree_bound_value first bound).
    { apply double_tree_bound_value_agree,AGREE; cbn; left; reflexivity. }
    rewrite BOUND; split; [exact RANGE|].
    destruct (Int.signed start <? double_tree_bound_value first bound) eqn:ACTIVE; [|exact I].
    apply IHtree with (first:=first); [|exact CHILD].
    intros header MEMBER; apply AGREE; cbn; rewrite ACTIVE; right; exact MEMBER.
Qed.
Theorem double_tree_active_words_agree tree first second ge locals memory :
  double_tree_active_values_agree tree first second ->
  double_source_tree_header_words ge locals (double_source_tree_active_headers first tree) first memory ->
  double_source_tree_header_words ge locals (double_source_tree_active_headers second tree) second memory.
Proof.
  intros AGREE WORDS header MEMBER; rewrite (double_tree_active_headers_agree AGREE) in MEMBER.
  destruct (WORDS header MEMBER) as [block [BIND LOAD]].
  exists block; split; [exact BIND|rewrite (AGREE header MEMBER); exact LOAD].
Qed.

Print Assumptions double_tree_bound_value_agree.
Print Assumptions double_tree_active_headers_agree.
Print Assumptions double_tree_active_ranges_agree.
Print Assumptions double_tree_active_words_agree.
