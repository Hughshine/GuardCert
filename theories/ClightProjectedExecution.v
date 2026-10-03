From Stdlib Require Import List.
From compcert.lib Require Import Coqlib Maps.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightTempFrame ClightTempFootprint.
Set Implicit Arguments.

Local Hint Resolve scope_append_left scope_append_right scope_cons_tail scope_cons_head
  temp_agree_set_both expression_temp_transport lvalue_temp_transport : core.
Local Hint Unfold expression_scope statement_scope : core.

Lemma structured_execution_temp_transport fe ge locals le memory code trace le' memory' outcome :
  exec_stmt fe ge locals le memory code trace le' memory' outcome ->
  forall live target allowed, writes_only allowed code -> statement_scope live code ->
  temp_agree live le target -> exists target',
    exec_stmt fe ge locals target memory code trace target' memory' outcome /\
    temp_agree live le' target'.
Proof.
  intro RUN; induction RUN; intros live target allowed WRITES SCOPE AGREE; inversion WRITES; subst;
    unfold statement_scope in SCOPE; cbn [statement_temps] in SCOPE;
    try solve [eexists; split; [econstructor; eauto 6|eauto]].
  - destruct (IHRUN1 live target allowed ltac:(eassumption) ltac:(eauto) AGREE) as [target1 [FIRST EQ1]].
    destruct (IHRUN2 live target1 allowed ltac:(eassumption) ltac:(eauto) EQ1) as [target2 [SECOND EQ2]].
    exists target2; split; [econstructor; eauto|exact EQ2].
  - destruct (IHRUN live target allowed ltac:(eassumption) ltac:(eauto) AGREE) as [target1 [FIRST EQ1]].
    exists target1; split; [econstructor; eauto|exact EQ1].
  - assert (SELECTED : writes_only allowed (if b then s1 else s2)) by (destruct b; assumption).
    assert (SELECTED_SCOPE : statement_scope live (if b then s1 else s2))
      by (destruct b; unfold statement_scope; eauto).
    destruct (IHRUN live target allowed SELECTED SELECTED_SCOPE AGREE) as [target1 [FIRST EQ1]].
    exists target1; split; [econstructor; eauto|exact EQ1].
  - destruct (IHRUN live target allowed ltac:(eassumption) ltac:(eauto) AGREE) as [target1 [FIRST EQ1]].
    exists target1; split; [econstructor; eauto|exact EQ1].
  - destruct (IHRUN1 live target allowed ltac:(eassumption) ltac:(eauto) AGREE) as [target1 [FIRST EQ1]].
    destruct (IHRUN2 live target1 allowed ltac:(eassumption) ltac:(eauto) EQ1) as [target2 [SECOND EQ2]].
    exists target2; split; [eapply exec_Sloop_stop2; eauto|exact EQ2].
  - destruct (IHRUN1 live target allowed ltac:(eassumption) ltac:(eauto) AGREE) as [target1 [FIRST EQ1]].
    destruct (IHRUN2 live target1 allowed ltac:(eassumption) ltac:(eauto) EQ1) as [target2 [SECOND EQ2]].
    destruct (IHRUN3 live target2 allowed ltac:(constructor; eassumption)
      ltac:(unfold statement_scope; exact SCOPE) EQ2) as [target3 [THIRD EQ3]].
    exists target3; split; [eapply exec_Sloop_loop; eauto|exact EQ3].
Qed.
Print Assumptions structured_execution_temp_transport.

Lemma temp_agree_sym live before after : temp_agree live before after -> temp_agree live after before.
Proof. intros EQ id IN; symmetry; apply EQ; exact IN. Qed.
Definition temp_except live iterator := filter (fun id => negb (Pos.eqb id iterator)) live.
Lemma temp_except_member live iterator id : In id (temp_except live iterator) <-> In id live /\ id <> iterator.
Proof. unfold temp_except; rewrite filter_In, negb_true_iff, Pos.eqb_neq; reflexivity. Qed.
Lemma temp_except_iterator live iterator : ~ In iterator (temp_except live iterator).
Proof. rewrite temp_except_member; tauto. Qed.
Lemma temp_except_private live iterator id : ~ In id live -> ~ In id (temp_except live iterator).
Proof. rewrite temp_except_member; tauto. Qed.
Lemma canonical_temp_agreement live iterator base le value :
  le ! iterator = Some value -> temp_agree (temp_except live iterator) base le ->
  temp_agree live (PTree.set iterator value base) le.
Proof.
  intros ITER FRAME id IN; rewrite PTree.gsspec; destruct (peq id iterator) as [SAME|DIFFERENT].
  - subst id; exact ITER.
  - apply FRAME, temp_except_member; auto.
Qed.
