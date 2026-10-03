From Stdlib Require Import List ZArith Lia.
From Guard Require Import ClightCountedLoop.
Local Open Scope Z_scope.
Set Implicit Arguments.

Lemma counted_iterations_split {State} (body : Z -> State -> State -> Prop) prefix tail x before after :
  counted_iterations body (prefix + tail) x before after ->
  exists middle, counted_iterations body prefix x before middle /\
    counted_iterations body tail (x + Z.of_nat prefix) middle after.
Proof.
  revert x before; induction prefix as [|prefix IH]; intros x before RUN; cbn in RUN.
  - exists before; split; [apply iterations_done|cbn; rewrite Z.add_0_r; exact RUN].
  - inversion RUN; subst.
    match goal with REST : counted_iterations body (prefix + tail) (x + 1) ?middle after |- _ =>
      destruct (IH (x + 1) middle REST) as [point [FIRST LAST]] end.
    exists point; split; [econstructor; eauto|].
    rewrite Nat2Z.inj_succ; replace (x + Z.succ (Z.of_nat prefix)) with (x + 1 + Z.of_nat prefix) by lia; exact LAST.
Qed.
Lemma counted_iterations_join {State} (body : Z -> State -> State -> Prop) prefix tail x before middle after :
  counted_iterations body prefix x before middle ->
  counted_iterations body tail (x + Z.of_nat prefix) middle after ->
  counted_iterations body (prefix + tail) x before after.
Proof.
  intros FIRST; revert after; induction FIRST; intros after LAST; cbn.
  - cbn in LAST; rewrite Z.add_0_r in LAST; exact LAST.
  - econstructor; [exact H|]. apply IHFIRST.
    rewrite Nat2Z.inj_succ in LAST; replace (x + 1 + Z.of_nat n) with (x + Z.succ (Z.of_nat n)) by lia; exact LAST.
Qed.

Inductive chunked_iterations {State} (body : Z -> State -> State -> Prop) (width : nat) :
  nat -> Z -> State -> State -> Prop :=
| chunks_done : forall x state, chunked_iterations body width 0 x state state
| chunks_next : forall remaining x before middle after,
    remaining <> 0%nat ->
    counted_iterations body (Nat.min width remaining) x before middle ->
    chunked_iterations body width (remaining - Nat.min width remaining) (x + Z.of_nat (Nat.min width remaining)) middle after ->
    chunked_iterations body width remaining x before after.
Theorem counted_iterations_stripmine {State} (body : Z -> State -> State -> Prop) width :
  (0 < width)%nat -> forall count x before after,
  counted_iterations body count x before after -> chunked_iterations body width count x before after.
Proof.
  intros POS; induction count using lt_wf_ind; intros x before after RUN.
  destruct count as [|remaining].
  - inversion RUN; subst; constructor.
  - set (chunk := Nat.min width (S remaining)).
    assert (SMALL : (chunk <= S remaining)%nat) by (unfold chunk; apply Nat.le_min_r).
    assert (NONEMPTY : (0 < chunk)%nat) by (unfold chunk; lia).
    replace (S remaining) with (chunk + (S remaining - chunk))%nat in RUN by lia.
    destruct (@counted_iterations_split State body chunk (S remaining - chunk) x before after RUN) as [middle [FIRST LAST]].
    eapply chunks_next; [lia|exact FIRST|].
    apply H; [lia|exact LAST].
Qed.
Theorem chunked_iterations_preserves_order {State} (body : Z -> State -> State -> Prop) width count x before after :
  chunked_iterations body width count x before after -> counted_iterations body count x before after.
Proof.
  intro RUN; induction RUN; [constructor|].
  assert (BOUND : (Nat.min width remaining <= remaining)%nat) by apply Nat.le_min_r.
  replace remaining with (Nat.min width remaining + (remaining - Nat.min width remaining))%nat by lia.
  eapply counted_iterations_join; eauto.
Qed.
Print Assumptions counted_iterations_stripmine.
Print Assumptions chunked_iterations_preserves_order.
