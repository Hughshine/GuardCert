From Stdlib Require Import List ZArith.
From Guard Require Import AbstractSchedule RectangularSchedule ClightCountedLoop.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section ITERATIONS.
Context {S Instruction : Type} (M : scheduling_model S Instruction).

Lemma schedule_run_append first second before middle after :
  schedule_run M first before middle -> schedule_run M second middle after ->
  schedule_run M (first ++ second) before after.
Proof. intros FIRST SECOND; induction FIRST; cbn; auto; econstructor; eauto. Qed.
Lemma schedule_run_split first : forall second before after,
  schedule_run M (first ++ second) before after ->
  exists middle, schedule_run M first before middle /\ schedule_run M second middle after.
Proof.
  induction first as [|a first IH]; intros second before after RUN; cbn in RUN.
  - exists before; split; [constructor|exact RUN].
  - inversion RUN; subst. match goal with TAIL : schedule_run _ (first ++ second) ?m after |- _ =>
      destruct (IH second m after TAIL) as [middle [LEFT RIGHT]] end.
    exists middle; split; [econstructor; eauto|exact RIGHT].
Qed.

Lemma counted_point_schedule (point : Z -> Instruction) count start before after :
  counted_iterations (fun x => instruction_run M (point x)) count start before after <->
  schedule_run M (map point (zseq start count)) before after.
Proof.
  revert start before after; induction count as [|count IH]; intros start before after; cbn; split; intro RUN.
  - inversion RUN; subst; constructor.
  - inversion RUN; subst; constructor.
  - inversion RUN; subst; econstructor; [eassumption|apply IH; eassumption].
  - inversion RUN; subst; econstructor; [eassumption|apply IH; eassumption].
Qed.

Lemma counted_flat_schedule (points : Z -> list Instruction) count start before after :
  counted_iterations (fun x => schedule_run M (points x)) count start before after <->
  schedule_run M (flat_map points (zseq start count)) before after.
Proof.
  revert start before after; induction count as [|count IH]; intros start before after; cbn; split; intro RUN.
  - inversion RUN; subst; constructor.
  - inversion RUN; subst; constructor.
  - inversion RUN; subst; eapply schedule_run_append; [eassumption|apply IH; eassumption].
  - destruct (@schedule_run_split (points start) (flat_map points (zseq (start + 1) count))
      before after RUN) as [middle [FIRST REST]].
    econstructor; [exact FIRST|apply IH; exact REST].
Qed.
End ITERATIONS.

Definition rectangular_iterations {S : Type} (point : Z -> Z -> S -> S -> Prop) rows columns :=
  counted_iterations (fun i => counted_iterations (point i) columns 0) rows 0.

Lemma counted_iterations_map {S} (p q : Z -> S -> S -> Prop) :
  (forall x before after, p x before after -> q x before after) ->
  forall count start before after, counted_iterations p count start before after ->
    counted_iterations q count start before after.
Proof. intros MAP count start before after RUN; induction RUN; econstructor; eauto. Qed.
Lemma rectangular_iterations_map {S} (p q : Z -> Z -> S -> S -> Prop) :
  (forall i j before after, p i j before after -> q i j before after) ->
  forall rows columns before after, rectangular_iterations p rows columns before after ->
    rectangular_iterations q rows columns before after.
Proof.
  intros MAP rows columns before after RUN; apply counted_iterations_map with
    (p := fun i => counted_iterations (p i) columns 0); [|exact RUN].
  intros i m m' ROW; apply counted_iterations_map with (p := p i); eauto.
Qed.
Lemma rectangular_first {S} (point : Z -> Z -> S -> S -> Prop) rows columns before after :
  rows <> O -> columns <> O -> rectangular_iterations point rows columns before after ->
  exists middle, point 0 0 before middle.
Proof.
  intros R C RUN; destruct rows, columns; try contradiction.
  unfold rectangular_iterations in RUN; inversion RUN; subst; inversion H0; subst; eauto.
Qed.

Lemma rectangular_schedule {S Instruction} (M : scheduling_model S Instruction)
  (point : Z -> Z -> Instruction) rows columns before after :
  rectangular_iterations (fun i j => instruction_run M (point i j)) rows columns before after <->
  schedule_run M (flat_map (fun i => map (point i) (zseq 0 columns)) (zseq 0 rows)) before after.
Proof.
  unfold rectangular_iterations.
  assert (EQUIV : forall count start before after,
    counted_iterations (fun i => counted_iterations (fun j => instruction_run M (point i j)) columns 0)
      count start before after <->
    counted_iterations (fun i => schedule_run M (map (point i) (zseq 0 columns))) count start before after).
  { intros count start s t; split; intro RUN; induction RUN.
    - constructor.
    - econstructor; [apply counted_point_schedule; exact H|exact IHRUN].
    - constructor.
    - econstructor; [apply counted_point_schedule; exact H|exact IHRUN]. }
  rewrite EQUIV; apply counted_flat_schedule.
Qed.

Print Assumptions rectangular_schedule.
