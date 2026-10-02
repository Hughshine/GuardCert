From Stdlib Require Import List.
From compcert.common Require Import Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightFiniteRegion.
Import ListNotations.

(** Frontend-generated sequences contain empty statements and different
    associations. Recognition can flatten them without changing evaluation. *)
Fixpoint flatten_region (s : statement) : list statement :=
  match s with
  | Sskip => []
  | Ssequence l r => flatten_region l ++ flatten_region r
  | _ => [s]
  end.

Lemma tail_execution_app fe ge e l r le m le1 m1 le' m' :
  tail_execution fe ge e l le m le1 m1 ->
  tail_execution fe ge e r le1 m1 le' m' ->
  tail_execution fe ge e (l ++ r) le m le' m'.
Proof. intros LEFT RIGHT; induction LEFT; simpl; auto. econstructor; eauto. Qed.

Lemma flatten_region_execution fe ge e : forall s le m le' m',
  exec_stmt fe ge e le m s E0 le' m' Out_normal ->
  tail_execution fe ge e (flatten_region s) le m le' m'.
Proof.
  induction s; intros le m le' m' RUN;
    try solve [simpl; econstructor; [exact RUN | constructor]].
  - inversion RUN; subst; constructor.
  - inversion RUN; subst; [|contradiction].
    match goal with EMPTY : _ ** _ = E0 |- _ =>
      apply Eapp_E0_inv in EMPTY as [LEFT RIGHT]; subst end.
    simpl; eapply tail_execution_app; eauto.
Qed.

Lemma flattened_pair_execution fe ge e source a b le m le' m' :
  flatten_region source = [a; b] ->
  exec_stmt fe ge e le m source E0 le' m' Out_normal ->
  exec_stmt fe ge e le m (Ssequence a b) E0 le' m' Out_normal.
Proof.
  intros FLAT SOURCE. apply flatten_region_execution in SOURCE. rewrite FLAT in SOURCE.
  inversion SOURCE; subst.
  match goal with SECOND : tail_execution _ _ _ [_] _ _ _ _ |- _ =>
    inversion SECOND; subst end.
  match goal with LAST : tail_execution _ _ _ [] _ _ _ _ |- _ => inversion LAST; subst end.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); eauto.
Qed.

Print Assumptions flatten_region_execution.
