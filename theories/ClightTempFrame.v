From Stdlib Require Import List.
From compcert.lib Require Import Coqlib Maps.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
Import ListNotations.
Set Implicit Arguments.

(** A frame constrains the temporaries read by the surrounding computation.
    Scratch temporaries outside this set may change. *)
Definition temp_agree (live : list ident) (before after : temp_env) :=
  forall id, In id live -> after ! id = before ! id.

Lemma temp_agree_refl live le : temp_agree live le le.
Proof. intros id IN; reflexivity. Qed.
Lemma temp_agree_trans live le0 le1 le2 :
  temp_agree live le0 le1 -> temp_agree live le1 le2 -> temp_agree live le0 le2.
Proof. intros A B id IN; rewrite B, A by exact IN; reflexivity. Qed.
Lemma temp_agree_weaken small big le le' :
  (forall id, In id small -> In id big) -> temp_agree big le le' -> temp_agree small le le'.
Proof. intros SUB FRAME id IN; apply FRAME, SUB; exact IN. Qed.
Lemma temp_agree_set live le id value : ~ In id live -> temp_agree live le (PTree.set id value le).
Proof. intros FRESH key IN; rewrite PTree.gso by congruence; reflexivity. Qed.

(** This certificate is enough for the structured, ordinary-memory code
    emitted by a loop backend. Calls and labels need their own host contract. *)
Inductive writes_only (allowed : list ident) : statement -> Prop :=
| writes_skip : writes_only allowed Sskip
| writes_assign : forall l r, writes_only allowed (Sassign l r)
| writes_set : forall id a, In id allowed -> writes_only allowed (Sset id a)
| writes_sequence : forall a b, writes_only allowed a -> writes_only allowed b ->
    writes_only allowed (Ssequence a b)
| writes_if : forall e a b, writes_only allowed a -> writes_only allowed b ->
    writes_only allowed (Sifthenelse e a b)
| writes_loop : forall a b, writes_only allowed a -> writes_only allowed b ->
    writes_only allowed (Sloop a b)
| writes_break : writes_only allowed Sbreak
| writes_continue : writes_only allowed Scontinue.

Lemma writes_only_frame function_entry ge locals le m code trace le' m' out :
  exec_stmt function_entry ge locals le m code trace le' m' out ->
  forall allowed, writes_only allowed code ->
  forall id, ~ In id allowed -> le' ! id = le ! id.
Proof.
  intro RUN; induction RUN; intros allowed WRITES key FRESH; inversion WRITES; subst;
    try reflexivity.
  - rewrite PTree.gso by (intro EQ; subst; contradiction); reflexivity.
  - erewrite IHRUN2 by eauto; eapply IHRUN1; eauto.
  - eapply IHRUN; eauto.
  - destruct b; eapply IHRUN; eauto.
  - eapply IHRUN; eauto.
  - erewrite IHRUN2 by eauto; eapply IHRUN1; eauto.
  - erewrite IHRUN3 by eauto; erewrite IHRUN2 by eauto; eapply IHRUN1; eauto.
Qed.

Theorem structured_temp_frame function_entry ge locals le m code trace le' m' out allowed live :
  writes_only allowed code ->
  (forall id, In id live -> ~ In id allowed) ->
  exec_stmt function_entry ge locals le m code trace le' m' out -> temp_agree live le le'.
Proof.
  intros WRITES DISJOINT RUN id IN. eapply writes_only_frame; eauto.
Qed.

Print Assumptions structured_temp_frame.
