From Stdlib Require Import Bool List.
From compcert.common Require Import Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightTempFrame ClightRegionProgress.
From GuardInterface Require Import ClightAdministrative.
Set Implicit Arguments.

(** Administrative normalization is a language service. It changes no
    expressions and preserves exact terminating traces, outcomes and states.
    Labels and switches are kept intact; the region host checks placement and
    progress on the original source, independently of this normalizer. *)
Lemma loop_execution_transport fe ge locals first next target_first target_next
  (FIRST : forall le memory trace after final outcome,
    exec_stmt fe ge locals le memory first trace after final outcome ->
    exec_stmt fe ge locals le memory target_first trace after final outcome)
  (NEXT : forall le memory trace after final outcome,
    exec_stmt fe ge locals le memory next trace after final outcome ->
    exec_stmt fe ge locals le memory target_next trace after final outcome) :
  forall le memory trace after final outcome,
    exec_stmt fe ge locals le memory (Sloop first next) trace after final outcome ->
    exec_stmt fe ge locals le memory (Sloop target_first target_next) trace after final outcome.
Proof.
  intros le memory trace after final outcome RUN.
  remember (Sloop first next) as code eqn:CODE in RUN.
  induction RUN; inversion CODE; subst; clear CODE.
  - eapply exec_Sloop_stop1; [apply FIRST; exact RUN|assumption].
  - eapply exec_Sloop_stop2; [apply FIRST; exact RUN1|assumption|apply NEXT; exact RUN2|assumption].
  - eapply exec_Sloop_loop; [apply FIRST; exact RUN1|assumption|apply NEXT; exact RUN2|].
    apply IHRUN3; auto.
Qed.

Lemma loop_equivalent fe first next target_first target_next :
  stmt_equivalent fe first target_first -> stmt_equivalent fe next target_next ->
  stmt_equivalent fe (Sloop first next) (Sloop target_first target_next).
Proof.
  intros FIRST NEXT ge locals le memory trace after final outcome; split; intro RUN.
  - eapply loop_execution_transport; [| |exact RUN]; intros; [apply (proj1 (FIRST _ _ _ _ _ _ _ _))|apply (proj1 (NEXT _ _ _ _ _ _ _ _))]; assumption.
  - eapply loop_execution_transport; [| |exact RUN]; intros; [apply (proj2 (FIRST _ _ _ _ _ _ _ _))|apply (proj2 (NEXT _ _ _ _ _ _ _ _))]; assumption.
Qed.

Fixpoint trim_loop_skips body := match body with
  | Ssequence first next => join_statements (trim_loop_skips first) (trim_loop_skips next)
  | Sifthenelse test yes no => Sifthenelse test (trim_loop_skips yes) (trim_loop_skips no)
  | Sloop (Ssequence header body) next => Sloop (Ssequence header (trim_loop_skips body)) next
  | _ => body end.

Theorem trim_loop_skips_equivalent fe body : stmt_equivalent fe (trim_loop_skips body) body.
Proof.
  revert body; fix IH 1; intro body; destruct body; unfold stmt_equivalent in *;
    cbn [trim_loop_skips]; try solve [intros; apply iff_refl].
  - intros ge locals le memory trace after final outcome.
    exact (iff_trans (join_statements_equivalent fe _ _ _ _ _ _ _ _ _ _)
      (sequence_equivalent (IH body1) (IH body2) ge locals le memory trace after final outcome)).
  - intros ge locals le memory trace after final outcome; split; intro RUN; inversion RUN; subst.
    + eapply exec_Sifthenelse; [eassumption|eassumption|].
      destruct b; [apply (proj1 (IH body1 _ _ _ _ _ _ _ _))|apply (proj1 (IH body2 _ _ _ _ _ _ _ _))]; assumption.
    + eapply exec_Sifthenelse; [eassumption|eassumption|].
      destruct b; [apply (proj2 (IH body1 _ _ _ _ _ _ _ _))|apply (proj2 (IH body2 _ _ _ _ _ _ _ _))]; assumption.
  - destruct body1; cbn [trim_loop_skips]; try solve [intros; apply iff_refl].
    apply loop_equivalent; [apply sequence_equivalent; [unfold stmt_equivalent; intros; reflexivity|exact (IH body1_2)]|
      unfold stmt_equivalent; intros; reflexivity].
Qed.

Lemma join_statements_quiet first next :
  quiet_statement (join_statements first next) = quiet_statement first && quiet_statement next.
Proof. destruct first; cbn [join_statements quiet_statement]; try reflexivity;
  destruct next; cbn [quiet_statement]; try reflexivity; apply eq_sym, andb_true_r. Qed.

Lemma trim_loop_skips_quiet body : quiet_statement (trim_loop_skips body) = quiet_statement body.
Proof.
  revert body; fix IH 1; intro body; destruct body; cbn [trim_loop_skips quiet_statement]; try reflexivity.
  - rewrite join_statements_quiet,IH,IH; reflexivity.
  - rewrite IH,IH; reflexivity.
  - destruct body1; cbn [trim_loop_skips quiet_statement]; try reflexivity; rewrite IH; reflexivity.
Qed.

Lemma join_statements_writes allowed first next :
  writes_only allowed (join_statements first next) -> writes_only allowed first /\ writes_only allowed next.
Proof.
  destruct first; cbn [join_statements]; try (intro WRITES; split; [constructor|exact WRITES]).
  all: destruct next; intro WRITES; try (split; [exact WRITES|constructor]);
    inversion WRITES; subst; split; assumption.
Qed.
Lemma trim_loop_skips_writes allowed body :
  writes_only allowed (trim_loop_skips body) -> writes_only allowed body.
Proof.
  revert body; fix IH 1; intro body; destruct body; cbn [trim_loop_skips]; intro WRITES; try exact WRITES.
  - apply join_statements_writes in WRITES as [FIRST NEXT]; constructor; apply IH; assumption.
  - inversion WRITES; subst; constructor; apply IH; assumption.
  - destruct body1; cbn [trim_loop_skips] in WRITES; try exact WRITES.
    inversion WRITES; subst; constructor; [|assumption].
    match goal with SEQ : writes_only _ (Ssequence _ _) |- _ => inversion SEQ; subst end.
    constructor; [assumption|apply IH; assumption].
Qed.
Print Assumptions loop_execution_transport.
Print Assumptions loop_equivalent.
Print Assumptions trim_loop_skips_equivalent.
Print Assumptions trim_loop_skips_quiet.
Print Assumptions trim_loop_skips_writes.
