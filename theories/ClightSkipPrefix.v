From Stdlib Require Import List.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightTempFootprint.
Set Implicit Arguments.

(** A language service for administrative frontend steps. It relates actual
    statements, preserving traces, memory, temporaries and every finite exit.
    It makes no progress or divergence claim. *)
Inductive skip_prefix_relation : statement -> statement -> Prop :=
| skip_prefix_same source : skip_prefix_relation source source
| skip_prefix_insert source canonical : skip_prefix_relation source canonical ->
    skip_prefix_relation (Ssequence Sskip source) canonical
| skip_prefix_sequence left right cleft cright :
    skip_prefix_relation left cleft -> skip_prefix_relation right cright ->
    skip_prefix_relation (Ssequence left right) (Ssequence cleft cright)
| skip_prefix_choice condition yes no cyes cno :
    skip_prefix_relation yes cyes -> skip_prefix_relation no cno ->
    skip_prefix_relation (Sifthenelse condition yes no) (Sifthenelse condition cyes cno)
| skip_prefix_loop body latch cbody clatch :
    skip_prefix_relation body cbody -> skip_prefix_relation latch clatch ->
    skip_prefix_relation (Sloop body latch) (Sloop cbody clatch).

Definition statement_execution_equivalent first second :=
  forall fe ge locals entry memory trace after final outcome,
    exec_stmt fe ge locals entry memory first trace after final outcome <->
    exec_stmt fe ge locals entry memory second trace after final outcome.

Lemma prefix_skip_execution source : statement_execution_equivalent (Ssequence Sskip source) source.
Proof.
  intros fe ge locals entry memory trace after final outcome; split; intro RUN.
  - inversion RUN; subst.
    + match goal with SKIP : exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ => inversion SKIP; subst end.
      assumption.
    + match goal with SKIP : exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ => inversion SKIP; subst end.
      contradiction.
  - change trace with (E0 ** trace); eapply exec_Sseq_1; [constructor|exact RUN].
Qed.

Section LOOP_CONGRUENCE.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variables first second target_first target_second : statement.
Hypothesis FIRST : forall entry memory trace after final outcome,
  exec_stmt fe ge locals entry memory first trace after final outcome ->
  exec_stmt fe ge locals entry memory target_first trace after final outcome.
Hypothesis SECOND : forall entry memory trace after final outcome,
  exec_stmt fe ge locals entry memory second trace after final outcome ->
  exec_stmt fe ge locals entry memory target_second trace after final outcome.
Lemma finite_loop_execution_transport entry memory trace after final outcome :
  exec_stmt fe ge locals entry memory (Sloop first second) trace after final outcome ->
  exec_stmt fe ge locals entry memory (Sloop target_first target_second) trace after final outcome.
Proof.
  intro RUN; remember (Sloop first second) as source eqn:SHAPE in RUN.
  induction RUN; inversion SHAPE; subst.
  - eapply exec_Sloop_stop1; eauto.
  - eapply exec_Sloop_stop2; eauto.
  - eapply exec_Sloop_loop; eauto.
Qed.
End LOOP_CONGRUENCE.

Lemma sequence_execution_congruence first second target_first target_second :
  statement_execution_equivalent first target_first -> statement_execution_equivalent second target_second ->
  statement_execution_equivalent (Ssequence first second) (Ssequence target_first target_second).
Proof.
  intros LEFT RIGHT fe ge locals entry memory trace after final outcome; split; intro RUN;
    inversion RUN; subst.
  - eapply exec_Sseq_1; [apply LEFT; eassumption|apply RIGHT; eassumption].
  - eapply exec_Sseq_2; [apply LEFT; eassumption|assumption].
  - eapply exec_Sseq_1; [apply LEFT; eassumption|apply RIGHT; eassumption].
  - eapply exec_Sseq_2; [apply LEFT; eassumption|assumption].
Qed.
Lemma choice_execution_congruence condition yes no target_yes target_no :
  statement_execution_equivalent yes target_yes -> statement_execution_equivalent no target_no ->
  statement_execution_equivalent (Sifthenelse condition yes no) (Sifthenelse condition target_yes target_no).
Proof.
  intros YES NO fe ge locals entry memory trace after final outcome; split; intro RUN;
    inversion RUN; subst; eapply exec_Sifthenelse; [eassumption|eassumption| |eassumption|eassumption|];
    destruct b; [apply YES|apply NO|apply YES|apply NO]; assumption.
Qed.
Lemma loop_execution_congruence first second target_first target_second :
  statement_execution_equivalent first target_first -> statement_execution_equivalent second target_second ->
  statement_execution_equivalent (Sloop first second) (Sloop target_first target_second).
Proof.
  intros FIRST SECOND fe ge locals entry memory trace after final outcome; split; intro RUN.
  - eapply finite_loop_execution_transport; [intros; apply FIRST; eassumption|intros; apply SECOND; eassumption|exact RUN].
  - eapply finite_loop_execution_transport; [intros; apply FIRST; eassumption|intros; apply SECOND; eassumption|exact RUN].
Qed.

Theorem skip_prefix_execution_equivalent actual canonical : skip_prefix_relation actual canonical ->
  statement_execution_equivalent actual canonical.
Proof.
  intro RELATED; induction RELATED.
  - unfold statement_execution_equivalent; intros; reflexivity.
  - intros fe ge locals entry memory trace after final outcome.
    split; intro RUN.
    + apply IHRELATED; apply prefix_skip_execution; exact RUN.
    + apply prefix_skip_execution; apply IHRELATED; exact RUN.
  - apply sequence_execution_congruence; assumption.
  - apply choice_execution_congruence; assumption.
  - apply loop_execution_congruence; assumption.
Qed.
Lemma skip_prefix_temporary_footprint actual canonical : skip_prefix_relation actual canonical ->
  statement_temps actual=statement_temps canonical.
Proof.
  intro RELATED; induction RELATED; cbn [statement_temps].
  - reflexivity.
  - cbn; exact IHRELATED.
  - rewrite IHRELATED1,IHRELATED2; reflexivity.
  - rewrite IHRELATED1,IHRELATED2; reflexivity.
  - rewrite IHRELATED1,IHRELATED2; reflexivity.
Qed.

Print Assumptions skip_prefix_execution_equivalent.
Print Assumptions skip_prefix_temporary_footprint.
