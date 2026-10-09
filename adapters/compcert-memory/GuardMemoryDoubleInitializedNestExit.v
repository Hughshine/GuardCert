From Stdlib Require Import List ZArith.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values.
From compcert.cfrontend Require Import Clight.
From GuardMemory Require Import GuardMemoryDoubleMatmulNest GuardMemoryLongLoopSettle.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint double_source_set_words (identifiers : list ident) (word : val) (temps : temp_env) :=
  match identifiers with [] => temps | identifier::rest => PTree.set identifier word (double_source_set_words rest word temps) end.
Lemma double_source_set_words_frame identifiers word temps key :
  ~ In key identifiers -> (double_source_set_words identifiers word temps) ! key=temps ! key.
Proof.
  induction identifiers as [|identifier rest IH]; intro FRESH; [reflexivity|].
  cbn [double_source_set_words]; rewrite PTree.gso by (intro SAME; subst; apply FRESH; cbn; auto).
  apply IH; intro MEMBER; apply FRESH; cbn; auto.
Qed.
Lemma double_source_set_words_member identifiers word temps key :
  In key identifiers -> (double_source_set_words identifiers word temps) ! key=Some word.
Proof.
  induction identifiers as [|identifier rest IH]; intro MEMBER; [contradiction|].
  cbn [double_source_set_words]; rewrite PTree.gsspec.
  destruct (peq key identifier); [reflexivity|].
  apply IH; cbn in MEMBER; destruct MEMBER; [congruence|assumption].
Qed.
Lemma double_source_set_words_idempotent identifiers word temps :
  double_source_set_words identifiers word (double_source_set_words identifiers word temps)=
  double_source_set_words identifiers word temps.
Proof.
  apply PTree.extensionality; intro key; destruct (in_dec peq key identifiers) as [MEMBER|FRESH].
  - rewrite !double_source_set_words_member by exact MEMBER; reflexivity.
  - rewrite double_source_set_words_frame by exact FRESH; reflexivity.
Qed.
Lemma double_source_set_words_commute identifiers word temps iterator value :
  ~ In iterator identifiers ->
  double_source_set_words identifiers word (PTree.set iterator value temps)=
  PTree.set iterator value (double_source_set_words identifiers word temps).
Proof.
  induction identifiers as [|identifier rest IH]; intro FRESH; [reflexivity|].
  cbn [double_source_set_words]; rewrite IH by (intro MEMBER; apply FRESH; cbn; auto).
  apply matmul_temp_set_commute; intro SAME; subst; apply FRESH; cbn; auto.
Qed.
Definition double_initialized_nest_exit_ids (outers : list ident) inner count :=
  match count,outers with O,iterator::_ => [iterator] | _,_ => outers++[inner] end.
Definition double_initialized_nest_exit outers inner count temps :=
  double_source_set_words (double_initialized_nest_exit_ids outers inner count)
    (Vlong (Int64.repr (Z.of_nat count))) temps.
Lemma double_initialized_nest_exit_ids_subset outers inner count : forall key,
  In key (double_initialized_nest_exit_ids outers inner count) -> In key (outers++[inner]).
Proof.
  destruct count,outers; cbn [double_initialized_nest_exit_ids app]; intros key MEMBER; try exact MEMBER.
  cbn in MEMBER; destruct MEMBER as [SAME|IMPOSSIBLE]; [subst; cbn; auto|contradiction].
Qed.
Lemma double_initialized_nest_exit_leaf inner count temps :
  double_initialized_nest_exit [] inner count temps=PTree.set inner (Vlong (Int64.repr (Z.of_nat count))) temps.
Proof. destruct count; reflexivity. Qed.
Lemma double_initialized_nest_exit_cons iterator rest inner count temps :
  double_initialized_nest_exit (iterator::rest) inner count temps=
  PTree.set iterator (Vlong (Int64.repr (Z.of_nat count)))
    (match count with O=>temps | S _=>double_initialized_nest_exit rest inner count temps end).
Proof. destruct count; reflexivity. Qed.
Lemma double_initialized_nest_exit_idempotent outers inner count temps :
  double_initialized_nest_exit outers inner count (double_initialized_nest_exit outers inner count temps)=
  double_initialized_nest_exit outers inner count temps.
Proof. apply double_source_set_words_idempotent. Qed.
Lemma double_initialized_nest_exit_frame outers inner count temps key :
  ~ In key (outers++[inner]) -> (double_initialized_nest_exit outers inner count temps) ! key=temps ! key.
Proof.
  intro FRESH; apply double_source_set_words_frame; intro MEMBER; apply FRESH;
    eapply double_initialized_nest_exit_ids_subset; exact MEMBER.
Qed.
Lemma double_initialized_nest_exit_commute outers inner count temps iterator word :
  ~ In iterator (outers++[inner]) ->
  double_initialized_nest_exit outers inner count (PTree.set iterator word temps)=
  PTree.set iterator word (double_initialized_nest_exit outers inner count temps).
Proof.
  intro FRESH; apply double_source_set_words_commute; intro MEMBER; apply FRESH;
    eapply double_initialized_nest_exit_ids_subset; exact MEMBER.
Qed.
Theorem double_initialized_nest_settled_exit iterator rest inner count temps :
  ~ In iterator (rest++[inner]) ->
  memory_long_settled_exit iterator (fun _ => double_initialized_nest_exit rest inner count) count 0
    (PTree.set iterator (Vlong Int64.zero) temps)=double_initialized_nest_exit (iterator::rest) inner count temps.
Proof.
  intro FRESH; destruct count as [|count]; [reflexivity|].
  rewrite (@memory_long_constant_settle_exit iterator (double_initialized_nest_exit rest inner (S count))
    ltac:(intro le; apply double_initialized_nest_exit_idempotent)
    ltac:(intros le word; apply double_initialized_nest_exit_commute; exact FRESH) count 0).
  rewrite Z.add_0_l,double_initialized_nest_exit_commute by exact FRESH.
  rewrite PTree.set2,double_initialized_nest_exit_cons; reflexivity.
Qed.

Print Assumptions double_source_set_words_frame.
Print Assumptions double_source_set_words_idempotent.
Print Assumptions double_initialized_nest_exit_frame.
Print Assumptions double_initialized_nest_exit_commute.
Print Assumptions double_initialized_nest_settled_exit.
