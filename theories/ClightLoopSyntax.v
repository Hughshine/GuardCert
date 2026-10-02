From Stdlib Require Import List Bool.
From compcert.common Require Import Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightRegionProgress ClightLoopExecution ClightStraightLine ClightTempFrame.
Import ListNotations.
Set Implicit Arguments.

(** A checked normal-exit property. A loop may contain break/continue, but
    quietness excludes returns and external calls. Its terminating exit is
    therefore normal. The enclosing compiler retains the original fallback. *)
Fixpoint normal_statement code :=
  match code with
  | Sskip | Sassign _ _ | Sset _ _ => true
  | Ssequence first second | Sifthenelse _ first second =>
      normal_statement first && normal_statement second
  | Sloop first second => quiet_statement (Sloop first second)
  | _ => false end.

Lemma normal_statement_execution fe ge locals code :
  normal_statement code = true -> forall le m trace le' m' outcome,
  exec_stmt fe ge locals le m code trace le' m' outcome -> outcome = Out_normal.
Proof.
  induction code; cbn [normal_statement]; try discriminate;
    intros CHECK le m trace le' m' outcome RUN; try solve [inversion RUN; reflexivity].
  - apply andb_true_iff in CHECK as [FIRST SECOND]; inversion RUN; subst.
    + eapply IHcode2; eauto.
    + match goal with FIRST_RUN : exec_stmt _ _ _ _ _ code1 _ _ _ _ |- _ =>
        pose proof (IHcode1 FIRST _ _ _ _ _ _ FIRST_RUN); subst end; contradiction.
  - apply andb_true_iff in CHECK as [FIRST SECOND]; inversion RUN; subst.
    destruct b; [eapply IHcode1|eapply IHcode2]; eauto.
  - eapply quiet_loop_normal; eauto.
Qed.

Lemma flatten_normal_certificate code :
  Forall (fun atom => normal_statement atom = true) (flatten_region code) ->
  normal_statement code = true.
Proof.
  induction code; cbn [flatten_region normal_statement]; intro CHECK;
    try solve [inversion CHECK; assumption]; try reflexivity.
  apply Forall_app in CHECK as [FIRST SECOND]; rewrite IHcode1, IHcode2 by assumption; reflexivity.
Qed.

Lemma flatten_writes_certificate allowed code :
  Forall (writes_only allowed) (flatten_region code) -> writes_only allowed code.
Proof.
  induction code; cbn [flatten_region]; intro CHECK;
    try solve [inversion CHECK; assumption].
  - constructor.
  - apply Forall_app in CHECK as [FIRST SECOND]; constructor; auto.
Qed.

Lemma flatten_quiet_certificate code :
  Forall (fun atom => quiet_statement atom = true) (flatten_region code) -> quiet_statement code = true.
Proof.
  induction code; cbn [flatten_region quiet_statement]; intro CHECK;
    try solve [inversion CHECK; assumption]; try reflexivity.
  apply Forall_app in CHECK as [FIRST SECOND]; rewrite IHcode1, IHcode2 by assumption; reflexivity.
Qed.

Lemma writes_only_weaken small big code :
  (forall id, In id small -> In id big) -> writes_only small code -> writes_only big code.
Proof. intros SUB WRITES; induction WRITES; constructor; auto. Qed.

Lemma flattened_singleton_execution fe ge locals source atom le m le' m' :
  flatten_region source = [atom] ->
  exec_stmt fe ge locals le m source E0 le' m' Out_normal ->
  exec_stmt fe ge locals le m atom E0 le' m' Out_normal.
Proof.
  intros FLAT RUN; apply flatten_region_execution in RUN; rewrite FLAT in RUN.
  inversion RUN; subst.
  match goal with LAST : ClightFiniteRegion.tail_execution _ _ _ [] _ _ _ _ |- _ => inversion LAST; subst end.
  assumption.
Qed.

Lemma sequence_normal_decode fe ge locals le m first second le' m' :
  exec_stmt fe ge locals le m (Ssequence first second) E0 le' m' Out_normal ->
  exists middle memory, exec_stmt fe ge locals le m first E0 middle memory Out_normal /\
    exec_stmt fe ge locals middle memory second E0 le' m' Out_normal.
Proof.
  intro RUN; inversion RUN; subst; [|contradiction].
  match goal with EMPTY : _ ** _ = E0 |- _ => apply Eapp_E0_inv in EMPTY as [LEFT RIGHT]; subst end.
  do 2 eexists; split; eassumption.
Qed.

Print Assumptions normal_statement_execution.
