From compcert.common Require Import Events Memory.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightFrontendRegion.
From GuardInterface Require Import ClightStrictLoopProgress.
Set Implicit Arguments.

(** A language-side loop facility: replace the body at every actual iteration
    while preserving a local invariant and exact public exits. The body
    transformation and its semantic certificate are supplied by the user. *)
Theorem strict_loop_body_transport fe ge locals iterator condition source_body target_body
  (invariant : temp_env -> mem -> Prop)
  (BODY : forall le m trace after final outcome, invariant le m ->
    exec_stmt fe ge locals le m source_body trace after final outcome ->
    exec_stmt fe ge locals le m target_body trace after final outcome /\ invariant after final)
  (INCREMENT : forall le m trace after final outcome, invariant le m ->
    exec_stmt fe ge locals le m (Ssequence Sskip (counter_increment iterator)) trace after final outcome ->
    invariant after final) :
  forall le m trace after final outcome,
  exec_stmt fe ge locals le m (strict_frontend_loop iterator condition source_body) trace after final outcome ->
  invariant le m ->
  exec_stmt fe ge locals le m (strict_frontend_loop iterator condition target_body) trace after final outcome /\
    invariant after final.
Proof.
  assert (CHECK : forall le m trace after final outcome, invariant le m ->
    exec_stmt fe ge locals le m (Ssequence Sskip (Sifthenelse condition Sskip Sbreak))
      trace after final outcome -> invariant after final).
  { intros le m trace after final outcome INV RUN; apply skip_prefix_exec in RUN; inversion RUN; subst.
    match goal with BRANCH : exec_stmt _ _ _ _ _ (if ?flag then Sskip else Sbreak) _ _ _ _ |- _ =>
      destruct flag; inversion BRANCH; subst; exact INV end. }
  assert (HEADER : forall le m trace after final outcome, invariant le m ->
    exec_stmt fe ge locals le m
      (Ssequence (Ssequence Sskip (Sifthenelse condition Sskip Sbreak)) source_body)
      trace after final outcome ->
    exec_stmt fe ge locals le m
      (Ssequence (Ssequence Sskip (Sifthenelse condition Sskip Sbreak)) target_body)
      trace after final outcome /\ invariant after final).
  { intros le m trace after final outcome INV RUN; inversion RUN; subst.
    - pose proof (@CHECK _ _ _ _ _ _ INV ltac:(eassumption)) as MIDDLE.
      destruct (@BODY _ _ _ _ _ _ MIDDLE ltac:(eassumption)) as [TARGET EXIT].
      split; [eapply exec_Sseq_1; eassumption|exact EXIT].
    - pose proof (@CHECK _ _ _ _ _ _ INV ltac:(eassumption)) as EXIT.
      split; [eapply exec_Sseq_2; eassumption|exact EXIT]. }
  intros le m trace after final outcome RUN.
  remember (strict_frontend_loop iterator condition source_body) as code eqn:CODE in RUN.
  induction RUN; inversion CODE; subst; clear CODE; intro INV.
  - destruct (@HEADER _ _ _ _ _ _ INV RUN) as [TARGET EXIT].
    split; [eapply exec_Sloop_stop1; eassumption|exact EXIT].
  - destruct (@HEADER _ _ _ _ _ _ INV RUN1) as [TARGET MIDDLE].
    pose proof (@INCREMENT _ _ _ _ _ _ MIDDLE RUN2) as EXIT.
    split; [eapply exec_Sloop_stop2; eassumption|exact EXIT].
  - destruct (@HEADER _ _ _ _ _ _ INV RUN1) as [TARGET MIDDLE].
    pose proof (@INCREMENT _ _ _ _ _ _ MIDDLE RUN2) as NEXT.
    destruct (IHRUN3 BODY INCREMENT CHECK HEADER eq_refl NEXT) as [TAIL EXIT].
    split; [eapply exec_Sloop_loop; eassumption|exact EXIT].
Qed.
Print Assumptions strict_loop_body_transport.
