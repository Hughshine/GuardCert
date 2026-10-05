From Stdlib Require Import List.
From compcert.common Require Import Events Memory.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightFrontendRegion ClightTempFootprint ClightStraightLine.
From GuardInterface Require Import ClightStrictLoopProgress.
Set Implicit Arguments.

(** A local invariant allows replacement of the actual loop test at every
    reached header. This theorem consumes actual body and increment executions. *)
Theorem strict_loop_condition_transport fe ge locals iterator source_test target_test body
  (invariant : temp_env -> mem -> Prop)
  (TEST : forall le m flag, invariant le m ->
    expression_test source_test (Entry ge locals le m) flag ->
    expression_test target_test (Entry ge locals le m) flag)
  (BODY : forall le m trace after final outcome, invariant le m ->
    exec_stmt fe ge locals le m body trace after final outcome -> invariant after final)
  (INCREMENT : forall le m trace after final outcome, invariant le m ->
    exec_stmt fe ge locals le m (Ssequence Sskip (counter_increment iterator)) trace after final outcome ->
    invariant after final) :
  forall le m trace after final outcome,
  exec_stmt fe ge locals le m (strict_frontend_loop iterator source_test body) trace after final outcome ->
  invariant le m ->
  exec_stmt fe ge locals le m (strict_frontend_loop iterator target_test body) trace after final outcome /\
    invariant after final.
Proof.
  assert (CHECK : forall le m trace after final outcome, invariant le m ->
    exec_stmt fe ge locals le m (Ssequence Sskip (Sifthenelse source_test Sskip Sbreak))
      trace after final outcome ->
    exec_stmt fe ge locals le m (Ssequence Sskip (Sifthenelse target_test Sskip Sbreak))
      trace after final outcome /\ invariant after final).
  { intros le m trace after final outcome INV RUN; apply skip_prefix_exec in RUN.
    inversion RUN; subst.
    match goal with H : exec_stmt _ _ _ _ _ (if _ then Sskip else Sbreak) _ _ _ _ |- _ => rename H into BRANCH end.
    assert (SOURCE : expression_test source_test (Entry ge locals le m) b)
      by (eexists; split; eassumption).
    destruct (@TEST le m b INV SOURCE) as [value [EVAL BOOL]].
    destruct b; inversion BRANCH; subst.
    - split; [|exact INV].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [constructor|].
      eapply exec_Sifthenelse with (b := true); [exact EVAL|exact BOOL|constructor].
    - split; [|exact INV].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [constructor|].
      eapply exec_Sifthenelse with (b := false); [exact EVAL|exact BOOL|constructor]. }
  assert (HEADER : forall le m trace after final outcome, invariant le m ->
    exec_stmt fe ge locals le m
      (Ssequence (Ssequence Sskip (Sifthenelse source_test Sskip Sbreak)) body)
      trace after final outcome ->
    exec_stmt fe ge locals le m
      (Ssequence (Ssequence Sskip (Sifthenelse target_test Sskip Sbreak)) body)
      trace after final outcome /\ invariant after final).
  { intros le m trace after final outcome INV RUN; inversion RUN; subst.
    - destruct (@CHECK _ _ _ _ _ _ INV ltac:(eassumption)) as [TARGET MIDDLE].
      split; [eapply exec_Sseq_1; eassumption|eapply BODY; eassumption].
    - destruct (@CHECK _ _ _ _ _ _ INV ltac:(eassumption)) as [TARGET EXIT].
      split; [eapply exec_Sseq_2; eassumption|exact EXIT]. }
  intros le m trace after final outcome RUN.
  remember (strict_frontend_loop iterator source_test body) as code eqn:CODE in RUN.
  induction RUN; inversion CODE; subst; clear CODE; intro INV.
  - destruct (@HEADER _ _ _ _ _ _ INV RUN) as [TARGET EXIT].
    split; [eapply exec_Sloop_stop1; eassumption|exact EXIT].
  - destruct (@HEADER _ _ _ _ _ _ INV RUN1) as [TARGET MIDDLE].
    pose proof (@INCREMENT _ _ _ _ _ _ MIDDLE RUN2) as EXIT.
    split; [eapply exec_Sloop_stop2; eassumption|exact EXIT].
  - destruct (@HEADER _ _ _ _ _ _ INV RUN1) as [TARGET MIDDLE].
    pose proof (@INCREMENT _ _ _ _ _ _ MIDDLE RUN2) as NEXT.
    destruct (IHRUN3 TEST BODY INCREMENT CHECK HEADER eq_refl NEXT) as [TAIL EXIT].
    split; [eapply exec_Sloop_loop; eassumption|exact EXIT].
Qed.
Print Assumptions strict_loop_condition_transport.

Lemma strict_header_execution fe ge locals le m condition body trace after final outcome :
  exec_stmt fe ge locals le m
    (Ssequence (Ssequence Sskip (Sifthenelse condition Sskip Sbreak)) body) trace after final outcome ->
  exists flag, expression_test condition (Entry ge locals le m) flag /\
    if flag then exec_stmt fe ge locals le m body trace after final outcome
    else trace = E0 /\ after = le /\ final = m /\ outcome = Out_break.
Proof.
  intro RUN; inversion RUN; subst.
  all: match goal with PRE : exec_stmt _ _ _ _ _ (Ssequence Sskip _) _ _ _ _ |- _ =>
    apply skip_prefix_exec in PRE; inversion PRE; subst;
    match goal with BRANCH : exec_stmt _ _ _ _ _ (if ?flag then Sskip else Sbreak) _ _ _ _ |- _ =>
      assert (TEST : expression_test condition (Entry ge locals le m) flag)
        by (eexists; split; eassumption);
      destruct flag; inversion BRANCH; subst
    end
  end; cbn in *; try contradiction.
  - exists true; split; [exact TEST|assumption].
  - exists false; split; [exact TEST|repeat split; reflexivity].
Qed.
Print Assumptions strict_header_execution.

Lemma flatten_statement_temps code :
  concat (map statement_temps (flatten_region code)) = statement_temps code.
Proof.
  induction code; cbn [flatten_region map concat]; try rewrite app_nil_r; try reflexivity.
  rewrite map_app, concat_app, IHcode1, IHcode2; reflexivity.
Qed.
Print Assumptions flatten_statement_temps.
