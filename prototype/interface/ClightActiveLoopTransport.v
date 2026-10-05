From compcert.common Require Import Events Memory.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightFrontendRegion ClightLoopSyntax.
From GuardInterface Require Import ClightStrictLoopProgress ClightStableLoopCondition.
Set Implicit Arguments.

(** The body certificate receives the actual active source header. A language
    instance can restrict its address reasoning to reached iteration points. *)
Theorem strict_active_loop_transport fe ge locals iterator source_test target_test source_body target_body
  (invariant body_invariant : temp_env -> mem -> Prop)
  (TEST : forall le m flag, invariant le m ->
    expression_test source_test (Entry ge locals le m) flag ->
    expression_test target_test (Entry ge locals le m) flag)
  (BODY : forall le m trace after final outcome, invariant le m ->
    expression_test source_test (Entry ge locals le m) true ->
    exec_stmt fe ge locals le m source_body trace after final outcome ->
    exec_stmt fe ge locals le m target_body trace after final outcome /\ body_invariant after final)
  (WEAKEN : forall le m, body_invariant le m -> invariant le m)
  (INCREMENT : forall le m trace after final outcome, body_invariant le m ->
    exec_stmt fe ge locals le m (Ssequence Sskip (counter_increment iterator)) trace after final outcome ->
    invariant after final) :
  forall le m trace after final outcome,
  exec_stmt fe ge locals le m (strict_frontend_loop iterator source_test source_body) trace after final outcome ->
  invariant le m ->
  exec_stmt fe ge locals le m (strict_frontend_loop iterator target_test target_body) trace after final outcome /\
    invariant after final.
Proof.
  assert (HEADER : forall le m trace after final outcome, invariant le m ->
    exec_stmt fe ge locals le m
      (Ssequence (Ssequence Sskip (Sifthenelse source_test Sskip Sbreak)) source_body)
      trace after final outcome ->
    exec_stmt fe ge locals le m
      (Ssequence (Ssequence Sskip (Sifthenelse target_test Sskip Sbreak)) target_body)
      trace after final outcome /\ invariant after final /\
      (out_normal_or_continue outcome -> body_invariant after final)).
  { intros le m trace after final outcome INV RUN.
    destruct (strict_header_execution RUN) as [flag [CHECK LEAF]].
    destruct (@TEST le m flag INV CHECK) as [value [EVAL BOOL]].
    destruct flag.
    - destruct (@BODY le m trace after final outcome INV CHECK LEAF) as [TARGET EXIT].
      split; [|split; [apply WEAKEN; exact EXIT|intros _; exact EXIT]].
      replace trace with (E0 ** trace) by reflexivity; eapply exec_Sseq_1; [|exact TARGET].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [constructor|].
      eapply exec_Sifthenelse; [exact EVAL|exact BOOL|constructor].
    - destruct LEAF as [TRACE [TEMPS [MEMORY OUTCOME]]]; subst.
      split; [|split; [exact INV|intro BAD; inversion BAD]].
      eapply exec_Sseq_2 with (out := Out_break); [|discriminate].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [constructor|].
      eapply exec_Sifthenelse; [exact EVAL|exact BOOL|constructor]. }
  intros le m trace after final outcome RUN.
  remember (strict_frontend_loop iterator source_test source_body) as code eqn:CODE in RUN.
  induction RUN; inversion CODE; subst; clear CODE; intro INV.
  - destruct (@HEADER _ _ _ _ _ _ INV RUN) as [TARGET [EXIT _]].
    split; [eapply exec_Sloop_stop1; eassumption|exact EXIT].
  - destruct (@HEADER _ _ _ _ _ _ INV RUN1) as [TARGET [_ READY]].
    assert (MIDDLE : body_invariant le1 m1) by (apply READY; assumption).
    pose proof (@INCREMENT _ _ _ _ _ _ MIDDLE RUN2) as EXIT.
    split; [eapply exec_Sloop_stop2; eassumption|exact EXIT].
  - destruct (@HEADER _ _ _ _ _ _ INV RUN1) as [TARGET [_ READY]].
    assert (MIDDLE : body_invariant le1 m1) by (apply READY; assumption).
    pose proof (@INCREMENT _ _ _ _ _ _ MIDDLE RUN2) as NEXT.
    destruct (IHRUN3 TEST BODY INCREMENT HEADER eq_refl NEXT) as [TAIL EXIT].
    split; [eapply exec_Sloop_loop; eassumption|exact EXIT].
Qed.
Print Assumptions strict_active_loop_transport.
