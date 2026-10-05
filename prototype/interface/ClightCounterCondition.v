From compcert.common Require Import Events Memory.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightFrontendRegion.
From GuardInterface Require Import ClightStrictLoopProgress ClightStableLoopCondition ClightCounterProgress.
Set Implicit Arguments.

(** The body certificate receives an actually true source header. This
    separates the header invariant from the stronger pre-increment invariant,
    so finite-footprint assumptions need only cover active iterations. *)
Theorem generic_active_condition_transport fe ge locals iterator increment_expression source_test target_test body
  (header_invariant step_invariant : temp_env -> mem -> Prop)
  (TEST : forall le m flag, header_invariant le m ->
    expression_test source_test (Entry ge locals le m) flag ->
    expression_test target_test (Entry ge locals le m) flag)
  (BODY : forall le m trace after final outcome, header_invariant le m ->
    expression_test source_test (Entry ge locals le m) true ->
    exec_stmt fe ge locals le m body trace after final outcome -> step_invariant after final)
  (WEAKEN : forall le m, step_invariant le m -> header_invariant le m)
  (INCREMENT : forall le m trace after final outcome, step_invariant le m ->
    exec_stmt fe ge locals le m (Ssequence Sskip (Sset iterator increment_expression)) trace after final outcome ->
    header_invariant after final) :
  forall le m trace after final outcome,
  exec_stmt fe ge locals le m (generic_frontend_loop iterator increment_expression source_test body) trace after final outcome ->
  header_invariant le m ->
  exec_stmt fe ge locals le m (generic_frontend_loop iterator increment_expression target_test body) trace after final outcome /\
    header_invariant after final.
Proof.
  assert (HEADER : forall le m trace after final outcome, header_invariant le m ->
    exec_stmt fe ge locals le m
      (Ssequence (Ssequence Sskip (Sifthenelse source_test Sskip Sbreak)) body)
      trace after final outcome ->
    exec_stmt fe ge locals le m
      (Ssequence (Ssequence Sskip (Sifthenelse target_test Sskip Sbreak)) body)
      trace after final outcome /\ header_invariant after final /\
      (out_normal_or_continue outcome -> step_invariant after final)).
  { intros le m trace after final outcome INV RUN.
    destruct (strict_header_execution RUN) as [flag [SOURCE BRANCH]].
    destruct (@TEST le m flag INV SOURCE) as [value [EVAL BOOL]].
    destruct flag; cbn in BRANCH.
    - pose proof (@BODY _ _ _ _ _ _ INV SOURCE BRANCH) as STEP.
      split; [|split; [apply WEAKEN; exact STEP|intros; exact STEP]].
      replace trace with (E0 ** trace) by reflexivity; eapply exec_Sseq_1; [|exact BRANCH].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [constructor|].
      eapply exec_Sifthenelse with (b := true); [exact EVAL|exact BOOL|constructor].
    - destruct BRANCH as [TRACE [TEMPS [MEMORY OUTCOME]]]; subst.
      split; [|split; [exact INV|intro BAD; inversion BAD]].
      eapply exec_Sseq_2; [|discriminate].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [constructor|].
      eapply exec_Sifthenelse with (b := false); [exact EVAL|exact BOOL|constructor]. }
  intros le m trace after final outcome RUN.
  remember (generic_frontend_loop iterator increment_expression source_test body) as code eqn:CODE in RUN.
  induction RUN; inversion CODE; subst; clear CODE; intro INV.
  - destruct (@HEADER _ _ _ _ _ _ INV RUN) as [TARGET [EXIT _]].
    split; [eapply exec_Sloop_stop1; eassumption|exact EXIT].
  - destruct (@HEADER _ _ _ _ _ _ INV RUN1) as [TARGET [MIDDLE STEP]].
    assert (BEFORE_INCREMENT : step_invariant le1 m1) by (apply STEP; assumption).
    pose proof (@INCREMENT _ _ _ _ _ _ BEFORE_INCREMENT RUN2) as EXIT.
    split; [eapply exec_Sloop_stop2; eassumption|exact EXIT].
  - destruct (@HEADER _ _ _ _ _ _ INV RUN1) as [TARGET [MIDDLE STEP]].
    assert (BEFORE_INCREMENT : step_invariant le1 m1) by (apply STEP; assumption).
    pose proof (@INCREMENT _ _ _ _ _ _ BEFORE_INCREMENT RUN2) as NEXT.
    destruct (IHRUN3 TEST BODY INCREMENT HEADER eq_refl NEXT) as [TAIL EXIT].
    split; [eapply exec_Sloop_loop; eassumption|exact EXIT].
Qed.
Print Assumptions generic_active_condition_transport.
