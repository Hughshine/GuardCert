From compcert.common Require Import Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightCountedProtocol ClightFrontendRegion ClightLoopSyntax ClightRegionProgress.
From GuardInterface Require Import ClightStrictLoopProgress ClightStableLoopCondition
  ClightQuietDeterminacy ClightReadonlyLoadedTreeSynthesis.
Set Implicit Arguments.

Lemma strict_increment_execution_exact fe ge locals iterator le memory trace after final outcome :
  strict_counter_active iterator le ->
  exec_stmt fe ge locals le memory (Ssequence Sskip (counter_increment iterator)) trace after final outcome ->
  trace = E0 /\ after = increment_temps iterator le /\ final = memory /\ outcome = Out_normal.
Proof.
  intros ACTIVE RUN; apply skip_prefix_exec in RUN.
  eapply quiet_execution_determinate; [exact RUN|reflexivity|].
  apply strict_increment_normal; exact ACTIVE.
Qed.

(** Source execution supplies the next real body before any load-stability
    assumption. An active header and finite normal body are enough. *)
Theorem strict_active_iteration fe ge locals iterator condition body le memory after final :
  normal_statement body = true -> quiet_statement body = true ->
  expression_test condition (Entry ge locals le memory) true ->
  exec_stmt fe ge locals le memory (strict_frontend_loop iterator condition body) E0 after final Out_normal ->
  exists body_temps body_memory next_temps next_memory,
    exec_stmt fe ge locals le memory body E0 body_temps body_memory Out_normal /\
    exec_stmt fe ge locals body_temps body_memory (Ssequence Sskip (counter_increment iterator))
      E0 next_temps next_memory Out_normal /\
    exec_stmt fe ge locals next_temps next_memory (strict_frontend_loop iterator condition body) E0 after final Out_normal.
Proof.
  intros NORMAL QUIET ACTIVE SOURCE.
  assert (HEADER : forall trace middle mem outcome,
    exec_stmt fe ge locals le memory
      (Ssequence (Ssequence Sskip (Sifthenelse condition Sskip Sbreak)) body) trace middle mem outcome ->
    exec_stmt fe ge locals le memory body trace middle mem outcome).
  { intros trace middle mem outcome RUN; destruct (strict_header_execution RUN) as [flag [TEST LEAF]].
    assert (SAME : flag = true) by (eapply readonly_test_determinate; [exact TEST|exact ACTIVE]); subst flag; exact LEAF. }
  inversion SOURCE; subst.
  - match goal with RUN : exec_stmt _ _ _ _ _ (Ssequence (Ssequence Sskip (Sifthenelse condition _ _)) body) _ _ _ _ |- _ =>
      pose proof (HEADER _ _ _ _ RUN) as BODY_RUN end.
    pose proof (@normal_statement_execution fe ge locals body NORMAL _ _ _ _ _ _ BODY_RUN) as OUTCOME.
    subst; match goal with BAD : out_break_or_return Out_normal _ |- _ => inversion BAD end.
  - match goal with INC : exec_stmt _ _ _ _ _ (Ssequence Sskip (counter_increment iterator)) _ _ _ _ |- _ =>
      rename INC into INCREMENT_RUN end.
    pose proof (@normal_statement_execution fe ge locals (Ssequence Sskip (counter_increment iterator))
      ltac:(reflexivity) _ _ _ _ _ _ INCREMENT_RUN) as OUTCOME.
    subst; match goal with BAD : out_break_or_return Out_normal _ |- _ => inversion BAD end.
  - match goal with RUN : exec_stmt _ _ _ _ _ (Ssequence (Ssequence Sskip (Sifthenelse condition _ _)) body) _ _ _ _ |- _ =>
      pose proof (HEADER _ _ _ _ RUN) as BODY_RUN end.
    pose proof (@normal_statement_execution fe ge locals body NORMAL _ _ _ _ _ _ BODY_RUN) as OUTCOME.
    pose proof (@quiet_execution_silent fe ge locals _ _ body _ _ _ _ BODY_RUN QUIET) as SILENT; subst.
    match goal with INC : exec_stmt _ _ _ _ _ (Ssequence Sskip (counter_increment iterator)) _ _ _ _ |- _ =>
      pose proof (@quiet_execution_silent fe ge locals _ _ _ _ _ _ _ INC ltac:(reflexivity)) as INC_SILENT end.
    subst; cbn in *; subst.
    do 4 eexists; split; [exact BODY_RUN|split; eassumption].
Qed.
Print Assumptions strict_active_iteration.
Print Assumptions strict_increment_execution_exact.
