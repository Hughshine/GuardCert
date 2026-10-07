From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightSyntaxEquality ClightTempFrame
  ClightTempFootprint ClightProjectedExecution ClightPureExpr ClightNoWrap.
From GuardInterface Require Import ClightCheckPlanFrame ClightExpressionHeaderCapture
  ClightSignedExpressionProgress.
Import ListNotations.
Set Implicit Arguments.

(** Only exact typed signed tests are changed. Address/value expressions and
    all stores retain their original syntax. A fresh helper is initialized by
    emitted code, rather than assumed defined in the original entry. *)
Definition literal_test_prepare helper upper test := match test with
| Ebinop Olt (Etempvar iterator _) _ _ =>
    if expression_eq test (signed_expression_test iterator(Econst_int upper type_int32s))
    then signed_expression_test iterator(Etempvar helper type_int32s) else test
| _=>test end.
Fixpoint literal_tests_prepare helper upper source := match source with
| Ssequence first next=>Ssequence(literal_tests_prepare helper upper first)(literal_tests_prepare helper upper next)
| Sifthenelse test yes no=>Sifthenelse(literal_test_prepare helper upper test)
    (literal_tests_prepare helper upper yes)(literal_tests_prepare helper upper no)
| Sloop first next=>Sloop(literal_tests_prepare helper upper first)(literal_tests_prepare helper upper next)
| _=>source end.
Definition literal_bound_set helper upper:=Sset helper(Econst_int upper type_int32s).
Definition literal_bound_temps helper upper temps:=PTree.set helper(Vint upper)temps.

Lemma literal_test_prepare_sound helper upper test ge locals temps memory flag :
  temps!helper=Some(Vint upper) ->
  expression_test test(Entry ge locals temps memory)flag ->
  expression_test(literal_test_prepare helper upper test)(Entry ge locals temps memory)flag.
Proof.
  intros WORD RUN; unfold literal_test_prepare.
  destruct test; try exact RUN; destruct b; try exact RUN; destruct test1; try exact RUN.
  destruct(expression_eq _ _)as [SAME|]; [|exact RUN].
  rewrite SAME in RUN.
  destruct(@signed_expression_test_facts ge locals temps memory i(Econst_int upper type_int32s)flag eq_refl RUN)
    as [counter [value [COUNTER [EVAL FLAG]]]].
  apply eval_const_inv in EVAL; injection EVAL as VALUE; subst value flag.
  apply signed_expression_test_eval; [reflexivity|exact COUNTER|constructor; exact WORD].
Qed.

Theorem literal_tests_prepare_execution fe ge locals temps memory source trace after final outcome :
  exec_stmt fe ge locals temps memory source trace after final outcome ->
  forall helper upper written, writes_only written source -> ~In helper written ->
  temps!helper=Some(Vint upper) ->
  exec_stmt fe ge locals temps memory(literal_tests_prepare helper upper source)trace after final outcome.
Proof.
  intro RUN; induction RUN; intros helper upper written WRITES PRIVATE WORD; inversion WRITES; subst;
    cbn [literal_tests_prepare]; try solve[econstructor; eauto].
  - eapply exec_Sseq_1.
    + eapply IHRUN1; eassumption.
    + eapply IHRUN2; [eassumption|exact PRIVATE|].
      rewrite(@writes_only_frame _ _ _ _ _ _ _ _ _ _ RUN1 written ltac:(eassumption)helper PRIVATE); exact WORD.
  - destruct(@literal_test_prepare_sound helper upper a ge e le m b WORD
      ltac:(exists v1; split; eassumption))as [value [TEST BOOL]].
    eapply exec_Sifthenelse; [exact TEST|exact BOOL|].
    destruct b; eapply IHRUN; eassumption.
  - eapply exec_Sloop_stop2.
    + eapply IHRUN1; eassumption.
    + assumption.
    + eapply IHRUN2; [eassumption|exact PRIVATE|].
      rewrite(@writes_only_frame _ _ _ _ _ _ _ _ _ _ RUN1 written ltac:(eassumption)helper PRIVATE); exact WORD.
    + assumption.
  - eapply exec_Sloop_loop.
    + eapply IHRUN1; eassumption.
    + assumption.
    + eapply IHRUN2; [eassumption|exact PRIVATE|].
      rewrite(@writes_only_frame _ _ _ _ _ _ _ _ _ _ RUN1 written ltac:(eassumption)helper PRIVATE); exact WORD.
    + eapply IHRUN3; [constructor; eassumption|exact PRIVATE|].
      rewrite(@writes_only_frame _ _ _ _ _ _ _ _ _ _ RUN2 written ltac:(eassumption)helper PRIVATE),
        (@writes_only_frame _ _ _ _ _ _ _ _ _ _ RUN1 written ltac:(eassumption)helper PRIVATE); exact WORD.
Qed.

Lemma literal_bound_set_execution fe ge locals temps memory helper upper :
  exec_stmt fe ge locals temps memory(literal_bound_set helper upper)E0
    (literal_bound_temps helper upper temps)memory Out_normal.
Proof. constructor; constructor. Qed.
Lemma literal_bound_temps_frame helper upper live temps : ~In helper live ->
  temp_agree live temps(literal_bound_temps helper upper temps).
Proof. intro PRIVATE; apply temp_agree_set; exact PRIVATE. Qed.

(** The transported source starts in the actual prepared state and preserves
    the original memory and public exit. This receipt supplies canonical
    source-definedness; it does not assume any optimization premise. *)
Theorem literal_prepared_source_execution fe ge locals temps memory source trace after final outcome
    live current helper upper :
  check_plan_frameable source=true -> ~In helper(statement_temps source++live) ->
  exec_stmt fe ge locals temps memory source trace after final outcome ->
  temp_agree(statement_temps source++live)temps current ->
  exists exit,
    exec_stmt fe ge locals(literal_bound_temps helper upper current)memory
      (literal_tests_prepare helper upper source)trace exit final outcome /\
    temp_agree live after exit.
Proof.
  intros FRAMEABLE PRIVATE SOURCE FRAME.
  assert(PREPARED:temp_agree(statement_temps source++live)temps(literal_bound_temps helper upper current)).
  { eapply temp_agree_trans; [exact FRAME|apply literal_bound_temps_frame; exact PRIVATE]. }
  destruct(@structured_execution_temp_transport fe ge locals temps memory source trace after final outcome SOURCE
    (statement_temps source++live)(literal_bound_temps helper upper current)(statement_temps source)
    (@check_plan_frameable_writes source FRAMEABLE)
    ltac:(unfold statement_scope; intros id MEMBER; apply in_or_app; left; exact MEMBER)PREPARED)
    as [exit [RAW PUBLIC]].
  exists exit; split.
  - eapply literal_tests_prepare_execution; [exact RAW|apply check_plan_frameable_writes; exact FRAMEABLE| |apply PTree.gss].
    intro MEMBER; apply PRIVATE,in_or_app; left; exact MEMBER.
  - eapply temp_agree_weaken; [|exact PUBLIC]; intros id MEMBER; apply in_or_app; right; exact MEMBER.
Qed.
Print Assumptions literal_test_prepare_sound.
Print Assumptions literal_tests_prepare_execution.
Print Assumptions literal_bound_set_execution.
Print Assumptions literal_bound_temps_frame.
Print Assumptions literal_prepared_source_execution.
