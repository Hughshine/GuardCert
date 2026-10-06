From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events Smallstep.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightTempFrame ClightTempFootprint ClightPureExpr
  ClightLoopSyntax ClightRegionProgress.
From GuardInterface Require Import ClightSharedGuard.
Import ListNotations.
Set Implicit Arguments.

(** A scan may read memory and update temporaries. Its completed executions
    retain memory and leave through normal completion or a rejecting break. *)
Inductive private_scan_statement : statement -> Prop :=
| scan_skip : private_scan_statement Sskip
| scan_set : forall identifier expression, private_scan_statement (Sset identifier expression)
| scan_break : private_scan_statement Sbreak
| scan_sequence : forall first second,
    private_scan_statement first -> private_scan_statement second ->
    private_scan_statement (Ssequence first second)
| scan_if : forall expression yes no,
    private_scan_statement yes -> private_scan_statement no ->
    private_scan_statement (Sifthenelse expression yes no)
| scan_loop : forall body increment,
    private_scan_statement body -> private_scan_statement increment ->
    private_scan_statement (Sloop body increment).

Lemma private_scan_quiet code : private_scan_statement code -> quiet_statement code = true.
Proof.
  intro SUPPORTED; induction SUPPORTED; cbn [quiet_statement]; try reflexivity;
    rewrite IHSUPPORTED1, IHSUPPORTED2; reflexivity.
Qed.

Lemma private_scan_tree tree yes no :
  private_scan_statement yes -> private_scan_statement no ->
  private_scan_statement (tree_statement tree yes no).
Proof.
  intros YES NO; induction tree as [accepted|atom left LEFT right RIGHT]; cbn [tree_statement].
  - destruct accepted; assumption.
  - constructor; assumption.
Qed.

Lemma private_scan_write_bound code :
  private_scan_statement code -> writes_only (statement_temps code) code.
Proof.
  intro SUPPORTED; induction SUPPORTED; cbn [statement_temps]; try solve [constructor; cbn; auto].
  - constructor.
    + eapply writes_only_weaken; [intros id IN; apply in_or_app; left; exact IN|exact IHSUPPORTED1].
    + eapply writes_only_weaken; [intros id IN; apply in_or_app; right; exact IN|exact IHSUPPORTED2].
  - constructor.
    + eapply writes_only_weaken; [intros id IN; apply in_or_app; right; apply in_or_app; left; exact IN|exact IHSUPPORTED1].
    + eapply writes_only_weaken; [intros id IN; apply in_or_app; right; apply in_or_app; right; exact IN|exact IHSUPPORTED2].
  - constructor.
    + eapply writes_only_weaken; [intros id IN; apply in_or_app; left; exact IN|exact IHSUPPORTED1].
    + eapply writes_only_weaken; [intros id IN; apply in_or_app; right; exact IN|exact IHSUPPORTED2].
Qed.

Theorem private_scan_completed_shape fe ge locals temps memory code trace after final outcome :
  exec_stmt fe ge locals temps memory code trace after final outcome ->
  private_scan_statement code ->
  trace = E0 /\ final = memory /\ (outcome = Out_normal \/ outcome = Out_break).
Proof.
  intro RUN; induction RUN; intro SUPPORTED; inversion SUPPORTED; subst;
    try solve [repeat split; auto].
  - destruct (IHRUN1 ltac:(assumption)) as [TRACE1 [MEMORY1 _]].
    destruct (IHRUN2 ltac:(assumption)) as [TRACE2 [MEMORY2 OUTCOME]].
    subst; auto.
  - apply IHRUN; assumption.
  - apply IHRUN; destruct b; assumption.
  - destruct (IHRUN ltac:(assumption)) as [TRACE [MEMORY OUTCOME]].
    split; [exact TRACE|split; [exact MEMORY|]].
    destruct OUTCOME as [NORMAL|BREAK]; subst;
      match goal with REL : out_break_or_return _ _ |- _ => inversion REL; auto end.
  - destruct (IHRUN1 ltac:(assumption)) as [TRACE1 [MEMORY1 _]].
    destruct (IHRUN2 ltac:(assumption)) as [TRACE2 [MEMORY2 OUTCOME]].
    subst; split; [reflexivity|split; [reflexivity|]].
    destruct OUTCOME as [NORMAL|BREAK]; subst;
      match goal with REL : out_break_or_return _ _ |- _ => inversion REL; auto end.
  - destruct (IHRUN1 ltac:(assumption)) as [TRACE1 [MEMORY1 _]].
    destruct (IHRUN2 ltac:(assumption)) as [TRACE2 [MEMORY2 _]].
    destruct (IHRUN3 SUPPORTED) as [TRACE3 [MEMORY3 OUTCOME]].
    subst; auto.
Qed.

(** The one-shot loop encloses the check only. Candidate and fallback remain
    outside it, so their break, continue and return outcomes are not absorbed. *)
Definition private_scan_finish result :=
  Ssequence (Sset result (Econst_int Int.one type_int32s)) Sbreak.
Definition private_scan_prefix raw result :=
  Ssequence (Sset result (Econst_int Int.zero type_int32s))
    (Sloop (Ssequence raw (private_scan_finish result)) Sbreak).
Definition private_scan_select raw result yes no :=
  Ssequence (private_scan_prefix raw result)
    (Sifthenelse (shared_guard_choice result) yes no).
Definition private_scan_checked_temps result (accepted : bool) (after : temp_env) :=
  if accepted then PTree.set result (Vint Int.one) after else after.

Definition private_scan_outcome (accepted : bool) := if accepted then Out_normal else Out_break.

Lemma private_scan_prefix_supported raw result :
  private_scan_statement raw -> private_scan_statement (private_scan_prefix raw result).
Proof.
  intro SUPPORTED; unfold private_scan_prefix, private_scan_finish.
  auto 8 using scan_sequence, scan_set, scan_loop, scan_break.
Qed.

Lemma private_scan_finish_exact fe ge locals temps memory result trace after final outcome :
  exec_stmt fe ge locals temps memory (private_scan_finish result) trace after final outcome <->
  trace = E0 /\ after = PTree.set result (Vint Int.one) temps /\ final = memory /\ outcome = Out_break.
Proof.
  split.
  - intro RUN; unfold private_scan_finish in RUN; inversion RUN; subst.
    + match goal with SET : exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _ => inversion SET; subst end.
      match goal with EVAL : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ => apply scalar_const_inv in EVAL; subst end.
      match goal with BREAK : exec_stmt _ _ _ _ _ Sbreak _ _ _ _ |- _ => inversion BREAK; subst end.
      repeat split; reflexivity.
    + match goal with SET : exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _ => inversion SET; subst end.
      contradiction.
  - intros [-> [-> [-> ->]]]; unfold private_scan_finish.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); constructor; constructor.
Qed.

Lemma private_scan_body_exact fe ge locals temps memory raw result trace after final outcome :
  private_scan_statement raw ->
  (exec_stmt fe ge locals temps memory (Ssequence raw (private_scan_finish result)) trace after final outcome <->
   exists accepted checked,
     exec_stmt fe ge locals temps memory raw E0 checked memory (private_scan_outcome accepted) /\
     trace = E0 /\ after = private_scan_checked_temps result accepted checked /\ final = memory /\ outcome = Out_break).
Proof.
  intro SUPPORTED; split.
  - intro RUN; inversion RUN; subst.
    + match goal with RAW : exec_stmt _ _ _ _ _ raw _ _ _ _ |- _ =>
        destruct (@private_scan_completed_shape _ _ _ _ _ _ _ _ _ _ RAW SUPPORTED)
          as [TRACE [MEMORY OUTCOME]]; subst end.
      match goal with FINISH : exec_stmt _ _ _ _ _ (private_scan_finish _) _ _ _ _ |- _ =>
        apply private_scan_finish_exact in FINISH as [-> [-> [-> ->]]] end.
      eexists true,_; repeat split; try reflexivity; eassumption.
    + match goal with RAW : exec_stmt _ _ _ _ _ raw _ _ _ _ |- _ =>
        destruct (@private_scan_completed_shape _ _ _ _ _ _ _ _ _ _ RAW SUPPORTED)
          as [TRACE [MEMORY [NORMAL|BREAK]]]; subst; [contradiction|] end.
      eexists false,_; repeat split; try reflexivity; eassumption.
  - intros [accepted [checked [RAW [-> [-> [-> ->]]]]]]; destruct accepted.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact RAW|].
      apply private_scan_finish_exact; repeat split; reflexivity.
    + eapply exec_Sseq_2; [exact RAW|discriminate].
Qed.

Lemma private_scan_loop_exact fe ge locals temps memory raw result trace after final outcome :
  private_scan_statement raw ->
  (exec_stmt fe ge locals temps memory (Sloop (Ssequence raw (private_scan_finish result)) Sbreak)
     trace after final outcome <->
   exists accepted checked,
     exec_stmt fe ge locals temps memory raw E0 checked memory (private_scan_outcome accepted) /\
     trace = E0 /\ after = private_scan_checked_temps result accepted checked /\ final = memory /\ outcome = Out_normal).
Proof.
  intro SUPPORTED; split.
  - intro RUN; inversion RUN; subst.
    all: match goal with SUPPORT : private_scan_statement ?body,
      BODY : exec_stmt _ _ _ _ _ (Ssequence ?body (private_scan_finish _)) _ _ _ _ |- _ =>
      apply (proj1 (@private_scan_body_exact _ _ _ _ _ _ _ _ _ _ _ SUPPORT)) in BODY;
      destruct BODY as [accepted [checked [RAW [TRACE [AFTER [MEMORY OUTCOME]]]]]]; subst end.
    + match goal with REL : out_break_or_return Out_break _ |- _ => inversion REL; subst end.
      exists accepted,checked; repeat split; try reflexivity; exact RAW.
    + match goal with REL : out_normal_or_continue Out_break |- _ => inversion REL end.
    + match goal with REL : out_normal_or_continue Out_break |- _ => inversion REL end.
  - intros [accepted [checked [RAW [-> [-> [-> ->]]]]]].
    eapply exec_Sloop_stop1 with (out' := Out_break).
    + apply (proj2 (@private_scan_body_exact _ _ _ _ _ _ _ _ _ _ _ SUPPORTED)).
      exists accepted,checked; repeat split; try reflexivity; exact RAW.
    + constructor.
Qed.

Theorem private_scan_prefix_exact fe ge locals temps memory raw result trace after final outcome :
  private_scan_statement raw ->
  (exec_stmt fe ge locals temps memory (private_scan_prefix raw result) trace after final outcome <->
   exists accepted checked,
     exec_stmt fe ge locals (PTree.set result (Vint Int.zero) temps) memory raw E0 checked memory
       (private_scan_outcome accepted) /\
     trace = E0 /\ after = private_scan_checked_temps result accepted checked /\ final = memory /\ outcome = Out_normal).
Proof.
  intro SUPPORTED; split.
  - intro RUN; unfold private_scan_prefix in RUN; inversion RUN; subst.
    + match goal with SET : exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _ => inversion SET; subst end.
      match goal with EVAL : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ => apply scalar_const_inv in EVAL; subst end.
      match goal with LOOP : exec_stmt _ _ _ _ _ (Sloop _ _) _ _ _ _ |- _ =>
        apply (proj1 (@private_scan_loop_exact _ _ _ _ _ _ _ _ _ _ _ SUPPORTED)) in LOOP;
        destruct LOOP as [accepted [checked [RAW [-> [-> [-> ->]]]]]] end.
      exists accepted,checked; repeat split; try reflexivity; exact RAW.
    + match goal with SET : exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _ => inversion SET; subst end.
      contradiction.
  - intros [accepted [checked [RAW [-> [-> [-> ->]]]]]].
    unfold private_scan_prefix; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + constructor; constructor.
    + apply (proj2 (@private_scan_loop_exact _ _ _ _ _ _ _ _ _ _ _ SUPPORTED)).
      exists accepted,checked; repeat split; try reflexivity; exact RAW.
Qed.

Lemma private_scan_result_value fe ge locals temps memory raw result accepted checked :
  private_scan_statement raw -> ~ In result (statement_temps raw) ->
  exec_stmt fe ge locals (PTree.set result (Vint Int.zero) temps) memory raw E0 checked memory
    (private_scan_outcome accepted) ->
  (private_scan_checked_temps result accepted checked) ! result = Some (Vint (shared_guard_word accepted)).
Proof.
  intros SUPPORTED FRESH RUN; destruct accepted; cbn [private_scan_checked_temps shared_guard_word].
  - apply PTree.gss.
  - rewrite (@writes_only_frame _ _ _ _ _ _ _ _ _ _ RUN _ (private_scan_write_bound SUPPORTED) _ FRESH).
    apply PTree.gss.
Qed.

Theorem private_scan_select_exact fe ge locals temps memory raw result yes no trace after final outcome :
  private_scan_statement raw -> ~ In result (statement_temps raw) ->
  (exec_stmt fe ge locals temps memory (private_scan_select raw result yes no) trace after final outcome <->
   exists accepted checked,
     exec_stmt fe ge locals (PTree.set result (Vint Int.zero) temps) memory raw E0 checked memory
       (private_scan_outcome accepted) /\
     exec_stmt fe ge locals (private_scan_checked_temps result accepted checked) memory
       (if accepted then yes else no) trace after final outcome).
Proof.
  intros SUPPORTED FRESH; split.
  - intro RUN; unfold private_scan_select in RUN; inversion RUN; subst.
    + match goal with PREFIX : exec_stmt _ _ _ _ _ (private_scan_prefix _ _) _ _ _ _ |- _ =>
        apply (proj1 (@private_scan_prefix_exact _ _ _ _ _ _ _ _ _ _ _ SUPPORTED)) in PREFIX;
        destruct PREFIX as [accepted [checked [RAW [TRACE [TEMPS [MEMORY OUTCOME]]]]]]; subst end.
      match goal with BRANCH : exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ |- _ =>
        inversion BRANCH; subst end.
      match goal with EVAL : eval_expr _ _ _ _ (shared_guard_choice _) _ |- _ =>
        unfold shared_guard_choice in EVAL; apply scalar_temp_inv in EVAL;
        rewrite (@private_scan_result_value fe ge locals temps memory raw result accepted checked SUPPORTED FRESH RAW)
          in EVAL; inversion EVAL; subst end.
      match goal with BOOL : bool_val (Vint (shared_guard_word accepted)) _ _ = Some ?choice |- _ =>
        assert (SAME : choice = accepted) by
          (destruct accepted; [change (Some true = Some choice) in BOOL|change (Some false = Some choice) in BOOL]; congruence);
        subst choice end.
      exists accepted,checked; split; [exact RAW|assumption].
    + match goal with PREFIX : exec_stmt _ _ _ _ _ (private_scan_prefix _ _) _ _ _ _ |- _ =>
        apply (proj1 (@private_scan_prefix_exact _ _ _ _ _ _ _ _ _ _ _ SUPPORTED)) in PREFIX;
        destruct PREFIX as [accepted [checked [RAW [TRACE [TEMPS [MEMORY OUTCOME]]]]]]; subst end.
      contradiction.
  - intros [accepted [checked [RAW BRANCH]]].
    unfold private_scan_select; eapply exec_Sseq_1 with (t1 := E0) (t2 := trace).
    + apply (proj2 (@private_scan_prefix_exact _ _ _ _ _ _ _ _ _ _ _ SUPPORTED)).
      exists accepted,checked; repeat split; try reflexivity; exact RAW.
    + destruct (@shared_guard_choice_test ge locals
        (private_scan_checked_temps result accepted checked) memory result accepted
        (@private_scan_result_value fe ge locals temps memory raw result accepted checked SUPPORTED FRESH RAW))
      as [value [EVAL BOOL]].
      eapply exec_Sifthenelse; eassumption.
Qed.

Theorem private_scan_prefix_dispatch temps (program : Clight.program) fn outside locals original memory
  raw result yes no checked accepted :
  exec_stmt (adapter_entry temps) (Clight.globalenv program) locals original memory
    (private_scan_prefix raw result) E0 checked memory Out_normal ->
  expression_test (shared_guard_choice result) (Entry (Clight.globalenv program) locals checked memory) accepted ->
  star (adapter_step temps) (Clight.globalenv program)
    (State fn (private_scan_select raw result yes no) outside locals original memory) E0
    (State fn (if accepted then yes else no) outside locals checked memory).
Proof.
  intros PREFIX [value [EVAL BOOL]].
  destruct (exec_stmt_steps (adapter_entry temps) program _ _ _ _ _ _ _ _ PREFIX fn
    (Kseq (Sifthenelse (shared_guard_choice result) yes no) outside)) as [next [STEPS EXIT]].
  inversion EXIT; subst next; unfold private_scan_select.
  eapply star_step; [unfold adapter_step; apply step_seq| |reflexivity].
  eapply star_trans; [exact STEPS| |reflexivity].
  eapply star_step; [unfold adapter_step; apply step_skip_seq| |reflexivity].
  apply star_one; unfold adapter_step; eapply step_ifthenelse; eassumption.
Qed.

Print Assumptions private_scan_completed_shape.
Print Assumptions private_scan_prefix_exact.
Print Assumptions private_scan_select_exact.
Print Assumptions private_scan_prefix_dispatch.
