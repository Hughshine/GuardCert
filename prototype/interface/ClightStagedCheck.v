From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightTempFrame ClightTempFootprint ClightProjectedExecution.
From GuardInterface Require Import ClightCheckPlan ClightCheckPlanFrame ClightPrivateScan ClightSharedGuard.
Import ListNotations.
Set Implicit Arguments.

Lemma decision_tree_read_frame tree entry current answer :
  temp_agree (check_plan_reads (tree_check_plan tree)) (entry_temps entry) current ->
  decision_run entry tree answer ->
  decision_run (Entry (entry_ge entry) (entry_env entry) current (entry_memory entry)) tree answer.
Proof.
  revert answer; induction tree; intros answer FRAME RUN; [inversion RUN; subst; constructor|].
  inversion RUN; subst; eapply run_test.
  - match goal with TEST : expression_test _ _ _ |- _ => destruct TEST as [value [EVAL BOOL]] end.
    exists value; split; [|exact BOOL].
    eapply expression_temp_transport with (live:=check_plan_reads (tree_check_plan (Test condition tree1 tree2)));
      [unfold expression_scope,incl; intros id READ; cbn; repeat rewrite in_app_iff; tauto|exact FRAME|exact EVAL].
  - destruct b.
    + apply IHtree1; [|assumption].
      eapply temp_agree_weaken with (big:=check_plan_reads (tree_check_plan (Test condition tree1 tree2)));
        [intros id READ; cbn; repeat rewrite in_app_iff; tauto|exact FRAME].
    + apply IHtree2; [|assumption].
      eapply temp_agree_weaken with (big:=check_plan_reads (tree_check_plan (Test condition tree1 tree2)));
        [intros id READ; cbn; repeat rewrite in_app_iff; tauto|exact FRAME].
Qed.

Lemma check_result_gate_execution fe ge locals temps memory code result choice middle yes no after final outcome :
  exec_stmt fe ge locals temps memory code E0 middle memory Out_normal ->
  middle ! result=Some (Vint (shared_guard_word choice)) ->
  exec_stmt fe ge locals middle memory (if choice then yes else no) E0 after final outcome ->
  exec_stmt fe ge locals temps memory (Ssequence code (Sifthenelse (shared_guard_choice result) yes no))
    E0 after final outcome.
Proof.
  intros CODE FLAG BRANCH; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [exact CODE|].
  destruct (@shared_guard_choice_test ge locals middle memory result choice FLAG) as [value [EVAL BOOL]].
  eapply exec_Sifthenelse; [exact EVAL|exact BOOL|exact BRANCH].
Qed.

Definition staged_check_code before between after result :=
  Ssequence (check_plan_code before result)
    (Sifthenelse (shared_guard_choice result)
      (Ssequence between (Sifthenelse (shared_guard_choice result) (check_plan_code after result) Sskip)) Sskip).
Definition staged_check_guarded before between after result yes no :=
  Ssequence (staged_check_code before between after result) (Sifthenelse (shared_guard_choice result) yes no).
Definition staged_check_spec before between after :=
  decision_bind (decision_bind (check_plan_tree before) between (Decision false)) (check_plan_tree after) (Decision false).

Section EXECUTION.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable entry : clight_entry.
Variables before after : clight_check_plan.
Variable between : statement.
Variable middle_spec : decision_tree.
Variable result : ident.
Variable live : list ident.
Hypothesis PRIVATE : ~ In result live.
Hypothesis BEFORE_FRESH : ~ In result (check_plan_reads before).
Hypothesis AFTER_FRESH : ~ In result (check_plan_reads after).
Hypothesis AFTER_SCOPE : incl (check_plan_reads after) live.
Hypothesis MIDDLE : forall current answer,
  temp_agree live (entry_temps entry) current -> decision_run entry middle_spec answer ->
  exists exit,
    exec_stmt fe (entry_ge entry) (entry_env entry) current (entry_memory entry) between E0 exit (entry_memory entry) Out_normal /\
    temp_agree live current exit /\ exit ! result=Some (Vint (shared_guard_word answer)).

Theorem staged_check_code_execution answer :
  decision_run entry (staged_check_spec before middle_spec after) answer ->
  exists exit,
    exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
      (staged_check_code before between after result) E0 exit (entry_memory entry) Out_normal /\
    temp_agree live (entry_temps entry) exit /\ exit ! result=Some (Vint (shared_guard_word answer)).
Proof.
  intro RUN; unfold staged_check_spec in RUN.
  destruct (@decision_bind_inv (decision_bind (check_plan_tree before) middle_spec (Decision false)) entry
    (check_plan_tree after) (Decision false) answer RUN) as [middle_answer [FIRST TAIL]].
  destruct (@decision_bind_inv (check_plan_tree before) entry middle_spec (Decision false) middle_answer FIRST)
    as [before_answer [HEAD POINT]].
  pose (initialized := PTree.set result (Vint (shared_guard_word before_answer)) (entry_temps entry)).
  assert (BEFORE : exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    (check_plan_code before result) E0 initialized (entry_memory entry) Out_normal).
  { unfold initialized; eapply check_plan_code_execution; [apply check_plan_tree_run; exact HEAD|exact BEFORE_FRESH|apply temp_agree_refl]. }
  assert (INITIAL_FRAME : temp_agree live (entry_temps entry) initialized) by (unfold initialized; apply temp_agree_set; exact PRIVATE).
  assert (INITIAL_FLAG : initialized ! result=Some (Vint (shared_guard_word before_answer))) by (unfold initialized; apply PTree.gss).
  destruct before_answer.
  - cbn in POINT; destruct (@MIDDLE initialized middle_answer INITIAL_FRAME POINT) as [middle [CHECK [FRAME FLAG]]].
    assert (MIDDLE_FRAME : temp_agree live (entry_temps entry) middle) by (eapply temp_agree_trans; eassumption).
    destruct middle_answer.
    + cbn in TAIL.
      pose (exit := PTree.set result (Vint (shared_guard_word answer)) middle).
      assert (AFTER : exec_stmt fe (entry_ge entry) (entry_env entry) middle (entry_memory entry)
        (check_plan_code after result) E0 exit (entry_memory entry) Out_normal).
      { unfold exit; eapply check_plan_code_execution; [apply check_plan_tree_run; exact TAIL|exact AFTER_FRESH|].
        eapply temp_agree_weaken; [exact AFTER_SCOPE|exact MIDDLE_FRAME]. }
      exists exit; split.
      * unfold staged_check_code; eapply check_result_gate_execution with (choice:=true) (middle:=initialized);
          [exact BEFORE|exact INITIAL_FLAG|].
        eapply check_result_gate_execution with (choice:=true) (middle:=middle); [exact CHECK|exact FLAG|exact AFTER].
      * split; [unfold exit; eapply temp_agree_trans; [exact MIDDLE_FRAME|apply temp_agree_set; exact PRIVATE]|unfold exit; apply PTree.gss].
    + cbn in TAIL; inversion TAIL; subst answer.
      exists middle; split; [|split; [exact MIDDLE_FRAME|exact FLAG]].
      unfold staged_check_code; eapply check_result_gate_execution with (choice:=true) (middle:=initialized);
        [exact BEFORE|exact INITIAL_FLAG|].
      eapply check_result_gate_execution with (choice:=false) (middle:=middle); [exact CHECK|exact FLAG|constructor].
  - cbn in POINT; inversion POINT; subst middle_answer; cbn in TAIL; inversion TAIL; subst answer.
    exists initialized; split; [|split; [exact INITIAL_FRAME|exact INITIAL_FLAG]].
    unfold staged_check_code; eapply check_result_gate_execution with (choice:=false) (middle:=initialized);
      [exact BEFORE|exact INITIAL_FLAG|constructor].
Qed.

Theorem staged_check_guarded_execution public yes no answer final_temps final_memory :
  check_plan_frameable yes=true -> check_plan_frameable no=true ->
  incl (statement_temps yes++statement_temps no++public) live ->
  decision_run entry (staged_check_spec before middle_spec after) answer ->
  exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    (if answer then yes else no) E0 final_temps final_memory Out_normal ->
  exists target,
    exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
      (staged_check_guarded before between after result yes no) E0 target final_memory Out_normal /\
    temp_agree public final_temps target.
Proof.
  intros YES NO SCOPE CHECK BRANCH.
  destruct (staged_check_code_execution CHECK) as [middle [CODE [FRAME FLAG]]].
  pose (chosen := if answer then yes else no).
  assert (SUPPORTED : check_plan_frameable chosen=true) by (unfold chosen; destruct answer; assumption).
  assert (CHOSEN_SCOPE : incl (statement_temps chosen++public) live).
  { unfold chosen; destruct answer; intros id MEMBER; apply SCOPE; repeat rewrite in_app_iff in *; tauto. }
  destruct (@structured_execution_temp_transport fe _ _ _ _ chosen _ _ _ _ BRANCH
    (statement_temps chosen++public) middle (statement_temps chosen) (@check_plan_frameable_writes chosen SUPPORTED)
    ltac:(unfold statement_scope,incl; intros id MEMBER; apply in_or_app; auto)
    (@temp_agree_weaken _ live _ _ CHOSEN_SCOPE FRAME)) as [target [ACTUAL PUBLIC]].
  exists target; split.
  - unfold staged_check_guarded; eapply check_result_gate_execution; [exact CODE|exact FLAG|exact ACTUAL].
  - eapply temp_agree_weaken with (big:=statement_temps chosen++public);
      [intros id MEMBER; apply in_or_app; right; exact MEMBER|exact PUBLIC].
Qed.
End EXECUTION.

Print Assumptions decision_tree_read_frame.
Print Assumptions check_result_gate_execution.
Print Assumptions staged_check_code_execution.
Print Assumptions staged_check_guarded_execution.
