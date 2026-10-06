From Stdlib Require Import Bool List.
From compcert.lib Require Import Maps.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightRegionProgress.
From GuardInterface Require Import ClightPrivateScan ClightQuietDeterminacy.
Set Implicit Arguments.

(** Safety covers the evaluation of each reached primitive and every possible
    completed child execution. The inductive loop rule also provides a finite
    continuation proof; a nonterminating raw loop cannot satisfy this judgment. *)
Inductive private_scan_safe
  (fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop)
  (ge : genv) (locals : env) : statement -> temp_env -> mem -> Prop :=
| scan_safe_skip : forall temps memory, private_scan_safe fe ge locals Sskip temps memory
| scan_safe_set : forall temps memory identifier expression value,
    eval_expr ge locals temps memory expression value ->
    private_scan_safe fe ge locals (Sset identifier expression) temps memory
| scan_safe_break : forall temps memory, private_scan_safe fe ge locals Sbreak temps memory
| scan_safe_sequence : forall first second temps memory,
    private_scan_safe fe ge locals first temps memory ->
    (forall trace after final,
      exec_stmt fe ge locals temps memory first trace after final Out_normal ->
      private_scan_safe fe ge locals second after final) ->
    private_scan_safe fe ge locals (Ssequence first second) temps memory
| scan_safe_if : forall expression yes no temps memory,
    (exists accepted, expression_test expression (Entry ge locals temps memory) accepted) ->
    (forall accepted, expression_test expression (Entry ge locals temps memory) accepted ->
      private_scan_safe fe ge locals (if accepted then yes else no) temps memory) ->
    private_scan_safe fe ge locals (Sifthenelse expression yes no) temps memory
| scan_safe_loop : forall body increment temps memory,
    private_scan_safe fe ge locals body temps memory ->
    (forall trace after final,
      exec_stmt fe ge locals temps memory body trace after final Out_normal ->
      private_scan_safe fe ge locals increment after final) ->
    (forall first_trace first_after first_memory next_trace next_after next_memory,
      exec_stmt fe ge locals temps memory body first_trace first_after first_memory Out_normal ->
      exec_stmt fe ge locals first_after first_memory increment next_trace next_after next_memory Out_normal ->
      private_scan_safe fe ge locals (Sloop body increment) next_after next_memory) ->
    private_scan_safe fe ge locals (Sloop body increment) temps memory.

Lemma scan_expression_test_unique ge locals temps memory expression first second :
  expression_test expression (Entry ge locals temps memory) first ->
  expression_test expression (Entry ge locals temps memory) second -> first = second.
Proof.
  intros [value [FIRST BOOL]] [other [SECOND OTHER_BOOL]].
  pose proof ((proj1 (expressions_determinate ge locals temps memory)) _ _ FIRST _ SECOND) as SAME.
  subst other; congruence.
Qed.

Theorem completed_private_scan_safe fe ge locals temps memory code trace after final outcome :
  exec_stmt fe ge locals temps memory code trace after final outcome ->
  private_scan_statement code -> private_scan_safe fe ge locals code temps memory.
Proof.
  intro RUN; induction RUN; intro SUPPORTED; inversion SUPPORTED; subst;
    try solve [econstructor; eauto].
  - eapply scan_safe_sequence; [apply IHRUN1; assumption|].
    intros other_trace other_after other_memory OTHER.
    destruct (@quiet_execution_determinate _ _ _ _ _ _ _ _ _ _ RUN1
      (ltac:(apply private_scan_quiet; assumption)) _ _ _ _ OTHER) as [_ [TEMPS [MEMORY _]]].
    subst; apply IHRUN2; assumption.
  - eapply scan_safe_sequence; [apply IHRUN; assumption|].
    intros other_trace other_after other_memory OTHER.
    destruct (@quiet_execution_determinate _ _ _ _ _ _ _ _ _ _ RUN
      (ltac:(apply private_scan_quiet; assumption)) _ _ _ _ OTHER) as [_ [_ [_ OUTCOME]]].
    contradiction.
  - apply scan_safe_if.
    + exists b; exists v1; auto.
    + intros accepted TEST.
      assert (SAME : b = accepted).
      { eapply (@scan_expression_test_unique ge e le m a b accepted); [exists v1; split; assumption|exact TEST]. }
      subst accepted; apply IHRUN; destruct b; assumption.
  - eapply scan_safe_loop; [apply IHRUN; assumption| |].
    + intros other_trace other_after other_memory OTHER.
      destruct (@quiet_execution_determinate _ _ _ _ _ _ _ _ _ _ RUN
        (ltac:(apply private_scan_quiet; assumption)) _ _ _ _ OTHER) as [_ [_ [_ OUTCOME]]].
      subst; inversion H; discriminate.
    + intros first_trace first_after first_memory next_trace next_after next_memory FIRST NEXT.
      destruct (@quiet_execution_determinate _ _ _ _ _ _ _ _ _ _ RUN
        (ltac:(apply private_scan_quiet; assumption)) _ _ _ _ FIRST) as [_ [_ [_ OUTCOME]]].
      subst; inversion H; discriminate.
  - eapply scan_safe_loop; [apply IHRUN1; assumption| |].
    + intros other_trace other_after other_memory OTHER.
      destruct (@quiet_execution_determinate _ _ _ _ _ _ _ _ _ _ RUN1
        (ltac:(apply private_scan_quiet; assumption)) _ _ _ _ OTHER) as [_ [TEMPS [MEMORY OUTCOME]]].
      subst; apply IHRUN2; assumption.
    + intros first_trace first_after first_memory next_trace next_after next_memory FIRST NEXT.
      destruct (@quiet_execution_determinate _ _ _ _ _ _ _ _ _ _ RUN1
        (ltac:(apply private_scan_quiet; assumption)) _ _ _ _ FIRST) as [_ [TEMPS [MEMORY OUTCOME]]].
      subst.
      destruct (@quiet_execution_determinate _ _ _ _ _ _ _ _ _ _ RUN2
        (ltac:(apply private_scan_quiet; assumption)) _ _ _ _ NEXT) as [_ [_ [_ OUTCOME]]].
      subst; inversion H0; discriminate.
  - eapply scan_safe_loop; [apply IHRUN1; assumption| |].
    + intros other_trace other_after other_memory OTHER.
      destruct (@quiet_execution_determinate _ _ _ _ _ _ _ _ _ _ RUN1
        (ltac:(apply private_scan_quiet; assumption)) _ _ _ _ OTHER) as [_ [TEMPS [MEMORY OUTCOME]]].
      subst; apply IHRUN2; assumption.
    + intros first_trace first_after first_memory next_trace next_after next_memory FIRST NEXT.
      destruct (@quiet_execution_determinate _ _ _ _ _ _ _ _ _ _ RUN1
        (ltac:(apply private_scan_quiet; assumption)) _ _ _ _ FIRST) as [_ [TEMPS [MEMORY OUTCOME]]].
      subst.
      destruct (@quiet_execution_determinate _ _ _ _ _ _ _ _ _ _ RUN2
        (ltac:(apply private_scan_quiet; assumption)) _ _ _ _ NEXT) as [_ [TEMPS [MEMORY OUTCOME]]].
      subst; apply IHRUN3; exact SUPPORTED.
Qed.

Theorem private_scan_safe_execution fe ge locals code temps memory :
  private_scan_safe fe ge locals code temps memory ->
  private_scan_statement code ->
  exists after outcome,
    exec_stmt fe ge locals temps memory code E0 after memory outcome /\
    (outcome = Out_normal \/ outcome = Out_break).
Proof.
  intro SAFE; induction SAFE; intro SUPPORTED; inversion SUPPORTED; subst.
  - exists temps, Out_normal; split; [constructor|auto].
  - exists (PTree.set identifier value temps), Out_normal; split; [constructor; assumption|auto].
  - exists temps, Out_break; split; [constructor|auto].
  - destruct (IHSAFE ltac:(assumption)) as [after [outcome [FIRST OUTCOME]]].
    destruct OUTCOME as [NORMAL | BREAK]; subst outcome.
    + destruct (H0 E0 after memory FIRST ltac:(assumption)) as [last [outcome [SECOND OUTCOME]]].
      exists last, outcome; split; [eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); eauto|exact OUTCOME].
    + exists after, Out_break; split; [eapply exec_Sseq_2; eauto; discriminate|auto].
  - destruct H as [accepted [value [EVAL BOOL]]].
    destruct (H1 accepted ltac:(exists value; split; assumption)
      ltac:(destruct accepted; assumption)) as [after [outcome [BRANCH OUTCOME]]].
    exists after, outcome; split; [eapply exec_Sifthenelse; eauto|exact OUTCOME].
  - destruct (IHSAFE ltac:(assumption)) as [after [outcome [BODY OUTCOME]]].
    destruct OUTCOME as [NORMAL | BREAK]; subst outcome.
    + destruct (H0 E0 after memory BODY ltac:(assumption)) as [next [outcome [INCREMENT OUTCOME]]].
      destruct OUTCOME as [NORMAL | BREAK]; subst outcome.
      * destruct (H2 E0 after memory E0 next memory BODY INCREMENT SUPPORTED)
          as [last [outcome [REST OUTCOME]]].
        exists last, outcome; split.
        -- eapply exec_Sloop_loop with (t1 := E0) (t2 := E0) (t3 := E0); eauto; constructor.
        -- exact OUTCOME.
      * exists next, Out_normal; split.
        -- eapply exec_Sloop_stop2 with (t1 := E0) (t2 := E0); eauto; constructor.
        -- auto.
    + exists after, Out_normal; split.
      * eapply exec_Sloop_stop1; eauto; constructor.
      * auto.
Qed.

Print Assumptions completed_private_scan_safe.
Print Assumptions private_scan_safe_execution.
