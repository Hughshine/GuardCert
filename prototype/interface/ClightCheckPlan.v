From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightTempFrame ClightTempFootprint.
From GuardInterface Require Import ClightSharedGuard.
Import ListNotations.
Set Implicit Arguments.

(** A Clight library representation that retains sequential short circuiting.
    The semantic kernel is unchanged. Flattening is a logical specification;
    the compiler lowers the plan directly and never materializes that tree. *)
Inductive clight_check_plan :=
| PlanDecision (answer : bool)
| PlanTest (expression : expr) (yes no : clight_check_plan)
| PlanAnd (first second : clight_check_plan).

Fixpoint check_plan_tree plan : decision_tree :=
  match plan with
  | PlanDecision answer => Decision answer
  | PlanTest expression yes no => Test expression (check_plan_tree yes) (check_plan_tree no)
  | PlanAnd first second => decision_bind (check_plan_tree first) (check_plan_tree second) (Decision false)
  end.
Fixpoint tree_check_plan tree : clight_check_plan :=
  match tree with
  | Decision answer => PlanDecision answer
  | Test expression yes no => PlanTest expression (tree_check_plan yes) (tree_check_plan no)
  end.
Lemma tree_check_plan_spec tree : check_plan_tree (tree_check_plan tree) = tree.
Proof. induction tree; cbn; congruence. Qed.

Inductive check_plan_run entry : clight_check_plan -> bool -> Prop :=
| plan_run_decision : forall answer, check_plan_run entry (PlanDecision answer) answer
| plan_run_test : forall expression yes no choice answer,
    expression_test expression entry choice ->
    check_plan_run entry (if choice then yes else no) answer ->
    check_plan_run entry (PlanTest expression yes no) answer
| plan_run_and_true : forall first second answer,
    check_plan_run entry first true -> check_plan_run entry second answer ->
    check_plan_run entry (PlanAnd first second) answer
| plan_run_and_false : forall first second,
    check_plan_run entry first false -> check_plan_run entry (PlanAnd first second) false.

Lemma check_plan_run_tree entry plan answer :
  check_plan_run entry plan answer -> decision_run entry (check_plan_tree plan) answer.
Proof.
  intro RUN; induction RUN; cbn [check_plan_tree].
  - constructor.
  - eapply run_test; [exact H|destruct choice; exact IHRUN].
  - eapply decision_bind_run; eassumption.
  - eapply decision_bind_run; [exact IHRUN|constructor].
Qed.
Lemma check_plan_tree_run plan : forall entry answer,
  decision_run entry (check_plan_tree plan) answer -> check_plan_run entry plan answer.
Proof.
  induction plan as [result|expression yes YES no NO|first FIRST second SECOND]; intros entry answer RUN;
    cbn [check_plan_tree] in RUN.
  - inversion RUN; subst; constructor.
  - inversion RUN; subst; eapply plan_run_test; [eassumption|destruct b; [apply YES|apply NO]; assumption].
  - destruct (@decision_bind_inv (check_plan_tree first) entry (check_plan_tree second) (Decision false) answer RUN)
      as [choice [PREFIX LEAF]].
    destruct choice.
    + eapply plan_run_and_true; [apply FIRST; exact PREFIX|apply SECOND; exact LEAF].
    + inversion LEAF; subst; apply plan_run_and_false,FIRST; exact PREFIX.
Qed.
Theorem check_plan_tree_exact entry plan answer :
  check_plan_run entry plan answer <-> decision_run entry (check_plan_tree plan) answer.
Proof. split; [apply check_plan_run_tree|apply check_plan_tree_run]. Qed.

Fixpoint check_plan_reads plan : list ident :=
  match plan with
  | PlanDecision _ => []
  | PlanTest expression yes no => expression_temps expression++check_plan_reads yes++check_plan_reads no
  | PlanAnd first second => check_plan_reads first++check_plan_reads second
  end.

Fixpoint check_plan_code plan result : statement :=
  match plan with
  | PlanDecision answer => Sset result (Econst_int (shared_guard_word answer) type_int32s)
  | PlanTest expression yes no => Sifthenelse expression (check_plan_code yes result) (check_plan_code no result)
  | PlanAnd first second => Ssequence (check_plan_code first result)
      (Sifthenelse (shared_guard_choice result) (check_plan_code second result) Sskip)
  end.
Definition check_plan_guarded_statement plan result yes no :=
  Ssequence (check_plan_code plan result) (Sifthenelse (shared_guard_choice result) yes no).

Lemma check_plan_selected_reads expression yes no (choice : bool) :
  incl (check_plan_reads (if choice then yes else no))
    (check_plan_reads (PlanTest expression yes no)).
Proof. destruct choice; cbn; intros id IN; repeat rewrite in_app_iff; tauto. Qed.

(** No initial value is required for result. Every completed subplan writes it
    before its enclosing PlanAnd or final dispatch reads it. *)
Theorem check_plan_code_execution fe entry plan answer : check_plan_run entry plan answer ->
  forall result current, ~ In result (check_plan_reads plan) ->
  temp_agree (check_plan_reads plan) (entry_temps entry) current ->
  exec_stmt fe (entry_ge entry) (entry_env entry) current (entry_memory entry)
    (check_plan_code plan result) E0 (PTree.set result (Vint (shared_guard_word answer)) current)
    (entry_memory entry) Out_normal.
Proof.
  intro RUN; induction RUN; intros result current FRESH FRAME; cbn [check_plan_code].
  - constructor; constructor.
  - destruct H as [value [EVAL BOOL]].
    eapply exec_Sifthenelse with (v1:=value) (b:=choice).
    + eapply expression_temp_transport with (live:=check_plan_reads (PlanTest expression yes no));
        [unfold expression_scope; intros id IN;
        cbn [check_plan_reads]; repeat rewrite in_app_iff; tauto|exact FRAME|exact EVAL].
    + exact BOOL.
    + destruct choice; apply IHRUN.
      * intro IN; apply FRESH; cbn; repeat rewrite in_app_iff; tauto.
      * eapply temp_agree_weaken; [apply check_plan_selected_reads with (choice:=true)|exact FRAME].
      * intro IN; apply FRESH; cbn; repeat rewrite in_app_iff; tauto.
      * eapply temp_agree_weaken; [apply check_plan_selected_reads with (choice:=false)|exact FRAME].
  - pose proof (IHRUN1 result current ltac:(intro IN; apply FRESH,in_or_app; left; exact IN)
      ltac:(eapply temp_agree_weaken; [intros id IN; apply in_or_app; left; exact IN|exact FRAME])) as FIRST.
    pose proof (IHRUN2 result (PTree.set result (Vint (shared_guard_word true)) current)
      ltac:(intro IN; apply FRESH,in_or_app; right; exact IN)
      ltac:(eapply temp_agree_trans;
        [eapply temp_agree_weaken; [intros id IN; apply in_or_app; right; exact IN|exact FRAME]|
         apply temp_agree_set; intro IN; apply FRESH,in_or_app; right; exact IN])) as SECOND.
    rewrite PTree.set2 in SECOND.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [exact FIRST|].
    destruct (@shared_guard_choice_test (entry_ge entry) (entry_env entry)
      (PTree.set result (Vint (shared_guard_word true)) current) (entry_memory entry) result true (PTree.gss _ _ _))
      as [value [EVAL BOOL]].
    eapply exec_Sifthenelse with (v1:=value) (b:=true); eassumption.
  - pose proof (IHRUN result current ltac:(intro IN; apply FRESH,in_or_app; left; exact IN)
      ltac:(eapply temp_agree_weaken; [intros id IN; apply in_or_app; left; exact IN|exact FRAME])) as FIRST.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [exact FIRST|].
    destruct (@shared_guard_choice_test (entry_ge entry) (entry_env entry)
      (PTree.set result (Vint (shared_guard_word false)) current) (entry_memory entry) result false (PTree.gss _ _ _))
      as [value [EVAL BOOL]].
    eapply exec_Sifthenelse with (v1:=value) (b:=false); [exact EVAL|exact BOOL|constructor].
Qed.

Lemma check_plan_code_writes plan result : writes_only [result] (check_plan_code plan result).
Proof. induction plan; cbn [check_plan_code]; constructor; cbn; auto; constructor; auto; constructor. Qed.

Print Assumptions tree_check_plan_spec.
Print Assumptions check_plan_tree_exact.
Print Assumptions check_plan_code_execution.
Print Assumptions check_plan_code_writes.
