From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightProjectedExecution ClightLoopSyntax.
From GuardInterface Require Import ClightCheckPlan ClightSharedGuard.
Import ListNotations.
Set Implicit Arguments.

(** A checked structured-language fragment for public temporary transport.
    The source/candidate certificates still establish their own memory effect.
    This checker does not accept calls, labels, returns, or switch exits. *)
Fixpoint check_plan_frameable code : bool :=
  match code with
  | Sskip | Sassign _ _ | Sset _ _ | Sbreak | Scontinue => true
  | Ssequence first second | Sifthenelse _ first second | Sloop first second =>
      check_plan_frameable first && check_plan_frameable second
  | _ => false
  end.
Lemma check_plan_frameable_writes code : check_plan_frameable code = true ->
  writes_only (statement_temps code) code.
Proof.
  induction code; cbn [check_plan_frameable statement_temps]; intros CHECK; try discriminate;
    try solve [constructor; cbn; auto].
  all: apply andb_true_iff in CHECK as [FIRST SECOND];
    first [apply writes_sequence|apply writes_if|apply writes_loop].
  all: eapply writes_only_weaken; [|first [apply IHcode1; exact FIRST|apply IHcode2; exact SECOND]].
  all: intros id IN; repeat rewrite in_app_iff; tauto.
Qed.

(** The private result may be undefined initially. It is assigned by the
    plan before dispatch; the branch is transported from the original public
    entry, including loads, stores and its final memory. *)
Theorem check_plan_guarded_normal_execution fe ge locals temps memory plan result live yes no answer after final :
  decision_run (Entry ge locals temps memory) (check_plan_tree plan) answer ->
  check_plan_frameable yes = true -> check_plan_frameable no = true ->
  ~ In result (check_plan_reads plan++statement_temps yes++statement_temps no++live) ->
  exec_stmt fe ge locals temps memory (if answer then yes else no) E0 after final Out_normal ->
  exists exit, exec_stmt fe ge locals temps memory (check_plan_guarded_statement plan result yes no)
    E0 exit final Out_normal /\ temp_agree live after exit.
Proof.
  intros CHECK YES NO FRESH BRANCH.
  pose (chosen := if answer then yes else no).
  assert (FRAMEABLE : check_plan_frameable chosen = true) by (unfold chosen; destruct answer; assumption).
  assert (PRIVATE : ~ In result (statement_temps chosen++live)).
  { unfold chosen; destruct answer; repeat rewrite in_app_iff in *; tauto. }
  destruct (@structured_execution_temp_transport fe ge locals temps memory chosen E0 after final Out_normal BRANCH
    (statement_temps chosen++live) (PTree.set result (Vint (shared_guard_word answer)) temps)
    (statement_temps chosen) (@check_plan_frameable_writes chosen FRAMEABLE)
    ltac:(unfold statement_scope; intros id IN; apply in_or_app; left; exact IN)
    (@temp_agree_set (statement_temps chosen++live) temps result (Vint (shared_guard_word answer)) PRIVATE))
    as [exit [RUN PUBLIC]].
  exists exit; split; [|eapply temp_agree_weaken; [intros id IN; apply in_or_app; right; exact IN|exact PUBLIC]].
  unfold check_plan_guarded_statement; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
  - eapply (@check_plan_code_execution fe (Entry ge locals temps memory) plan answer);
      [apply check_plan_tree_run; exact CHECK|
      intro IN; apply FRESH,in_or_app; left; exact IN|apply temp_agree_refl].
  - destruct (@shared_guard_choice_test ge locals (PTree.set result (Vint (shared_guard_word answer)) temps)
      memory result answer (PTree.gss _ _ _)) as [value [EVAL BOOL]].
    eapply exec_Sifthenelse; [exact EVAL|exact BOOL|exact RUN].
Qed.

Definition check_plan_resources plan result live yes no :=
  check_plan_frameable yes && check_plan_frameable no &&
    (if in_dec peq result (check_plan_reads plan++statement_temps yes++statement_temps no++live)
      then false else true).
Lemma check_plan_resources_sound plan result live yes no : check_plan_resources plan result live yes no = true ->
  check_plan_frameable yes = true /\ check_plan_frameable no = true /\
    ~ In result (check_plan_reads plan++statement_temps yes++statement_temps no++live).
Proof.
  unfold check_plan_resources; rewrite !andb_true_iff.
  destruct (in_dec peq result _); [intros [_ BAD]; discriminate|tauto].
Qed.

Print Assumptions check_plan_frameable_writes.
Print Assumptions check_plan_guarded_normal_execution.
Print Assumptions check_plan_resources_sound.
