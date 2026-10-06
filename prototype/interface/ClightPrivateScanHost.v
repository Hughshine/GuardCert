From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightTempFootprint.
From Guard Require Import ClightTempFrame.
From GuardInterface Require Import GuardInterface ClightReadonlyRewrite
  ClightPrivateScan ClightPrivateScanSafety ClightSharedGuard.
Set Implicit Arguments.

(** Syntax and result freshness belong to the language adapter. They justify
    dispatch for arbitrary branch statements, independently of a domain or
    of the optimization's conditional preservation proof. *)
Record private_scan_test := PrivateScanTest {
  scan_body : statement;
  scan_result : ident;
  scan_supported : private_scan_statement scan_body;
  scan_result_fresh : ~ In scan_result (statement_temps scan_body)
}.

Definition private_scan_entry_frame ports original checked :=
  entry_ge checked = entry_ge original /\ entry_env checked = entry_env original /\
  entry_memory checked = entry_memory original /\
  temp_agree ports (entry_temps original) (entry_temps checked).

Section HOST.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Context {O : Type} (observe : fragment_observation -> O -> Prop).

Definition private_scan_checks test entry accepted checked :=
  exists after,
    exec_stmt fe (entry_ge entry) (entry_env entry)
      (PTree.set (scan_result test) (Vint Int.zero) (entry_temps entry))
      (entry_memory entry) (scan_body test) E0 after (entry_memory entry)
      (private_scan_outcome accepted) /\
    checked = Entry (entry_ge entry) (entry_env entry)
      (private_scan_checked_temps (scan_result test) accepted after) (entry_memory entry).

Definition private_scan_host : guard_host clight_entry.
Proof.
  refine {| code := statement; check := private_scan_test; observation := O;
    runs := readonly_clight_runs fe observe;
    checks := private_scan_checks;
    check_safe := fun test entry => private_scan_safe fe (entry_ge entry) (entry_env entry)
      (private_scan_prefix (scan_body test) (scan_result test)) (entry_temps entry) (entry_memory entry);
    select := fun test => private_scan_select (scan_body test) (scan_result test) |}.
  intros test yes no entry observed; split.
  - intros [raw [RUN OBSERVE]].
    unfold clight_fragment_run in RUN.
    apply (proj1 (@private_scan_select_exact _ _ _ _ _ _ _ _ _ _ _ _ _
      (scan_supported test) (scan_result_fresh test))) in RUN.
    destruct RUN as [accepted [after [CHECK BRANCH]]].
    exists accepted,(Entry (entry_ge entry) (entry_env entry)
      (private_scan_checked_temps (scan_result test) accepted after) (entry_memory entry)).
    split; [exists after; auto|exists raw; auto].
  - intros [accepted [checked [[after [CHECK SAME]] [raw [RUN OBSERVE]]]]]; subst checked.
    exists raw; split; [|exact OBSERVE].
    unfold clight_fragment_run in *; cbn [entry_ge entry_env entry_temps entry_memory] in RUN.
    apply (proj2 (@private_scan_select_exact _ _ _ _ _ _ _ _ _ _ _ _ _
      (scan_supported test) (scan_result_fresh test))).
    exists accepted,after; auto.
Defined.

Lemma private_scan_checks_prefix test entry accepted checked :
  private_scan_checks test entry accepted checked ->
  exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    (private_scan_prefix (scan_body test) (scan_result test)) E0 (entry_temps checked)
    (entry_memory entry) Out_normal /\
  entry_ge checked = entry_ge entry /\ entry_env checked = entry_env entry /\
  entry_memory checked = entry_memory entry /\
  expression_test (shared_guard_choice (scan_result test)) checked accepted.
Proof.
  intros [after [RUN ->]]; cbn [entry_ge entry_env entry_temps entry_memory].
  split.
  - apply (proj2 (@private_scan_prefix_exact _ _ _ _ _ _ _ _ _ _ _ (scan_supported test))).
    exists accepted,after; repeat split; try reflexivity; exact RUN.
  - repeat split; try reflexivity.
    apply shared_guard_choice_test.
    eapply private_scan_result_value; [apply scan_supported|apply scan_result_fresh|exact RUN].
Qed.

Lemma private_scan_prefix_checks test entry trace after final outcome :
  exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    (private_scan_prefix (scan_body test) (scan_result test)) trace after final outcome ->
  exists accepted checked, private_scan_checks test entry accepted checked /\
    checked = Entry (entry_ge entry) (entry_env entry) after (entry_memory entry).
Proof.
  intro RUN.
  apply (proj1 (@private_scan_prefix_exact _ _ _ _ _ _ _ _ _ _ _ (scan_supported test))) in RUN.
  destruct RUN as [accepted [raw_after [RAW [TRACE [TEMPS [MEMORY OUTCOME]]]]]]; subst.
  exists accepted,(Entry (entry_ge entry) (entry_env entry)
    (private_scan_checked_temps (scan_result test) accepted raw_after) (entry_memory entry)).
  split; [exists raw_after; auto|reflexivity].
Qed.

Theorem private_scan_host_safe_available test entry :
  check_safe private_scan_host test entry ->
  exists accepted checked, checks private_scan_host test entry accepted checked.
Proof.
  intro SAFE.
  destruct (@private_scan_safe_execution fe (entry_ge entry) (entry_env entry)
    (private_scan_prefix (scan_body test) (scan_result test)) (entry_temps entry) (entry_memory entry)
    SAFE (private_scan_prefix_supported (scan_result test) (scan_supported test)))
    as [after [outcome [RUN OUTCOME]]].
  destruct (private_scan_prefix_checks test entry RUN) as [accepted [checked [CHECK _]]].
  exists accepted,checked; exact CHECK.
Qed.
End HOST.

Print Assumptions private_scan_host.
Print Assumptions private_scan_checks_prefix.
Print Assumptions private_scan_prefix_checks.
Print Assumptions private_scan_host_safe_available.
