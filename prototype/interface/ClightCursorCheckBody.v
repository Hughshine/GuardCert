From Stdlib Require Import List ZArith.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint.
From GuardInterface Require Import ClightCursorSpecialization ClightCheckPlan ClightPrivateScan ClightSharedGuard.
Import ListNotations.
Set Implicit Arguments.

(** Reuse the existing point condition by specializing a runtime expression
    template in the logical specification. Its actual body writes only result. *)
Definition cursor_check_body tree result := check_plan_code (tree_check_plan tree) result.
Theorem cursor_check_body_execution fe tree entry cursor index current answer result live :
  current ! cursor = Some (Vint (Int.repr index)) ->
  temp_agree (check_plan_reads (tree_check_plan (cursor_tree_at cursor index tree))) (entry_temps entry) current ->
  decision_run entry (cursor_tree_at cursor index tree) answer ->
  result <> cursor -> ~ In result live -> ~ In result (check_plan_reads (tree_check_plan tree)) ->
  exists after,
    exec_stmt fe (entry_ge entry) (entry_env entry) current (entry_memory entry)
      (cursor_check_body tree result) E0 after (entry_memory entry) Out_normal /\
    temp_agree (cursor::live) current after /\ after ! result = Some (Vint (shared_guard_word answer)).
Proof.
  intros CURSOR FRAME CHECK DISTINCT PRIVATE FRESH.
  exists (PTree.set result (Vint (shared_guard_word answer)) current); split.
  - unfold cursor_check_body; eapply (@check_plan_code_execution fe
      (Entry (entry_ge entry) (entry_env entry) current (entry_memory entry)) (tree_check_plan tree) answer).
    + apply check_plan_tree_run; rewrite tree_check_plan_spec.
      eapply cursor_tree_run_transport; [exact CURSOR|exact FRAME|exact CHECK].
    + exact FRESH.
    + apply temp_agree_refl.
  - split; [apply temp_agree_set; cbn; intros [SAME|MEMBER]; [congruence|contradiction]|apply PTree.gss].
Qed.

Lemma cursor_check_body_supported tree result : private_scan_statement (cursor_check_body tree result).
Proof.
  unfold cursor_check_body; induction tree; cbn [tree_check_plan check_plan_code];
    [constructor|constructor; assumption].
Qed.

Print Assumptions cursor_check_body_execution.
Print Assumptions cursor_check_body_supported.
