From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightCountedLoop.
From GuardInterface Require Import ClightBoundedCheckLoop ClightCursorSpecialization
  ClightCursorCheckBody ClightCheckPlan ClightPrivateScan ClightPrivateScanSafety ClightSharedGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A language library for a cursor-parametric condition. The caller proves
    that its logical specialization is the desired domain condition. *)
Definition cursor_bounded_scan cursor start ceiling active tree result :=
  bounded_check_prefix cursor start ceiling active (cursor_check_body tree result) result.

Theorem cursor_bounded_scan_execution fe entry cursor result start ceiling active tree live fuel answer :
  cursor <> result -> ~ In cursor live -> ~ In result live ->
  ~ In result (check_plan_reads (tree_check_plan tree)) ->
  (forall identifier, In identifier (expression_temps active) -> identifier <> cursor -> In identifier live) ->
  (forall identifier, In identifier (check_plan_reads (tree_check_plan tree)) -> identifier <> cursor -> In identifier live) ->
  signed_range start -> signed_range ceiling -> ceiling=start+Z.of_nat fuel ->
  decision_run entry (bounded_check_tree (fun index => cursor_expression_at cursor index active)
    (fun index => cursor_tree_at cursor index tree) fuel start) answer ->
  exists after,
    exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
      (cursor_bounded_scan cursor start ceiling active tree result) E0 after (entry_memory entry) Out_normal /\
    temp_agree live (entry_temps entry) after /\ after ! result=Some (Vint (shared_guard_word answer)).
Proof.
  intros DISTINCT CURSOR_PRIVATE RESULT_PRIVATE RESULT_FRESH ACTIVITY_READS POINT_READS START CEILING LENGTH CHECK.
  unfold cursor_bounded_scan; eapply bounded_check_prefix_execution with
    (floor:=start) (active_at:=fun index => cursor_expression_at cursor index active)
    (probe:=fun index => cursor_tree_at cursor index tree).
  - exact DISTINCT.
  - exact CURSOR_PRIVATE.
  - exact CEILING.
  - intros index current choice FLOOR INDEX CURSOR FRAME TEST.
    eapply cursor_expression_test_transport; [exact CURSOR| |exact TEST].
    eapply temp_agree_weaken with (big:=live); [|exact FRAME].
    intros identifier MEMBER; destruct (@cursor_expression_at_reads cursor index active identifier MEMBER) as [READ OTHER].
    apply ACTIVITY_READS; assumption.
  - intros index current choice RANGE INDEX CURSOR FLAG FRAME POINT.
    eapply cursor_check_body_execution; [exact CURSOR| |exact POINT|congruence|exact RESULT_PRIVATE|exact RESULT_FRESH].
    eapply temp_agree_weaken with (big:=live); [|exact FRAME].
    intros identifier MEMBER; destruct (@cursor_tree_at_reads cursor index tree identifier MEMBER) as [READ OTHER].
    apply POINT_READS; assumption.
  - exact RESULT_PRIVATE.
  - exact LENGTH.
  - lia.
  - exact START.
  - exact CHECK.
Qed.

Lemma cursor_bounded_scan_supported cursor start ceiling active tree result :
  private_scan_statement (cursor_bounded_scan cursor start ceiling active tree result).
Proof.
  unfold cursor_bounded_scan; apply bounded_check_prefix_supported,cursor_check_body_supported.
Qed.

Print Assumptions cursor_bounded_scan_execution.
Print Assumptions cursor_bounded_scan_supported.
