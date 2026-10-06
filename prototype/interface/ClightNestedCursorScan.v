From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightCountedLoop ClightTempFrame ClightTempFootprint.
From GuardInterface Require Import ClightBoundedCheckLoop ClightCursorSpecialization ClightCursorCheckBody
  ClightCursorBoundedScan ClightCheckPlan ClightPrivateScan ClightSharedGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma cursor_expression_at_commute outer inner i j expression : outer <> inner ->
  cursor_expression_at outer i (cursor_expression_at inner j expression) =
  cursor_expression_at inner j (cursor_expression_at outer i expression).
Proof.
  intro DISTINCT; induction expression; cbn [cursor_expression_at]; try reflexivity;
    try (rewrite IHexpression; reflexivity); try (rewrite IHexpression1,IHexpression2; reflexivity).
  destruct (peq i0 inner); destruct (peq i0 outer); cbn [cursor_expression_at];
    try congruence; repeat match goal with |- context[peq ?x ?y] => destruct (peq x y) end; congruence.
Qed.

Lemma cursor_tree_at_commute outer inner i j tree : outer <> inner ->
  cursor_tree_at outer i (cursor_tree_at inner j tree) = cursor_tree_at inner j (cursor_tree_at outer i tree).
Proof.
  intro DISTINCT; induction tree; cbn [cursor_tree_at]; [reflexivity|].
  rewrite cursor_expression_at_commute by exact DISTINCT; rewrite IHtree1,IHtree2; reflexivity.
Qed.

Lemma cursor_tree_at_bounded_check cursor index active probe fuel start :
  cursor_tree_at cursor index (bounded_check_tree active probe fuel start) =
  bounded_check_tree (fun j => cursor_expression_at cursor index (active j))
    (fun j => cursor_tree_at cursor index (probe j)) fuel start.
Proof.
  revert start; induction fuel; intro start; cbn [bounded_check_tree cursor_tree_at];
    [reflexivity|rewrite cursor_tree_at_bind,IHfuel; reflexivity].
Qed.

Lemma check_tree_bind_read_scope tree : forall yes no live,
  incl (check_plan_reads (tree_check_plan tree)) live ->
  incl (check_plan_reads (tree_check_plan yes)) live ->
  incl (check_plan_reads (tree_check_plan no)) live ->
  incl (check_plan_reads (tree_check_plan (decision_bind tree yes no))) live.
Proof.
  induction tree as [accepted|condition first IHfirst second IHsecond];
    intros yes no live TREE YES NO; cbn [decision_bind]; [destruct accepted; assumption|].
  cbn [tree_check_plan check_plan_reads] in TREE |- *.
  intros id MEMBER; repeat rewrite in_app_iff in MEMBER; destruct MEMBER as [MEMBER|[MEMBER|MEMBER]].
  - apply TREE; cbn; repeat rewrite in_app_iff; tauto.
  - apply (IHfirst yes no live); [|exact YES|exact NO|exact MEMBER].
    intros key READ; apply TREE; repeat rewrite in_app_iff; tauto.
  - apply (IHsecond yes no live); [|exact YES|exact NO|exact MEMBER].
    intros key READ; apply TREE; repeat rewrite in_app_iff; tauto.
Qed.

Lemma bounded_check_tree_read_scope active probe fuel start live :
  (forall j, incl (expression_temps (active j)) live) ->
  (forall j, incl (check_plan_reads (tree_check_plan (probe j))) live) ->
  incl (check_plan_reads (tree_check_plan (bounded_check_tree active probe fuel start))) live.
Proof.
  intros ACTIVE POINT; revert start; induction fuel; intro start; cbn [bounded_check_tree tree_check_plan check_plan_reads].
  - intros id MEMBER; contradiction.
  - intros id MEMBER; repeat rewrite in_app_iff in MEMBER; destruct MEMBER as [MEMBER|[MEMBER|MEMBER]];
      [apply (ACTIVE start); exact MEMBER| |contradiction].
    exact (@check_tree_bind_read_scope (probe start) (bounded_check_tree active probe fuel (start+1))
      (Decision false) live (POINT start) (IHfuel (start+1)) ltac:(cbn; intros key READ; contradiction) id MEMBER).
Qed.

Definition nested_cursor_inner_spec outer inner index active probe fuel :=
  cursor_tree_at outer index (bounded_check_tree (fun j => cursor_expression_at inner j active)
    (fun j => cursor_tree_at inner j probe) fuel 0).
Definition nested_cursor_scan_spec outer inner active outer_active probe outer_fuel inner_fuel :=
  bounded_check_tree (fun i => cursor_expression_at outer i outer_active)
    (fun i => nested_cursor_inner_spec outer inner i active probe inner_fuel) outer_fuel 0.
Definition nested_cursor_scan outer inner result outer_ceiling inner_ceiling outer_active active probe :=
  bounded_check_prefix outer 0 outer_ceiling outer_active
    (cursor_bounded_scan inner 0 inner_ceiling active probe result) result.

Section EXECUTION.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable entry : clight_entry.
Variables outer inner result : ident.
Variables outer_fuel inner_fuel : nat.
Variables outer_active active : expr.
Variable probe : decision_tree.
Variable live : list ident.
Hypothesis OUTER_INNER : outer <> inner.
Hypothesis OUTER_RESULT : outer <> result.
Hypothesis INNER_RESULT : inner <> result.
Hypothesis OUTER_PRIVATE : ~ In outer live.
Hypothesis INNER_PRIVATE : ~ In inner live.
Hypothesis RESULT_PRIVATE : ~ In result live.
Hypothesis RESULT_FRESH : ~ In result (check_plan_reads (tree_check_plan probe)).
Hypothesis OUTER_READS : forall id, In id (expression_temps outer_active) -> id <> outer -> In id live.
Hypothesis INNER_READS : forall id, In id (expression_temps active) -> id <> inner -> In id (outer::live).
Hypothesis POINT_READS : forall id, In id (check_plan_reads (tree_check_plan probe)) -> id <> inner -> In id (outer::live).
Hypothesis OUTER_RANGE : signed_range (Z.of_nat outer_fuel).
Hypothesis INNER_RANGE : signed_range (Z.of_nat inner_fuel).

Lemma nested_cursor_inner_public index :
  incl (check_plan_reads (tree_check_plan (nested_cursor_inner_spec outer inner index active probe inner_fuel))) live.
Proof.
  unfold nested_cursor_inner_spec; rewrite cursor_tree_at_bounded_check; apply bounded_check_tree_read_scope.
  - intros j id READ.
    destruct (@cursor_expression_at_reads outer index (cursor_expression_at inner j active) id READ) as [INNER OTHER].
    destruct (@cursor_expression_at_reads inner j active id INNER) as [ORIGINAL DIFFERENT].
    destruct (@INNER_READS id ORIGINAL DIFFERENT) as [SAME|MEMBER]; [congruence|exact MEMBER].
  - intros j id READ.
    destruct (@cursor_tree_at_reads outer index (cursor_tree_at inner j probe) id READ) as [INNER OTHER].
    destruct (@cursor_tree_at_reads inner j probe id INNER) as [ORIGINAL DIFFERENT].
    destruct (@POINT_READS id ORIGINAL DIFFERENT) as [SAME|MEMBER]; [congruence|exact MEMBER].
Qed.

Lemma nested_cursor_inner_execution index current answer :
  current ! outer=Some (Vint (Int.repr index)) -> temp_agree live (entry_temps entry) current ->
  decision_run entry (nested_cursor_inner_spec outer inner index active probe inner_fuel) answer ->
  exists after,
    exec_stmt fe (entry_ge entry) (entry_env entry) current (entry_memory entry)
      (cursor_bounded_scan inner 0 (Z.of_nat inner_fuel) active probe result) E0 after (entry_memory entry) Out_normal /\
    temp_agree (outer::live) current after /\ after ! result=Some (Vint (shared_guard_word answer)).
Proof.
  intros CURSOR FRAME CHECK.
  assert (LOGICAL : decision_run (Entry (entry_ge entry) (entry_env entry) current (entry_memory entry))
    (bounded_check_tree (fun j => cursor_expression_at inner j active) (fun j => cursor_tree_at inner j probe) inner_fuel 0) answer).
  { eapply (@cursor_tree_run_transport _ entry outer index current answer); [exact CURSOR| |exact CHECK].
    eapply temp_agree_weaken with (big:=live); [apply nested_cursor_inner_public|exact FRAME]. }
  eapply (@cursor_bounded_scan_execution fe (Entry (entry_ge entry) (entry_env entry) current (entry_memory entry))
    inner result 0 (Z.of_nat inner_fuel) active probe (outer::live) inner_fuel answer).
  - exact INNER_RESULT.
  - cbn; intros [SAME|MEMBER]; [congruence|contradiction].
  - cbn; intros [SAME|MEMBER]; [congruence|contradiction].
  - exact RESULT_FRESH.
  - exact INNER_READS.
  - exact POINT_READS.
  - unfold signed_range; change (-2147483648 <= 0 <= 2147483647); lia.
  - exact INNER_RANGE.
  - lia.
  - exact LOGICAL.
Qed.

Theorem nested_cursor_scan_execution answer :
  decision_run entry (nested_cursor_scan_spec outer inner active outer_active probe outer_fuel inner_fuel) answer ->
  exists after,
    exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
      (nested_cursor_scan outer inner result (Z.of_nat outer_fuel) (Z.of_nat inner_fuel) outer_active active probe)
      E0 after (entry_memory entry) Out_normal /\
    temp_agree live (entry_temps entry) after /\ after ! result=Some (Vint (shared_guard_word answer)).
Proof.
  intro CHECK; unfold nested_cursor_scan; eapply bounded_check_prefix_execution with
    (floor:=0) (active_at:=fun i => cursor_expression_at outer i outer_active)
    (probe:=fun i => nested_cursor_inner_spec outer inner i active probe inner_fuel) (fuel:=outer_fuel).
  - exact OUTER_RESULT.
  - exact OUTER_PRIVATE.
  - exact OUTER_RANGE.
  - intros index current choice FLOOR INDEX CURSOR FRAME TEST.
    eapply cursor_expression_test_transport; [exact CURSOR| |exact TEST].
    eapply temp_agree_weaken with (big:=live); [|exact FRAME].
    intros id READ; destruct (@cursor_expression_at_reads outer index outer_active id READ) as [ORIGINAL OTHER].
    apply OUTER_READS; assumption.
  - intros index current choice RANGE INDEX CURSOR FLAG FRAME POINT.
    eapply nested_cursor_inner_execution; [exact CURSOR|exact FRAME|exact POINT].
  - exact RESULT_PRIVATE.
  - lia.
  - lia.
  - unfold signed_range; change (-2147483648 <= 0 <= 2147483647); lia.
  - exact CHECK.
Qed.
End EXECUTION.

Lemma nested_cursor_scan_supported outer inner result outer_ceiling inner_ceiling outer_active active probe :
  private_scan_statement (nested_cursor_scan outer inner result outer_ceiling inner_ceiling outer_active active probe).
Proof. unfold nested_cursor_scan; apply bounded_check_prefix_supported,cursor_bounded_scan_supported. Qed.

Print Assumptions cursor_tree_at_bounded_check.
Print Assumptions cursor_expression_at_commute.
Print Assumptions cursor_tree_at_commute.
Print Assumptions check_tree_bind_read_scope.
Print Assumptions bounded_check_tree_read_scope.
Print Assumptions nested_cursor_inner_public.
Print Assumptions nested_cursor_inner_execution.
Print Assumptions nested_cursor_scan_execution.
Print Assumptions nested_cursor_scan_supported.
