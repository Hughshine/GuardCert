From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightCountedLoop ClightTempFrame ClightTempFootprint.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineSourceExpressions
  GuardMemoryAffineRowSeparation GuardMemoryAffineChunkWriteSeparation GuardMemoryAffineCursorProbes
  GuardMemoryAffineNestedCursorProbes GuardMemoryAffineDependentRow.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite ClightIndexedAliasGuard
  ClightNestedCursorScan ClightBoundedCheckLoop ClightCursorSpecialization ClightCheckPlan ClightSharedGuard
  ClightPrivateScan ClightPrivateScanSafety ClightQuietDeterminacy ClightReadonlyExpressionScan
  ClightStagedCheck
  ClightAffineDependentLoadedStability ClightAffineDependentLoadedPrefix ClightAffineInnerPointerSourceGuard
  ClightAffinePreparedState.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition affine_dependent_cursor_outer source (package : memory_affine_inner_pointer_package source) outer :=
  Ebinop Olt (Etempvar outer type_int32s)
    (Etempvar (affine_inner_pointer_bound (affine_inner_pointer_shape package)) type_int32s) type_int32s.
Definition affine_dependent_cursor_inner source (package : memory_affine_inner_pointer_package source) outer inner :=
  memory_affine_nested_cursor_activity (affine_inner_pointer_row (affine_inner_pointer_shape package))
    (affine_inner_pointer_column (affine_inner_pointer_shape package)) outer inner (affine_inner_pointer_expression package).
Definition affine_dependent_cursor_probe source (package : memory_affine_inner_pointer_package source) root pointer_cache outer inner :=
  memory_affine_nested_cursor_dependent_probe (affine_inner_pointer_row (affine_inner_pointer_shape package))
    (affine_inner_pointer_column (affine_inner_pointer_shape package)) outer inner root pointer_cache (affine_inner_pointer_operations package).
Definition affine_dependent_cursor_scan source (package : memory_affine_inner_pointer_package source) root pointer_cache outer inner result :=
  nested_cursor_scan outer inner result
    (Z.of_nat (Z.to_nat (affine_inner_pointer_row_limit package)))
    (Z.of_nat (Z.to_nat (affine_inner_pointer_column_limit package)))
    (affine_dependent_cursor_outer package outer) (affine_dependent_cursor_inner package outer inner)
    (affine_dependent_cursor_probe package root pointer_cache outer inner).

Section SPECIFICATION.
Variable source : statement.
Variable package : memory_affine_inner_pointer_package source.
Variables root pointer_cache outer inner : ident.
Let row := affine_inner_pointer_row (affine_inner_pointer_shape package).
Let column := affine_inner_pointer_column (affine_inner_pointer_shape package).
Let cache := affine_inner_pointer_bound (affine_inner_pointer_shape package).
Hypothesis DISTINCT : outer <> inner.
Hypothesis CACHE_FRESH : cache <> outer.
Hypothesis ROOT_FRESH : root <> outer /\ root <> inner.
Hypothesis POINTER_FRESH : pointer_cache <> outer /\ pointer_cache <> inner.
Hypothesis BOUND_FRESH : forall identifier, In identifier (memory_source_affine_reads (affine_inner_pointer_expression package)) ->
  identifier <> row -> identifier <> column -> identifier <> outer /\ identifier <> inner.
Hypothesis OPERATIONS_FRESH : Forall (memory_affine_nested_cursor_operation_fresh row column outer inner)
  (affine_inner_pointer_operations package).

Lemma affine_dependent_cursor_row_spec i fuel : 0 <= i -> forall start, 0 <= start ->
  cursor_tree_at outer i (bounded_check_tree
    (fun j => cursor_expression_at inner j (affine_dependent_cursor_inner package outer inner))
    (fun j => cursor_tree_at inner j (affine_dependent_cursor_probe package root pointer_cache outer inner)) fuel start) =
  readonly_bound_expression_scan (memory_affine_row_bound row column i (affine_inner_pointer_expression package))
    (fun j => memory_affine_dependent_write_probe row column i j root pointer_cache (affine_inner_pointer_operations package)) fuel start.
Proof.
  intro I; intros start START; rewrite cursor_tree_at_bounded_check.
  assert (ACTIVE : forall j,
    cursor_expression_at outer i (cursor_expression_at inner j (affine_dependent_cursor_inner package outer inner)) =
    Ebinop Olt (Econst_int (Int.repr j) type_int32s)
      (memory_affine_row_bound row column i (affine_inner_pointer_expression package)) type_int32s).
  { intro j; unfold affine_dependent_cursor_inner,memory_affine_nested_cursor_activity.
    cbn [cursor_expression_at]; destruct (peq inner inner); [|congruence].
    rewrite memory_affine_nested_cursor_bound_inner,memory_affine_nested_cursor_bound_outer by assumption; reflexivity. }
  assert (POINT : forall j, 0 <= j ->
    cursor_tree_at outer i (cursor_tree_at inner j (affine_dependent_cursor_probe package root pointer_cache outer inner)) =
    memory_affine_dependent_write_probe row column i j root pointer_cache (affine_inner_pointer_operations package)).
  { intros j J; rewrite cursor_tree_at_commute by exact DISTINCT; unfold affine_dependent_cursor_probe.
    rewrite memory_affine_nested_cursor_dependent_outer by (try assumption; tauto).
    apply memory_affine_cursor_dependent_probe_specialized; [exact J|tauto|tauto|].
    eapply Forall_impl; [|exact OPERATIONS_FRESH]; intros operation [FIRST SECOND]; exact SECOND. }
  revert start START; induction fuel; intros start START; cbn [bounded_check_tree readonly_bound_expression_scan]; [reflexivity|].
  rewrite ACTIVE,POINT by exact START; rewrite IHfuel by lia; reflexivity.
Qed.

Theorem affine_dependent_cursor_scan_spec fuel start : 0 <= start ->
  bounded_check_tree (fun i => cursor_expression_at outer i (affine_dependent_cursor_outer package outer))
    (fun i => nested_cursor_inner_spec outer inner i (affine_dependent_cursor_inner package outer inner)
      (affine_dependent_cursor_probe package root pointer_cache outer inner)
      (Z.to_nat (affine_inner_pointer_column_limit package))) fuel start =
  affine_dependent_stability_tree package root pointer_cache fuel start.
Proof.
  revert start; induction fuel; intros start START; cbn [bounded_check_tree affine_dependent_stability_tree]; [reflexivity|].
  assert (ACTIVE : cursor_expression_at outer start (affine_dependent_cursor_outer package outer) = indexed_active_expr cache start).
  { unfold affine_dependent_cursor_outer,indexed_active_expr; fold cache; cbn [cursor_expression_at];
      destruct (peq outer outer); destruct (peq cache outer); congruence. }
  rewrite ACTIVE; unfold nested_cursor_inner_spec.
  rewrite affine_dependent_cursor_row_spec by lia; rewrite IHfuel by lia; reflexivity.
Qed.
End SPECIFICATION.

Section EXECUTION.
Variable source : statement.
Variable package : memory_affine_inner_pointer_package source.
Variables root pointer_cache outer inner result : ident.
Let row := affine_inner_pointer_row (affine_inner_pointer_shape package).
Let column := affine_inner_pointer_column (affine_inner_pointer_shape package).
Let cache := affine_inner_pointer_bound (affine_inner_pointer_shape package).
Let active := affine_dependent_cursor_inner package outer inner.
Let outer_active := affine_dependent_cursor_outer package outer.
Let probe := affine_dependent_cursor_probe package root pointer_cache outer inner.
Let code := affine_dependent_cursor_scan package root pointer_cache outer inner result.
Variable live : list ident.
Hypothesis OUTER_INNER : outer <> inner.
Hypothesis OUTER_RESULT : outer <> result.
Hypothesis INNER_RESULT : inner <> result.
Hypothesis OUTER_PRIVATE : ~ In outer live.
Hypothesis INNER_PRIVATE : ~ In inner live.
Hypothesis RESULT_PRIVATE : ~ In result live.
Hypothesis CACHE_FRESH : cache <> outer.
Hypothesis ROOT_CURSOR : root <> outer /\ root <> inner.
Hypothesis POINTER_CURSOR : pointer_cache <> outer /\ pointer_cache <> inner.
Hypothesis BOUND_FRESH : forall identifier, In identifier (memory_source_affine_reads (affine_inner_pointer_expression package)) ->
  identifier <> row -> identifier <> column -> identifier <> outer /\ identifier <> inner.
Hypothesis OPERATIONS_FRESH : Forall (memory_affine_nested_cursor_operation_fresh row column outer inner)
  (affine_inner_pointer_operations package).
Hypothesis RESULT_FRESH : ~ In result (check_plan_reads (tree_check_plan probe)).
Hypothesis OUTER_READS : forall id, In id (expression_temps outer_active) -> id <> outer -> In id live.
Hypothesis INNER_READS : forall id, In id (expression_temps active) -> id <> inner -> In id (outer::live).
Hypothesis POINT_READS : forall id, In id (check_plan_reads (tree_check_plan probe)) -> id <> inner -> In id (outer::live).
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable O : Type.
Variable observe : fragment_observation -> O -> Prop.
Hypothesis ROOT_SOURCE : root <> row /\ root <> column /\ root <> affine_inner_pointer_inner_bound (affine_inner_pointer_shape package).
Hypothesis POINTER_SOURCE : pointer_cache <> row /\ pointer_cache <> column /\ pointer_cache <> affine_inner_pointer_inner_bound (affine_inner_pointer_shape package).

Theorem affine_dependent_cursor_scan_execution entry answer :
  decision_run entry (affine_dependent_stability_tree package root pointer_cache (Z.to_nat (affine_inner_pointer_row_limit package)) 0) answer ->
  exists after,
    exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry) code E0 after (entry_memory entry) Out_normal /\
    temp_agree live (entry_temps entry) after /\ after ! result=Some (Vint (shared_guard_word answer)).
Proof.
  intro CHECK; unfold code,affine_dependent_cursor_scan; eapply nested_cursor_scan_execution;
    [exact OUTER_INNER|exact OUTER_RESULT|exact INNER_RESULT|exact OUTER_PRIVATE|exact INNER_PRIVATE|exact RESULT_PRIVATE|
     exact RESULT_FRESH|exact OUTER_READS|exact INNER_READS|exact POINT_READS| | |].
  - pose proof (affine_inner_pointer_control_limits (affine_inner_pointer_syntax package)) as CAPS; inversion CAPS; subst;
      rewrite Z2Nat.id by lia; tauto.
  - pose proof (affine_inner_pointer_control_limits (affine_inner_pointer_syntax package)) as CAPS; inversion CAPS; subst;
      match goal with REST : Forall _ [_] |- _ => inversion REST; subst end; rewrite Z2Nat.id by lia; tauto.
  - unfold nested_cursor_scan_spec; rewrite affine_dependent_cursor_scan_spec by (try assumption; lia); exact CHECK.
Qed.

Lemma affine_dependent_cursor_scan_public :
  incl (check_plan_reads (tree_check_plan (affine_dependent_stability_tree package root pointer_cache
    (Z.to_nat (affine_inner_pointer_row_limit package)) 0))) live.
Proof.
  rewrite <- (@affine_dependent_cursor_scan_spec source package root pointer_cache outer inner
    OUTER_INNER CACHE_FRESH ROOT_CURSOR POINTER_CURSOR BOUND_FRESH OPERATIONS_FRESH
    (Z.to_nat (affine_inner_pointer_row_limit package)) 0 ltac:(lia)).
  apply bounded_check_tree_read_scope.
  - intros index id MEMBER.
    destruct (@cursor_expression_at_reads outer index outer_active id MEMBER) as [READ OTHER].
    apply OUTER_READS; assumption.
  - intro index; apply nested_cursor_inner_public; [exact INNER_READS|exact POINT_READS].
Qed.

Theorem affine_dependent_cursor_scan_execution_current entry current answer :
  temp_agree live (entry_temps entry) current ->
  decision_run entry (affine_dependent_stability_tree package root pointer_cache (Z.to_nat (affine_inner_pointer_row_limit package)) 0) answer ->
  exists after,
    exec_stmt fe (entry_ge entry) (entry_env entry) current (entry_memory entry) code E0 after (entry_memory entry) Out_normal /\
    temp_agree live current after /\ after ! result=Some (Vint (shared_guard_word answer)).
Proof.
  intros FRAME CHECK; eapply (affine_dependent_cursor_scan_execution
    (entry:=Entry (entry_ge entry) (entry_env entry) current (entry_memory entry))).
  eapply decision_tree_read_frame; [|exact CHECK].
  eapply temp_agree_weaken with (big:=live); [apply affine_dependent_cursor_scan_public|exact FRAME].
Qed.

Theorem affine_dependent_cursor_scan_available entry :
  affine_dependent_loaded_completed package root pointer_cache fe entry -> affine_inner_pointer_ready package entry ->
  exists answer after,
    decision_run entry (affine_dependent_stability_tree package root pointer_cache (Z.to_nat (affine_inner_pointer_row_limit package)) 0) answer /\
    exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry) code E0 after (entry_memory entry) Out_normal /\
    temp_agree live (entry_temps entry) after /\ after ! result=Some (Vint (shared_guard_word answer)).
Proof.
  intros SOURCE READY.
  destruct (readonly_available (@affine_dependent_stability_condition source package root pointer_cache ROOT_SOURCE POINTER_SOURCE
    fe O observe) entry (conj SOURCE READY)) as [answer [checked [CHECK SAME]]].
  destruct (affine_dependent_cursor_scan_execution CHECK) as [after [RUN [FRAME FLAG]]].
  exists answer,after; split; [exact CHECK|split; [exact RUN|split; assumption]].
Qed.

Theorem affine_dependent_cursor_scan_safe entry :
  affine_dependent_loaded_completed package root pointer_cache fe entry -> affine_inner_pointer_ready package entry ->
  private_scan_safe fe (entry_ge entry) (entry_env entry) code (entry_temps entry) (entry_memory entry).
Proof.
  intros SOURCE READY; destruct (affine_dependent_cursor_scan_available SOURCE READY) as [answer [after [CHECK [RUN REST]]]].
  eapply completed_private_scan_safe; [exact RUN|unfold code,affine_dependent_cursor_scan; apply nested_cursor_scan_supported].
Qed.

Theorem affine_dependent_cursor_scan_accepted entry trace after final outcome :
  affine_dependent_loaded_completed package root pointer_cache fe entry -> affine_inner_pointer_ready package entry ->
  exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry) code trace after final outcome ->
  after ! result=Some (Vint Int.one) -> affine_dependent_writes_separated package root pointer_cache entry.
Proof.
  intros SOURCE READY ACTUAL ACCEPT.
  destruct (affine_dependent_cursor_scan_available SOURCE READY) as [answer [expected [CHECK [RUN [FRAME FLAG]]]]].
  destruct (@quiet_execution_determinate _ _ _ _ _ _ _ _ _ _ RUN
    ltac:(apply private_scan_quiet; unfold code,affine_dependent_cursor_scan; apply nested_cursor_scan_supported)
    _ _ _ _ ACTUAL) as [TRACE [TEMPS [MEMORY OUTCOME]]].
  subst after; rewrite ACCEPT in FLAG; assert (ANSWER : answer=true) by
    (destruct answer; [reflexivity|cbn [shared_guard_word] in FLAG; discriminate]).
  subst answer.
  exact (proj2 (readonly_sound (@affine_dependent_stability_condition source package root pointer_cache ROOT_SOURCE POINTER_SOURCE
    fe O observe) entry true entry (conj SOURCE READY) (conj CHECK eq_refl)) eq_refl).
Qed.
End EXECUTION.

Print Assumptions affine_dependent_cursor_row_spec.
Print Assumptions affine_dependent_cursor_scan_spec.
Print Assumptions affine_dependent_cursor_scan_execution.
Print Assumptions affine_dependent_cursor_scan_public.
Print Assumptions affine_dependent_cursor_scan_execution_current.
Print Assumptions affine_dependent_cursor_scan_available.
Print Assumptions affine_dependent_cursor_scan_safe.
Print Assumptions affine_dependent_cursor_scan_accepted.
