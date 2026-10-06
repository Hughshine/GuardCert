From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightCountedLoop ClightTempFrame ClightTempFootprint
  CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryAffineCursorProbes GuardMemoryAffineDependentRow
  GuardMemoryAffineRowSeparation GuardMemoryAffineSourceExpressions GuardMemoryAffineChunkWriteSeparation
  GuardMemoryNaryCompute GuardMemoryMultiPointerSequence GuardMemoryObservationStability.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite ClightReadonlyExpressionScan
  ClightBoundedCheckLoop ClightCursorSpecialization ClightCursorCheckBody ClightCursorBoundedScan
  ClightCheckPlan ClightSharedGuard ClightPrivateScan ClightPrivateScanSafety ClightQuietDeterminacy
  ClightDependentHeaderObservations.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_affine_dependent_cursor_activity row column i expression cursor :=
  Ebinop Olt (Etempvar cursor type_int32s) (memory_affine_row_bound row column i expression) type_int32s.
Definition memory_affine_dependent_cursor_row row column i expression cursor result root pointer_cache operations cap :=
  cursor_bounded_scan cursor 0 (Z.of_nat cap)
    (memory_affine_dependent_cursor_activity row column i expression cursor)
    (memory_affine_cursor_dependent_probe row column i cursor root pointer_cache operations) result.

(** The runtime body is independent of cap. This logical equality reuses the
    original row certificate, including reached-write receipts and coverage. *)
Theorem memory_affine_dependent_cursor_row_spec row column i expression cursor root pointer_cache operations fuel start :
  0 <= start -> ~ In cursor (expression_temps (memory_affine_row_bound row column i expression)) ->
  root <> cursor -> pointer_cache <> cursor ->
  Forall (memory_affine_cursor_operation_fresh row column cursor) operations ->
  bounded_check_tree
    (fun j => cursor_expression_at cursor j (memory_affine_dependent_cursor_activity row column i expression cursor))
    (fun j => cursor_tree_at cursor j (memory_affine_cursor_dependent_probe row column i cursor root pointer_cache operations))
    fuel start =
  readonly_bound_expression_scan (memory_affine_row_bound row column i expression)
    (fun j => memory_affine_dependent_write_probe row column i j root pointer_cache operations) fuel start.
Proof.
  intros START BOUND ROOT POINTER FRESH.
  assert (ACTIVITY : forall j,
    cursor_expression_at cursor j (memory_affine_dependent_cursor_activity row column i expression cursor) =
    Ebinop Olt (Econst_int (Int.repr j) type_int32s) (memory_affine_row_bound row column i expression) type_int32s).
  { intro j; unfold memory_affine_dependent_cursor_activity; cbn [cursor_expression_at];
      destruct (peq cursor cursor); [|congruence]; rewrite cursor_expression_at_fresh by exact BOUND; reflexivity. }
  revert start START; induction fuel as [|fuel IH]; intros start START;
    cbn [bounded_check_tree readonly_bound_expression_scan]; [reflexivity|].
  rewrite ACTIVITY.
  rewrite memory_affine_cursor_dependent_probe_specialized by assumption.
  rewrite IH by lia; reflexivity.
Qed.

Section ROW.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable O : Type.
Variable observe : fragment_observation -> O -> Prop.
Variables row column cursor result root pointer_cache cache : ident.
Variable i : Z.
Variable expression : memory_source_affine.
Variable operations : list memory_nary_compute.
Variable cap : nat.
Variable live : list ident.
Variables valuation : clight_entry -> ident -> Z.
Variable values : clight_entry -> Z -> list Z.
Variable width : clight_entry -> Z.
Hypothesis CAP : Z.of_nat cap <= Int.max_signed.
Hypothesis DISTINCT : cursor <> result.
Hypothesis CURSOR_PRIVATE : ~ In cursor live.
Hypothesis RESULT_PRIVATE : ~ In result live.
Hypothesis BOUND_FRESH : ~ In cursor (expression_temps (memory_affine_row_bound row column i expression)).
Hypothesis ROOT_FRESH : root <> cursor.
Hypothesis POINTER_FRESH : pointer_cache <> cursor.
Hypothesis OPERATIONS_FRESH : Forall (memory_affine_cursor_operation_fresh row column cursor) operations.
Let active := memory_affine_dependent_cursor_activity row column i expression cursor.
Let probe := memory_affine_cursor_dependent_probe row column i cursor root pointer_cache operations.
Let code := memory_affine_dependent_cursor_row row column i expression cursor result root pointer_cache operations cap.
Hypothesis RESULT_FRESH : ~ In result (check_plan_reads (tree_check_plan probe)).
Hypothesis ACTIVITY_READS : forall identifier, In identifier (expression_temps active) -> identifier <> cursor -> In identifier live.
Hypothesis POINT_READS : forall identifier, In identifier (check_plan_reads (tree_check_plan probe)) -> identifier <> cursor -> In identifier live.
Let domain := memory_affine_dependent_row_domain row column i expression root pointer_cache cache operations cap valuation values width.

Theorem memory_affine_dependent_cursor_row_execution entry answer :
  decision_run entry (memory_affine_dependent_row_probe row column i expression root pointer_cache operations cap) answer ->
  exists after,
    exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
      code E0 after (entry_memory entry) Out_normal /\
    temp_agree live (entry_temps entry) after /\ after ! result=Some (Vint (shared_guard_word answer)).
Proof.
  intro CHECK; unfold code,memory_affine_dependent_cursor_row.
  eapply cursor_bounded_scan_execution with (fuel:=cap).
  - exact DISTINCT.
  - exact CURSOR_PRIVATE.
  - exact RESULT_PRIVATE.
  - exact RESULT_FRESH.
  - exact ACTIVITY_READS.
  - exact POINT_READS.
  - unfold signed_range; change (-2147483648 <= 0 <= 2147483647); lia.
  - unfold signed_range; change Int.min_signed with (-2147483648); pose proof (Nat2Z.is_nonneg cap); lia.
  - lia.
  - rewrite memory_affine_dependent_cursor_row_spec by (try assumption; lia); exact CHECK.
Qed.

Theorem memory_affine_dependent_cursor_row_available entry : domain entry ->
  exists answer after,
    decision_run entry (memory_affine_dependent_row_probe row column i expression root pointer_cache operations cap) answer /\
    exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
      code E0 after (entry_memory entry) Out_normal /\
    temp_agree live (entry_temps entry) after /\ after ! result=Some (Vint (shared_guard_word answer)).
Proof.
  intro DOMAIN.
  destruct (readonly_available (@memory_affine_dependent_row_condition fe O observe row column root pointer_cache cache
    i expression operations cap valuation values width CAP) entry DOMAIN) as [answer [checked [CHECK SAME]]].
  destruct (memory_affine_dependent_cursor_row_execution CHECK) as [after [RUN [FRAME FLAG]]].
  exists answer,after; split; [exact CHECK|split; [exact RUN|split; assumption]].
Qed.

Theorem memory_affine_dependent_cursor_row_safe entry : domain entry ->
  private_scan_safe fe (entry_ge entry) (entry_env entry) code (entry_temps entry) (entry_memory entry).
Proof.
  intro DOMAIN; destruct (memory_affine_dependent_cursor_row_available DOMAIN) as [answer [after [CHECK [RUN REST]]]].
  eapply completed_private_scan_safe; [exact RUN|unfold code,memory_affine_dependent_cursor_row; apply cursor_bounded_scan_supported].
Qed.

Theorem memory_affine_dependent_cursor_row_accepted_preserves entry trace after final outcome :
  domain entry ->
  exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry) code trace after final outcome ->
  after ! result=Some (Vint Int.one) ->
  forall j before next, 0 <= j < width entry ->
    memory_multi_pointer_sequence_physical (entry_temps entry) (values entry j) operations before next ->
  forall observation, In observation (dependent_header_observations root pointer_cache cache entry) ->
    location_load (fst observation) next=location_load (fst observation) before.
Proof.
  intros DOMAIN ACTUAL ACCEPT.
  destruct (memory_affine_dependent_cursor_row_available DOMAIN) as [answer [expected [CHECK [RUN [FRAME FLAG]]]]].
  destruct (@quiet_execution_determinate _ _ _ _ _ _ _ _ _ _ RUN
    ltac:(apply private_scan_quiet; unfold code,memory_affine_dependent_cursor_row; apply cursor_bounded_scan_supported)
    _ _ _ _ ACTUAL) as [TRACE [TEMPS [MEMORY OUTCOME]]].
  subst after; rewrite ACCEPT in FLAG.
  assert (ANSWER : answer=true).
  { destruct answer; [reflexivity|cbn [shared_guard_word] in FLAG; discriminate]. }
  subst answer; exact (@memory_affine_dependent_row_preserves fe O observe row column root pointer_cache cache
    i expression operations cap valuation values width CAP entry DOMAIN CHECK).
Qed.
End ROW.

Print Assumptions memory_affine_dependent_cursor_row_spec.
Print Assumptions memory_affine_dependent_cursor_row_execution.
Print Assumptions memory_affine_dependent_cursor_row_available.
Print Assumptions memory_affine_dependent_cursor_row_safe.
Print Assumptions memory_affine_dependent_cursor_row_accepted_preserves.
