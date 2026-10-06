From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightPureExpr
  ClightProjectedExecution ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryBooleanScan
  GuardMemoryBooleanRectangleExecution GuardMemoryParamBoundaryScan GuardMemoryParamBoundaryMasks
  GuardMemoryParamBoundaryPair GuardMemoryParamAxisPairScan GuardMemoryParamAxisPairChoice
  GuardMemoryParamAxisScan GuardMemoryParamAxisFrame GuardMemoryParamAxisGuard
  GuardMemoryParamPointerSyntax GuardMemoryParamPointerHeader GuardMemoryParamPointerProjectedCandidate
  GuardMemoryProjectedCondition.
From GuardInterface Require Import ClightPrivateScan ClightQuietDeterminacy ClightSharedGuard
  ClightParamPointerEntryFacts.
Import ListNotations.
Set Implicit Arguments.

Lemma param_scan_rectangle_supported counters bounds body :
  private_scan_statement body ->
  private_scan_statement (memory_boolean_rectangle_statement counters bounds body).
Proof.
  intro BODY; revert bounds; induction counters as [|counter rest IH]; intros bounds;
    [exact BODY|destruct bounds as [|bound tail]; [constructor|]].
  cbn [memory_boolean_rectangle_statement]; unfold counted_loop, counter_increment.
  auto 6 using scan_sequence, scan_set, scan_loop, scan_if, scan_break.
Qed.
Lemma param_scan_boundary_masks_supported layout counters parameters zero flag bounds masks first second first_expression second_expression :
  private_scan_statement (memory_param_affine_axis_boundary_masks_statement layout counters parameters zero flag bounds masks
    first second first_expression second_expression).
Proof.
  induction masks; cbn [memory_param_affine_axis_boundary_masks_statement]; [constructor|].
  constructor; [|exact IHmasks].
  unfold memory_param_affine_axis_boundary_mask_statement.
  apply param_scan_rectangle_supported; unfold memory_boolean_test_body.
  auto using scan_if, scan_skip, scan_set.
Qed.
Lemma param_scan_pair_supported layout left right parameters flag bounds first second first_expression second_expression :
  private_scan_statement (memory_param_affine_axis_pair_statement layout left right parameters flag bounds
    first second first_expression second_expression).
Proof.
  unfold memory_param_affine_axis_pair_statement.
  apply param_scan_rectangle_supported; apply param_scan_rectangle_supported.
  unfold memory_boolean_test_body; auto using scan_if, scan_skip, scan_set.
Qed.
Lemma param_scan_pair_choice_supported layout left right parameters flag bounds first second first_term second_term first_expression second_expression :
  private_scan_statement (memory_param_affine_axis_pair_choice_statement layout left right parameters flag bounds
    first second first_term second_term first_expression second_expression).
Proof.
  unfold memory_param_affine_axis_pair_choice_statement.
  destruct right as [|zero right]; [apply param_scan_pair_supported|].
  match goal with |- context [List.list_eq_dec Z.eq_dec ?first_list ?second_list] =>
    destruct (List.list_eq_dec Z.eq_dec first_list second_list) end;
    [|apply param_scan_pair_supported].
  unfold memory_param_affine_axis_boundary_pair_statement; constructor;
    [constructor|apply param_scan_boundary_masks_supported].
Qed.
Lemma param_scan_pairs_supported layout left right parameters flag bounds pairs :
  private_scan_statement (memory_param_axis_access_pairs_statement layout left right parameters flag bounds pairs).
Proof.
  induction pairs as [|[first second] rest IH]; [constructor|].
  cbn [memory_param_axis_access_pairs_statement]; constructor;
    [apply param_scan_pair_choice_supported|exact IH].
Qed.
Theorem param_axis_pointer_guard_supported source (package : memory_param_pointer_region_package source) left right flag :
  private_scan_statement (memory_param_axis_pointer_guard_statement package left right flag).
Proof.
  unfold memory_param_axis_pointer_guard_statement, memory_param_axis_pointer_scan_statement.
  constructor; [apply private_scan_tree; constructor|].
  constructor; [constructor|]; constructor; [apply param_scan_pairs_supported|].
  constructor; constructor.
Qed.

(** The result initialization is real code. Freshness permits transporting
    the existing scan witness through that write, without assuming P first. *)
Theorem param_axis_pointer_prefix_entry_witness source (package : memory_param_pointer_region_package source)
  fe entry live left right flag result :
  length left = length (memory_nest_iterators (param_pointer_region_nest package)) ->
  length right = length (memory_nest_iterators (param_pointer_region_nest package)) ->
  NoDup (left ++ right) ->
  NoDup (left ++ param_pointer_region_parameters package) ->
  NoDup (right ++ param_pointer_region_parameters package) ->
  (forall identifier, In identifier (left ++ right) ->
    ~ In identifier (memory_param_axis_pointer_guard_protected package live) /\ identifier <> flag) ->
  ~ In flag (memory_param_axis_pointer_guard_protected package live) ->
  ~ In result (statement_temps (memory_param_axis_pointer_guard_statement package left right flag) ++
    memory_param_axis_pointer_guard_protected package live) ->
  memory_param_pointer_runtime_domain package entry ->
  exists accepted checked,
    exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
      (private_scan_prefix (memory_param_axis_pointer_guard_statement package left right flag) result)
      E0 checked (entry_memory entry) Out_normal /\
    temp_agree (memory_param_axis_pointer_guard_protected package live) (entry_temps entry) checked /\
    checked ! result = Some (Vint (shared_guard_word accepted)) /\
    (accepted = true -> memory_param_pointer_runtime_presumption package entry).
Proof.
  intros LEFT RIGHT UNIQUE LEFT_PARAM RIGHT_PARAM FRESH FLAG RESULT DOMAIN.
  destruct (@param_axis_pointer_guard_entry_witness source package fe entry live left right flag
    LEFT RIGHT UNIQUE LEFT_PARAM RIGHT_PARAM FRESH FLAG DOMAIN)
    as [accepted [after [[RUN PUBLIC] [FRAME SOUND]]]].
  set (raw := memory_param_axis_pointer_guard_statement package left right flag) in *.
  assert (SUPPORTED : private_scan_statement raw) by (unfold raw; apply param_axis_pointer_guard_supported).
  set (ports := statement_temps raw ++ memory_param_axis_pointer_guard_protected package live) in *.
  assert (INIT_FRAME : temp_agree ports (entry_temps entry) (PTree.set result (Vint Int.zero) (entry_temps entry))).
  { apply temp_agree_set; exact RESULT. }
  destruct (@structured_execution_temp_transport fe (entry_ge entry) (entry_env entry)
    (entry_temps entry) (entry_memory entry) raw E0 after (entry_memory entry) _ RUN ports
    (PTree.set result (Vint Int.zero) (entry_temps entry)) (statement_temps raw)
    (private_scan_write_bound SUPPORTED)
    ltac:(intros id MEMBER; unfold ports; apply in_or_app; left; exact MEMBER) INIT_FRAME)
    as [initialized_after [INITIALIZED SAME]].
  assert (RESULT_RAW : ~ In result (statement_temps raw))
    by (intro BAD; apply RESULT; unfold ports; apply in_or_app; left; exact BAD).
  assert (RESULT_PROTECTED : ~ In result (memory_param_axis_pointer_guard_protected package live))
    by (intro BAD; apply RESULT; unfold ports; apply in_or_app; right; exact BAD).
  change (exec_stmt fe (entry_ge entry) (entry_env entry) (PTree.set result (Vint Int.zero) (entry_temps entry))
    (entry_memory entry) raw E0 initialized_after (entry_memory entry) (private_scan_outcome accepted)) in INITIALIZED.
  exists accepted,(private_scan_checked_temps result accepted initialized_after); split.
  - apply (proj2 (@private_scan_prefix_exact _ _ _ _ _ _ _ _ _ _ _ SUPPORTED)).
    exists accepted,initialized_after; repeat split; try reflexivity; exact INITIALIZED.
  - split.
    + eapply temp_agree_trans; [exact FRAME|].
      eapply temp_agree_trans.
      * eapply temp_agree_weaken; [|exact SAME]; intros id MEMBER; unfold ports; apply in_or_app; right; exact MEMBER.
      * destruct accepted; cbn [private_scan_checked_temps];
          [apply temp_agree_set; exact RESULT_PROTECTED|apply temp_agree_refl].
    + split; [eapply private_scan_result_value; eassumption|exact SOUND].
Qed.

Theorem param_axis_pointer_prefix_all_executions source (package : memory_param_pointer_region_package source)
  fe entry live left right flag result :
  length left = length (memory_nest_iterators (param_pointer_region_nest package)) ->
  length right = length (memory_nest_iterators (param_pointer_region_nest package)) ->
  NoDup (left ++ right) ->
  NoDup (left ++ param_pointer_region_parameters package) ->
  NoDup (right ++ param_pointer_region_parameters package) ->
  (forall identifier, In identifier (left ++ right) ->
    ~ In identifier (memory_param_axis_pointer_guard_protected package live) /\ identifier <> flag) ->
  ~ In flag (memory_param_axis_pointer_guard_protected package live) ->
  ~ In result (statement_temps (memory_param_axis_pointer_guard_statement package left right flag) ++
    memory_param_axis_pointer_guard_protected package live) ->
  memory_param_pointer_runtime_domain package entry ->
  forall trace checked final outcome,
    exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
      (private_scan_prefix (memory_param_axis_pointer_guard_statement package left right flag) result)
      trace checked final outcome ->
    trace = E0 /\ final = entry_memory entry /\ outcome = Out_normal /\
    temp_agree (memory_param_axis_pointer_guard_protected package live) (entry_temps entry) checked /\
    (expression_test (shared_guard_choice result)
      (Entry (entry_ge entry) (entry_env entry) checked (entry_memory entry)) true ->
      memory_param_pointer_runtime_presumption package entry).
Proof.
  intros LEFT RIGHT UNIQUE LEFT_PARAM RIGHT_PARAM FRESH FLAG RESULT DOMAIN trace checked final outcome RUN.
  destruct (@param_axis_pointer_prefix_entry_witness source package fe entry live left right flag result
    LEFT RIGHT UNIQUE LEFT_PARAM RIGHT_PARAM FRESH FLAG RESULT DOMAIN)
    as [accepted [first [WITNESS [FRAME [VALUE SOUND]]]]].
  destruct (@quiet_execution_determinate fe (entry_ge entry) (entry_env entry)
    (entry_temps entry) (entry_memory entry) _ _ _ _ _ WITNESS
    (private_scan_quiet (private_scan_prefix_supported result
      (param_axis_pointer_guard_supported package left right flag))) _ _ _ _ RUN)
    as [TRACE [TEMPS [MEMORY OUTCOME]]].
  subst trace checked final outcome; split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [exact FRAME|]]]].
  intros [value [EVAL BOOL]]; unfold shared_guard_choice in EVAL; apply scalar_temp_inv in EVAL.
  cbn [entry_temps] in EVAL; rewrite VALUE in EVAL; inversion EVAL; subst value.
  destruct accepted.
  - apply SOUND; reflexivity.
  - change (Some false = Some true) in BOOL; discriminate.
Qed.

Print Assumptions param_axis_pointer_guard_supported.
Print Assumptions param_axis_pointer_prefix_entry_witness.
Print Assumptions param_axis_pointer_prefix_all_executions.
