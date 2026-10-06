From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Integers.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightRegionProgress ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryBooleanScan
  GuardMemoryBooleanRectangleExecution GuardMemoryParamBoundaryScan GuardMemoryParamBoundaryMasks
  GuardMemoryParamBoundaryPair GuardMemoryParamAxisPairScan GuardMemoryParamAxisPairChoice
  GuardMemoryParamAxisScan GuardMemoryParamAxisFrame GuardMemoryParamAxisGuard
  GuardMemoryParamPointerSyntax GuardMemoryParamPointerHeader GuardMemoryParamPointerProjectedCandidate GuardMemoryProjectedCondition.
From GuardInterface Require Import ClightPrivateCheckFacts.
Import ListNotations.
Set Implicit Arguments.

Lemma private_check_tree_quiet tree yes no :
  quiet_statement yes = true -> quiet_statement no = true ->
  quiet_statement (tree_statement tree yes no) = true.
Proof.
  intros YES NO; induction tree as [accepted|atom left IHleft right IHright];
    cbn [tree_statement quiet_statement].
  - destruct accepted; assumption.
  - rewrite IHleft, IHright; reflexivity.
Qed.
Lemma private_check_rectangle_quiet counters bounds body :
  quiet_statement body = true ->
  quiet_statement (memory_boolean_rectangle_statement counters bounds body) = true.
Proof.
  intro BODY; revert bounds; induction counters as [|counter rest IH]; intros bounds;
    [exact BODY|destruct bounds as [|bound tail]; [reflexivity|]].
  cbn [memory_boolean_rectangle_statement counted_loop counter_increment quiet_statement].
  rewrite IH; reflexivity.
Qed.
Lemma private_check_boundary_masks_quiet layout counters parameters zero flag bounds masks first second first_expression second_expression :
  quiet_statement (memory_param_affine_axis_boundary_masks_statement layout counters parameters zero flag bounds masks
    first second first_expression second_expression) = true.
Proof.
  induction masks; cbn [memory_param_affine_axis_boundary_masks_statement quiet_statement]; [reflexivity|].
  rewrite IHmasks, andb_true_r.
  unfold memory_param_affine_axis_boundary_mask_statement.
  apply private_check_rectangle_quiet; reflexivity.
Qed.
Lemma private_check_pair_quiet layout left right parameters flag bounds first second first_expression second_expression :
  quiet_statement (memory_param_affine_axis_pair_statement layout left right parameters flag bounds
    first second first_expression second_expression) = true.
Proof.
  unfold memory_param_affine_axis_pair_statement.
  apply private_check_rectangle_quiet; apply private_check_rectangle_quiet; reflexivity.
Qed.
Lemma private_check_pair_choice_quiet layout left right parameters flag bounds first second first_term second_term first_expression second_expression :
  quiet_statement (memory_param_affine_axis_pair_choice_statement layout left right parameters flag bounds
    first second first_term second_term first_expression second_expression) = true.
Proof.
  unfold memory_param_affine_axis_pair_choice_statement.
  destruct right as [|zero right]; [apply private_check_pair_quiet|].
  match goal with |- context [List.list_eq_dec Z.eq_dec ?first_list ?second_list] =>
    destruct (List.list_eq_dec Z.eq_dec first_list second_list) end;
    [|apply private_check_pair_quiet].
  cbn [memory_param_affine_axis_boundary_pair_statement quiet_statement].
  apply private_check_boundary_masks_quiet.
Qed.
Lemma private_check_pairs_quiet layout left right parameters flag bounds pairs :
  quiet_statement (memory_param_axis_access_pairs_statement layout left right parameters flag bounds pairs) = true.
Proof.
  induction pairs as [|[first second] rest IH]; [reflexivity|].
  cbn [memory_param_axis_access_pairs_statement quiet_statement].
  rewrite IH, private_check_pair_choice_quiet; reflexivity.
Qed.
Theorem param_axis_pointer_guard_quiet source (package : memory_param_pointer_region_package source) left right flag :
  quiet_statement (memory_param_axis_pointer_guard_statement package left right flag) = true.
Proof.
  unfold memory_param_axis_pointer_guard_statement, memory_param_axis_pointer_scan_statement.
  cbn [quiet_statement].
  rewrite (@private_check_tree_quiet (memory_param_pointer_header_tree package) Sskip Sbreak eq_refl eq_refl),
    private_check_pairs_quiet; reflexivity.
Qed.

(** This closes the all-completed-executions obligation for the actual scan.
    Its premise remains at the checked state; original-entry stability and
    exact host dispatch are separate, still outstanding obligations. *)
Theorem param_axis_pointer_guard_all_executions source (package : memory_param_pointer_region_package source)
  fe entry live left right flag :
  length left = length (memory_nest_iterators (param_pointer_region_nest package)) ->
  length right = length (memory_nest_iterators (param_pointer_region_nest package)) ->
  NoDup (left ++ right) ->
  NoDup (left ++ param_pointer_region_parameters package) ->
  NoDup (right ++ param_pointer_region_parameters package) ->
  (forall identifier, In identifier (left ++ right) ->
    ~ In identifier (memory_param_axis_pointer_guard_protected package live) /\ identifier <> flag) ->
  ~ In flag (memory_param_axis_pointer_guard_protected package live) ->
  memory_param_pointer_runtime_domain package entry ->
  forall accepted checked,
    memory_projected_check_execution fe entry live
      (memory_param_axis_pointer_guard_statement package left right flag) accepted checked ->
    accepted = true -> memory_param_pointer_runtime_presumption package
      (Entry (entry_ge entry) (entry_env entry) checked (entry_memory entry)).
Proof.
  intros LEFT RIGHT UNIQUE LEFT_PARAM RIGHT_PARAM FRESH FLAG DOMAIN.
  apply (@projected_check_witness_all fe entry live
    (memory_param_axis_pointer_guard_statement package left right flag)
    (fun accepted checked => accepted = true -> memory_param_pointer_runtime_presumption package
      (Entry (entry_ge entry) (entry_env entry) checked (entry_memory entry)))).
  - apply param_axis_pointer_guard_quiet.
  - eapply memory_param_axis_pointer_guard_execution; eassumption.
Qed.

Print Assumptions param_axis_pointer_guard_quiet.
Print Assumptions param_axis_pointer_guard_all_executions.
