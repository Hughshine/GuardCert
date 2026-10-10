From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import PolCertGuardedBodyPruning ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDoubleAssignment GuardMemoryDoubleLocations GuardMemoryDoubleSourceTreeData
  GuardMemoryDoubleTreeCacheParameters GuardMemoryDoubleTreeCacheEnvironment GuardMemoryDoublePolyhedral
  GuardMemoryDoubleTensorBackend GuardMemoryDoubleNestedBackend GuardMemoryDoubleTreeCandidate.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Module DoubleBodyPruning := PolCertGuardedBodyPruningFor DoubleAssignmentInstr DoubleAssignmentIRs.Loop.

Definition double_tree_pruning_intervals (headers : list ident) (lower upper : ident -> Z) := map
  (fun header=>DoubleBodyPruning.A.Interval (Z.min 0 (lower header)) (Z.max 0 (upper header))) headers.
Lemma double_tree_cache_within_pruning_intervals headers cache lower upper temps :
  double_tree_cache_environment headers cache lower upper temps ->
  DoubleBodyPruning.A.env_within (double_tree_pruning_intervals headers lower upper)
    (map (double_tree_cached_value cache temps) headers).
Proof.
  induction headers as [|header headers IH]; intros ENV [|index] interval INDEX; cbn in INDEX; try discriminate.
  - inversion INDEX; subst interval; cbn [map nth]; unfold DoubleBodyPruning.A.contains.
    destruct (ENV header (or_introl eq_refl)) as [word [WORD RANGE]].
    unfold double_tree_cached_value; rewrite WORD; exact RANGE.
  - cbn [map nth]; apply IH; [intros key MEMBER; apply ENV; right; exact MEMBER|exact INDEX].
Qed.
Definition double_tree_pruned_loop tree lower upper (generated : DoubleAssignmentIRs.Loop.t) :=
  DoubleBodyPruning.prune (double_tree_pruning_intervals (double_source_tree_parameters tree) lower upper)
    (fst (fst generated)).
Definition compile_pruned_double_tree_candidate layouts tree cache flag lower upper live pool generated :=
  compile_double_tensor_loop layouts (map cache (double_source_tree_parameters tree))
    (double_tree_candidate_intervals (double_source_tree_parameters tree) lower upper)
    (flag::live) pool (double_tree_pruned_loop tree lower upper generated).
Theorem compiled_pruned_double_tree_candidate_execution layouts tree cache flag lower upper live pool generated code
  fe ge locals temps memory final :
  double_tensor_static ge locals layouts ->
  compile_pruned_double_tree_candidate layouts tree cache flag lower upper live pool generated=Some code ->
  double_tree_cache_environment (double_source_tree_parameters tree) cache lower upper temps ->
  DoubleAssignmentIRs.Loop.loop_semantics (fst (fst generated)) (double_tree_cached_parameters tree cache temps)
    (RuntimeState (global_double_locations ge layouts) memory) (RuntimeState (global_double_locations ge layouts) final) ->
  exists candidate_after, temp_agree (map cache (double_source_tree_parameters tree)++flag::live) temps candidate_after /\
    exec_stmt fe ge locals temps memory code E0 candidate_after final Out_normal.
Proof.
  intros STATIC CODE ENV MODEL.
  pose proof (@DoubleBodyPruning.prune_execution (fst (fst generated))
    (double_tree_pruning_intervals (double_source_tree_parameters tree) lower upper)
    (double_tree_cached_parameters tree cache temps) _ _
    (double_tree_cache_within_pruning_intervals ENV) MODEL) as PRUNED.
  destruct (@compile_double_tensor_loop_correct fe ge locals layouts STATIC
    (map cache (double_source_tree_parameters tree))
    (double_tree_candidate_intervals (double_source_tree_parameters tree) lower upper) (flag::live) pool
    (double_tree_pruned_loop tree lower upper generated) code (double_tree_cached_parameters tree cache temps)
    temps _ _ memory CODE (double_tree_cache_typed_view ENV) (double_tree_cache_within_intervals ENV)
    PRUNED ltac:(split; reflexivity))
    as [candidate_after [target_memory [[LOCATIONS SAME] [FRAME RUN]]]].
  cbn [runtime_memory] in SAME; subst target_memory; exists candidate_after; auto.
Qed.

Definition double_body_quiet_bounds_sound := DoubleBodyPruning.quiet_bounds_sound.
Definition double_body_bound_selection_sound := DoubleBodyPruning.select_bound_execution.
Definition double_body_pruning_sound := DoubleBodyPruning.prune_execution.
Print Assumptions double_body_quiet_bounds_sound.
Print Assumptions double_body_bound_selection_sound.
Print Assumptions double_body_pruning_sound.
Print Assumptions double_tree_cache_within_pruning_intervals.
Print Assumptions compiled_pruned_double_tree_candidate_execution.
