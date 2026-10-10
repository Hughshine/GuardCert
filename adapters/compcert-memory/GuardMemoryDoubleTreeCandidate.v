From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDoubleLocations GuardMemoryDoubleSourceTreeData
  GuardMemoryDoubleTreeCacheParameters GuardMemoryDoubleTreeCacheEnvironment GuardMemoryDoublePolyhedral
  GuardMemoryDoubleTensorBackend GuardMemoryDoubleNestedBackend.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition double_tree_candidate_intervals (headers : list ident) (lower upper : ident -> Z) := map
  (fun header=>DoubleNested.A.Interval (Z.min 0 (lower header)) (Z.max 0 (upper header))) headers.
Theorem double_tree_cache_typed_view headers cache lower upper temps :
  double_tree_cache_environment headers cache lower upper temps ->
  DoubleNested.A.typed_view (map cache headers) (map (double_tree_cached_value cache temps) headers) temps.
Proof.
  induction headers as [|header headers IH]; intros ENV [|index] identifier INDEX; cbn in INDEX; try discriminate.
  - inversion INDEX; subst identifier; cbn [map nth].
    destruct (ENV header (or_introl eq_refl)) as [word [WORD RANGE]].
    exists word; split; [exact WORD|unfold double_tree_cached_value; rewrite WORD; reflexivity].
  - cbn [map nth]; apply IH; [intros key MEMBER; apply ENV; right; exact MEMBER|exact INDEX].
Qed.
Theorem double_tree_cache_within_intervals headers cache lower upper temps :
  double_tree_cache_environment headers cache lower upper temps ->
  DoubleNested.A.env_within (double_tree_candidate_intervals headers lower upper)
    (map (double_tree_cached_value cache temps) headers).
Proof.
  induction headers as [|header headers IH]; intros ENV [|index] interval INDEX; cbn in INDEX; try discriminate.
  - inversion INDEX; subst interval; cbn [map nth]; unfold DoubleNested.A.contains.
    destruct (ENV header (or_introl eq_refl)) as [word [WORD RANGE]].
    unfold double_tree_cached_value; rewrite WORD; exact RANGE.
  - cbn [map nth]; apply IH; [intros key MEMBER; apply ENV; right; exact MEMBER|exact INDEX].
Qed.
Definition compile_double_tree_candidate layouts tree cache flag lower upper live pool (generated : DoubleAssignmentIRs.Loop.t) :=
  compile_double_tensor_loop layouts (map cache (double_source_tree_parameters tree))
    (double_tree_candidate_intervals (double_source_tree_parameters tree) lower upper)
    (flag::live) pool (fst (fst generated)).
Theorem compiled_double_tree_candidate_execution layouts tree cache flag lower upper live pool generated code
  fe ge locals temps memory final :
  double_tensor_static ge locals layouts ->
  compile_double_tree_candidate layouts tree cache flag lower upper live pool generated=Some code ->
  double_tree_cache_environment (double_source_tree_parameters tree) cache lower upper temps ->
  DoubleAssignmentIRs.Loop.loop_semantics (fst (fst generated)) (double_tree_cached_parameters tree cache temps)
    (RuntimeState (global_double_locations ge layouts) memory) (RuntimeState (global_double_locations ge layouts) final) ->
  exists candidate_after, temp_agree (map cache (double_source_tree_parameters tree)++flag::live) temps candidate_after /\
    exec_stmt fe ge locals temps memory code E0 candidate_after final Out_normal.
Proof.
  intros STATIC CODE ENV MODEL.
  destruct (@compile_double_tensor_loop_correct fe ge locals layouts STATIC
    (map cache (double_source_tree_parameters tree))
    (double_tree_candidate_intervals (double_source_tree_parameters tree) lower upper) (flag::live) pool
    (fst (fst generated)) code (double_tree_cached_parameters tree cache temps) temps _ _ memory CODE
    (double_tree_cache_typed_view ENV) (double_tree_cache_within_intervals ENV) MODEL ltac:(split; reflexivity))
    as [candidate_after [target_memory [[LOCATIONS SAME] [FRAME RUN]]]].
  cbn [runtime_memory] in SAME; subst target_memory; exists candidate_after; auto.
Qed.

Print Assumptions double_tree_cache_typed_view.
Print Assumptions double_tree_cache_within_intervals.
Print Assumptions compiled_double_tree_candidate_execution.
