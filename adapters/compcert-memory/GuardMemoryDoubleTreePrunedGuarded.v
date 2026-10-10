From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightTempFrame ClightTempFootprint ClightGlobalScope ClightRegionProgress.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLongControl GuardMemoryDoubleLocations
  GuardMemoryDoubleSourceTreeData GuardMemoryDoubleSourceTreeDecode GuardMemoryDoubleSourceTreeCertificates
  GuardMemoryDoubleSourceTreeState GuardMemoryDoubleSourceTreeModelData GuardMemoryDoubleSourceTreeExit
  GuardMemoryDoublePipelineTransport GuardMemoryDoublePolyhedral GuardMemoryDoubleTensorBackend
  GuardMemoryDoubleTreeCaptureData GuardMemoryDoubleTreeCapturePrepared GuardMemoryDoubleTreeCacheFrame
  GuardMemoryDoubleTreeCacheParameters GuardMemoryDoubleTreeCacheEnvironment GuardMemoryDoubleTreeFootprint
  GuardMemoryDoubleTreePreparedModel GuardMemoryDoubleTreeCandidate GuardMemoryDoubleTreePrepared
  GuardMemoryDoubleTreeExitCode GuardMemoryDoubleTreePrunedCandidate GuardMemoryDoubleTreeGuarded GuardMemoryDoubleTreeSourcePrepared.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Consume the generated preparation, actual polyhedral phase/final checker,
    machine candidate lowering and executable public-exit restoration together.
    No dynamic source-model correspondence premise is supplied by the caller. *)
Theorem checked_double_tree_pruned_guarded_execution p source tree cache flag lower upper live pool phase adapt shifts_proposal choices generated code
  fe ge locals temps memory after final :
  checked_double_source_tree p source=Some tree -> preserving_globals (globalenv p) ge ->
  double_source_tree_scope tree locals -> locals_avoid (double_source_tree_headers tree) locals ->
  double_tensor_static ge locals (double_source_tree_layouts tree) ->
  double_tree_footprint_check tree upper []=true ->
  (forall header, In header (double_source_tree_headers tree) ->
    Int.min_signed<=lower header<=Int.max_signed /\ Int.min_signed<=upper header<=Int.max_signed) ->
  double_tree_cache_distinct (double_source_tree_headers tree) cache ->
  (forall header, In header (double_source_tree_headers tree) -> cache header<>flag) ->
  (forall header, In header (double_source_tree_headers tree) -> ~ In (cache header) (double_source_tree_writes tree)) ->
  (forall key, In key (statement_temps source++live) -> ~ In key (double_tree_capture_private tree cache flag)) ->
  mayReturn (checked_double_tree_source_prepared_loop_progress phase adapt shifts_proposal choices
    (double_tree_parameter_intervals (double_source_tree_parameters tree) lower upper) (double_tree_pipeline_request tree))
    (Some generated) ->
  compile_pruned_double_tree_candidate (double_source_tree_layouts tree) tree cache flag lower upper live pool generated=Some code ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists target_after,
    exec_stmt fe ge locals temps memory (double_tree_guarded_code source tree cache flag lower upper code)
      E0 target_after final Out_normal /\ temp_agree live after target_after.
Proof.
  intros CHECK GLOBAL SCOPE LOCAL STATIC FOOTPRINT LIMITS DISTINCT FLAG_FRESH CACHES_FRESH PRIVATE PIPELINE CODE SOURCE.
  destruct (@checked_double_tree_prepared_model p source tree fe ge locals temps memory after final live cache flag lower upper
    CHECK GLOBAL SCOPE LOCAL FOOTPRINT LIMITS DISTINCT FLAG_FRESH PRIVATE SOURCE)
    as [prepared [accepted [prepared_after [PREPARE [FLAG [ENTRY [ENV [FALLBACK [EXIT FACTS]]]]]]]]].
  destruct accepted.
  - destruct (FACTS eq_refl) as [MODEL SET].
    assert (CANDIDATE_MODEL : DoubleAssignmentIRs.Loop.loop_semantics (fst (fst generated))
      (double_tree_cached_parameters tree cache prepared)
      (RuntimeState (global_double_locations ge (double_source_tree_layouts tree)) memory)
      (RuntimeState (global_double_locations ge (double_source_tree_layouts tree)) final)).
    { eapply (@checked_double_tree_source_prepared_loop_progress_at phase adapt shifts_proposal choices
        (double_tree_parameter_intervals (double_source_tree_parameters tree) lower upper)
        (double_tree_pipeline_request tree) generated _ _ _ PIPELINE).
      - unfold double_tree_pipeline_request,double_tree_cached_parameters; cbn [fst snd]; rewrite map_length; reflexivity.
      - apply global_double_locations_nonalias.
      - apply double_tree_cached_parameter_ranges; exact ENV.
      - apply double_pipeline_execution; exact MODEL. }
    destruct (@compiled_pruned_double_tree_candidate_execution (double_source_tree_layouts tree) tree cache flag lower upper live
      pool generated code fe ge locals prepared memory final STATIC CODE ENV CANDIDATE_MODEL)
      as [candidate_after [FRAME CANDIDATE]].
    assert (CACHE_FRAME : forall header, In header (double_source_tree_headers tree) ->
      candidate_after ! (cache header)=prepared ! (cache header)).
    { intros header MEMBER; apply FRAME; apply in_or_app; left; apply in_map,
        double_source_tree_parameter_membership; exact MEMBER. }
    assert (VALUES : forall header, In header (double_source_tree_headers tree) ->
      double_tree_cached_value cache candidate_after header=double_tree_cached_value cache prepared header).
    { intros header MEMBER; unfold double_tree_cached_value; rewrite CACHE_FRAME by exact MEMBER; reflexivity. }
    assert (RESTORE : exec_stmt fe ge locals candidate_after final (double_tree_exit_code tree cache) E0
      (double_source_tree_exit (double_tree_cached_value cache candidate_after) tree candidate_after) final Out_normal).
    { apply double_tree_exit_code_execution; [exact CACHES_FRESH|].
      intros header MEMBER; destruct (ENV header (proj2 (@double_source_tree_parameter_membership tree header) MEMBER)) as [word [WORD RANGE]].
      exists word; rewrite CACHE_FRAME by exact MEMBER; exact WORD. }
    exists (double_source_tree_exit (double_tree_cached_value cache candidate_after) tree candidate_after); split.
    + unfold double_tree_guarded_code; eapply exec_Sseq_1 with (le1:=prepared) (m1:=memory) (t1:=E0) (t2:=E0); [exact PREPARE|].
      eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true); [constructor; exact FLAG|reflexivity|].
      eapply exec_Sseq_1 with (le1:=candidate_after) (m1:=final) (t1:=E0) (t2:=E0); eassumption.
    + eapply temp_agree_trans; [exact EXIT|rewrite SET].
      rewrite (@double_tree_exit_valuation_agree tree (double_tree_cached_value cache prepared)
        (double_tree_cached_value cache candidate_after) candidate_after VALUES).
      apply double_tree_exit_public_frame; eapply temp_agree_weaken; [|exact FRAME].
      intros key MEMBER; apply in_or_app; right; right; exact MEMBER.
  - exists prepared_after; split; [|exact EXIT].
    unfold double_tree_guarded_code; eapply exec_Sseq_1 with (le1:=prepared) (m1:=memory) (t1:=E0) (t2:=E0); [exact PREPARE|].
    eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false); [constructor; exact FLAG|reflexivity|exact FALLBACK].
Qed.

Print Assumptions checked_double_tree_pruned_guarded_execution.
