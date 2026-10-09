From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightTempFootprint
  ClightGlobalScope ClightRegionProgress.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLongControl GuardMemoryDoubleLocations GuardMemoryDoubleAssignment
  GuardMemoryDoubleTensorBackend GuardMemoryDoubleNestedBackend GuardMemoryDoublePolyhedral
  GuardMemoryDoubleUniformPrepared GuardMemoryDoubleSourceInstruction GuardMemoryDoubleReductionNestData
  GuardMemoryDoubleReductionNestModel GuardMemoryDoubleReductionNestEntry GuardMemoryDoubleReductionNestCapture
  GuardMemoryDoubleReductionNestExitCode GuardMemoryDoubleInitializedLowering GuardMemoryLongRangeCapture
  GuardMemoryDoubleReductionNestLowering GuardMemoryDoubleTiledPrepared GuardMemoryDoubleReindexedTiledPrepared.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem checked_double_reindexed_tiled_reduction_guarded_execution p source description limit phase adapt choices generated
  cache flag live pool code fe ge locals temps memory after final :
  checked_double_reduction_raw_nest p [] source=Some description ->
  double_reduction_entry_bounds_check limit description=true ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_reduction_globals description) locals ->
  double_tensor_static ge locals (double_source_instruction_layouts (reduction_nest_instruction description)) ->
  cache<>flag -> ~ In cache (reduction_nest_iterators description) ->
  (forall key, In key (statement_temps source++live) -> ~ In key [cache;flag]) ->
  mayReturn (checked_double_reindexed_tiled_prepared_loop_progress phase adapt choices limit
    (double_reduction_pipeline_request description)) (Some generated) ->
  compile_double_reduction_candidate description cache flag limit live pool generated=Some code ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists target_after,
    exec_stmt fe ge locals temps memory
      (double_reduction_guarded_code source description cache flag limit code)
      E0 target_after final Out_normal /\ temp_agree live after target_after.
Proof.
  intros CHECK BOUNDS GLOBAL LOCAL STATIC DISTINCT CACHE_FRESH PRIVATE PIPELINE CODE SOURCE.
  pose proof (@double_reduction_checked_limit limit description BOUNDS) as LIMIT.
  destruct (@checked_double_reduction_capture_model p source description limit fe ge locals temps memory
    cache flag live after final CHECK BOUNDS GLOBAL LOCAL DISTINCT PRIVATE SOURCE)
    as [accepted [prepared [prepared_after [CAPTURE [FLAG [ENTRY [FALLBACK [EXIT FACTS]]]]]]]].
  destruct accepted.
  - destruct (FACTS eq_refl) as [count [UPPER [CACHE [MODEL SET]]]].
    assert (RANGE : signed_range (Z.of_nat count))
      by (unfold signed_range; change (-2147483648<=Z.of_nat count<=2147483647);
          change (0<limit<=2147483647) in LIMIT; lia).
    assert (CANDIDATE_MODEL : DoubleAssignmentIRs.Loop.loop_semantics (fst (fst generated)) [Z.of_nat count]
      (RuntimeState (global_double_locations ge (double_source_instruction_layouts (reduction_nest_instruction description))) memory)
      (RuntimeState (global_double_locations ge (double_source_instruction_layouts (reduction_nest_instruction description))) final)).
    { apply (@checked_double_reindexed_tiled_prepared_loop_progress_at phase adapt choices limit
        (double_reduction_pipeline_request description) generated [Z.of_nat count]
        (RuntimeState (global_double_locations ge (double_source_instruction_layouts (reduction_nest_instruction description))) memory)
        (RuntimeState (global_double_locations ge (double_source_instruction_layouts (reduction_nest_instruction description))) final)
        PIPELINE eq_refl ltac:(apply global_double_locations_nonalias)); exact MODEL. }
    destruct (@compiled_double_reduction_candidate_execution description cache flag limit live pool generated code
      fe ge locals prepared memory count final STATIC CODE RANGE UPPER CACHE CANDIDATE_MODEL)
      as [candidate_after [FRAME CANDIDATE]].
    assert (RESTORE : exec_stmt fe ge locals candidate_after final
      (double_reduction_exit_code (reduction_nest_iterators description) cache) E0
      (double_reduction_nest_exit (reduction_nest_iterators description) count candidate_after)
      final Out_normal).
    { apply double_reduction_exit_code_execution; [exact CACHE_FRESH|exact RANGE|].
      rewrite (FRAME cache ltac:(cbn; auto)); exact CACHE. }
    exists (double_reduction_nest_exit (reduction_nest_iterators description) count candidate_after).
    split.
    + unfold double_reduction_guarded_code; eapply exec_Sseq_1 with
        (le1:=prepared) (m1:=memory) (t1:=E0) (t2:=E0); [exact CAPTURE|].
      eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true); [constructor; exact FLAG|reflexivity|].
      eapply exec_Sseq_1 with (le1:=candidate_after) (m1:=final) (t1:=E0) (t2:=E0); eassumption.
    + eapply temp_agree_trans; [exact EXIT|rewrite SET].
      apply double_reduction_exit_agree.
      eapply temp_agree_weaken; [|exact FRAME]; intros key MEMBER; cbn; auto.
  - exists prepared_after; split; [|exact EXIT].
    unfold double_reduction_guarded_code; eapply exec_Sseq_1 with
      (le1:=prepared) (m1:=memory) (t1:=E0) (t2:=E0); [exact CAPTURE|].
    eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false); [constructor; exact FLAG|reflexivity|exact FALLBACK].
Qed.

Print Assumptions checked_double_reindexed_tiled_reduction_guarded_execution.
