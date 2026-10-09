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
  GuardMemoryDoubleReductionNestExitCode GuardMemoryDoubleInitializedLowering GuardMemoryLongRangeCapture.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition compile_double_reduction_candidate description cache flag limit live pool (generated : DoubleAssignmentIRs.Loop.t) :=
  compile_double_tensor_loop (double_source_instruction_layouts (reduction_nest_instruction description)) [cache]
    [DoubleNested.A.Interval 0 limit] (flag::live) pool (fst (fst generated)).
Theorem compiled_double_reduction_candidate_execution description cache flag limit live pool generated code
  fe ge locals temps memory count final :
  double_tensor_static ge locals (double_source_instruction_layouts (reduction_nest_instruction description)) ->
  compile_double_reduction_candidate description cache flag limit live pool generated=Some code ->
  signed_range (Z.of_nat count) -> Z.of_nat count<=limit ->
  temps ! cache=Some (Vint (Int.repr (Z.of_nat count))) ->
  DoubleAssignmentIRs.Loop.loop_semantics (fst (fst generated)) [Z.of_nat count]
    (RuntimeState (global_double_locations ge (double_source_instruction_layouts (reduction_nest_instruction description))) memory)
    (RuntimeState (global_double_locations ge (double_source_instruction_layouts (reduction_nest_instruction description))) final) ->
  exists candidate_after,
    temp_agree ([cache;flag]++live) temps candidate_after /\
    exec_stmt fe ge locals temps memory code E0 candidate_after final Out_normal.
Proof.
  intros STATIC CODE RANGE UPPER CACHE MODEL.
  destruct (@compile_double_tensor_loop_correct fe ge locals (double_source_instruction_layouts (reduction_nest_instruction description)) STATIC
    [cache] [DoubleNested.A.Interval 0 limit] (flag::live) pool (fst (fst generated)) code [Z.of_nat count]
    temps _ _ memory CODE (@double_initialized_cache_view cache count temps RANGE CACHE)
    (@double_initialized_candidate_bounds limit count UPPER) MODEL ltac:(split; reflexivity))
    as [candidate_after [target_memory [[LOCATIONS SAME] [FRAME RUN]]]].
  cbn [runtime_memory] in SAME; subst target_memory; exists candidate_after; auto.
Qed.
Definition double_reduction_guarded_code source description cache flag limit code :=
  Ssequence (memory_long_range_capture (reduction_nest_header description) cache flag limit)
    (Sifthenelse (Etempvar flag memory_signed_int_type)
      (Ssequence code (double_reduction_exit_code (reduction_nest_iterators description) cache)) source).
Theorem checked_double_reduction_guarded_execution p source description limit schedule swaps generated
  cache flag live pool code fe ge locals temps memory after final :
  checked_double_reduction_raw_nest p [] source=Some description ->
  double_reduction_entry_bounds_check limit description=true ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_reduction_globals description) locals ->
  double_tensor_static ge locals (double_source_instruction_layouts (reduction_nest_instruction description)) ->
  cache<>flag -> ~ In cache (reduction_nest_iterators description) ->
  (forall key, In key (statement_temps source++live) -> ~ In key [cache;flag]) ->
  mayReturn (checked_double_uniform_prepared_loop_progress schedule swaps
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
    { apply (proj1 (@checked_double_uniform_prepared_loop_progress_at schedule swaps
        (double_reduction_pipeline_request description) generated [Z.of_nat count]
        (RuntimeState (global_double_locations ge (double_source_instruction_layouts (reduction_nest_instruction description))) memory)
        (RuntimeState (global_double_locations ge (double_source_instruction_layouts (reduction_nest_instruction description))) final)
        PIPELINE eq_refl ltac:(apply global_double_locations_nonalias))); exact MODEL. }
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

Print Assumptions compiled_double_reduction_candidate_execution.
Print Assumptions checked_double_reduction_guarded_execution.
