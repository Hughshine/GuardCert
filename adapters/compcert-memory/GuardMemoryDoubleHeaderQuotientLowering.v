From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightTempFootprint
  ClightGlobalScope ClightRegionProgress.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLongControl GuardMemoryDoubleLocations
  GuardMemoryDoubleAssignment GuardMemoryDoubleTensorBackend GuardMemoryDoubleNestedBackend
  GuardMemoryDoublePolyhedral GuardMemoryDoubleSourceInstruction GuardMemoryDoubleReductionNestData
  GuardMemoryDoubleReductionNestModel GuardMemoryDoubleReductionNestEntry GuardMemoryDoubleReductionNestCapture
  GuardMemoryDoubleReductionNestExitCode GuardMemoryDoubleInitializedLowering GuardMemoryLongRangeCapture
  GuardMemoryDoubleQuotientPrepared GuardMemoryDoubleQuotientLowering
  GuardMemoryDoubleReductionQuotientLowering GuardMemoryDoubleHeaderNestData GuardMemoryDoubleHeaderNestEntry
  GuardMemoryDoubleHeaderNestCapture.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem checked_double_header_quotient_guarded_execution p source description limit divisor phase adapt choices generated
  cache flag quotient live pool capture quotient_range code fe ge locals temps memory after final :
  checked_double_header_raw_nest p [] source=Some description ->
  double_header_nest_entry_bounds_check limit description=true ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_reduction_globals description) locals ->
  double_tensor_static ge locals (double_source_instruction_layouts (reduction_nest_instruction description)) ->
  cache<>flag -> ~ In cache (reduction_nest_iterators description) ->
  (forall key, In key (statement_temps source++live) -> ~ In key [cache;flag]) ->
  ~ In quotient (cache::flag::live) -> 0<divisor ->
  compile_double_ceil_capture cache quotient limit divisor=Some (capture,quotient_range) ->
  mayReturn (checked_double_quotient_tiled_prepared_loop phase adapt choices limit divisor quotient
    (double_header_pipeline_request description)) (Some generated) ->
  compile_double_quotient_candidate
    (double_source_instruction_layouts (reduction_nest_instruction description)) cache flag quotient limit quotient_range
    live pool generated=Some code ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists target_after,
    exec_stmt fe ge locals temps memory
      (double_reduction_quotient_guarded_code source description cache flag limit capture code)
      E0 target_after final Out_normal /\ temp_agree live after target_after.
Proof.
  intros CHECK BOUNDS GLOBAL LOCAL STATIC DISTINCT CACHE_FRESH PRIVATE QFRESH POSITIVE
    QUOTIENT PIPELINE CODE SOURCE.
  pose proof (@double_header_nest_checked_limit limit description BOUNDS) as LIMIT.
  destruct (@checked_double_header_capture_model p source description limit fe ge locals temps memory
    cache flag live after final CHECK BOUNDS GLOBAL LOCAL DISTINCT PRIVATE SOURCE)
    as [accepted [prepared [prepared_after [CAPTURE [FLAG [ENTRY [FALLBACK [EXIT FACTS]]]]]]]].
  destruct accepted.
  - destruct (FACTS eq_refl) as [count [UPPER [CACHE [MODEL SET]]]].
    assert (RANGE : signed_range (Z.of_nat count))
      by (unfold signed_range; change (-2147483648<=Z.of_nat count<=2147483647);
          change (0<limit<=2147483647) in LIMIT; lia).
    set (value := (Z.of_nat count+divisor-1)/divisor).
    set (captured := PTree.set quotient (Vint (Int.repr value)) prepared).
    destruct (@compiled_double_ceil_capture_execution cache quotient flag limit divisor capture quotient_range
      fe ge locals prepared memory count live QUOTIENT RANGE UPPER CACHE QFRESH)
      as [QCAPTURE [VIEW [WITHIN [RELATION QFRAME]]]].
    assert (CANDIDATE_MODEL : DBL.loop_semantics (fst (fst generated)) [value;Z.of_nat count]
      (RuntimeState (global_double_locations ge (double_source_instruction_layouts (reduction_nest_instruction description))) memory)
      (RuntimeState (global_double_locations ge (double_source_instruction_layouts (reduction_nest_instruction description))) final)).
    { apply (@checked_double_quotient_tiled_prepared_loop_at phase adapt choices limit divisor quotient
        (double_header_pipeline_request description) generated [Z.of_nat count] value
        (RuntimeState (global_double_locations ge (double_source_instruction_layouts (reduction_nest_instruction description))) memory)
        (RuntimeState (global_double_locations ge (double_source_instruction_layouts (reduction_nest_instruction description))) final)
        PIPELINE eq_refl ltac:(apply global_double_locations_nonalias) POSITIVE ltac:(cbn; lia)).
      - exact (proj1 (@DoubleQuotientModel.quotient_relation_exact
          (double_ceil_numerator divisor) divisor [Z.of_nat count] value POSITIVE) RELATION).
      - exact MODEL. }
    destruct (@compiled_double_quotient_candidate_execution
      (double_source_instruction_layouts (reduction_nest_instruction description)) cache flag quotient limit quotient_range
      live pool generated code fe ge locals captured memory (Z.of_nat count) value final STATIC CODE VIEW WITHIN CANDIDATE_MODEL)
      as [candidate_after [CFRAME CANDIDATE]].
    assert (FRAME : temp_agree (cache::flag::live) prepared candidate_after).
    { eapply temp_agree_trans; [exact QFRAME|].
      eapply temp_agree_weaken; [|exact CFRAME]; intros key MEMBER; cbn in *; tauto. }
    assert (RESTORE : exec_stmt fe ge locals candidate_after final
      (double_reduction_exit_code (reduction_nest_iterators description) cache) E0
      (double_reduction_nest_exit (reduction_nest_iterators description) count candidate_after)
      final Out_normal).
    { apply double_reduction_exit_code_execution; [exact CACHE_FRESH|exact RANGE|].
      rewrite (FRAME cache ltac:(cbn; auto)); exact CACHE. }
    exists (double_reduction_nest_exit (reduction_nest_iterators description) count candidate_after).
    split.
    + unfold double_reduction_quotient_guarded_code.
      eapply exec_Sseq_1 with (le1:=prepared) (m1:=memory) (t1:=E0) (t2:=E0); [exact CAPTURE|].
      eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true); [constructor; exact FLAG|reflexivity|].
      eapply exec_Sseq_1 with (le1:=captured) (m1:=memory) (t1:=E0) (t2:=E0); [exact QCAPTURE|].
      eapply exec_Sseq_1 with (le1:=candidate_after) (m1:=final) (t1:=E0) (t2:=E0); eassumption.
    + eapply temp_agree_trans; [exact EXIT|rewrite SET].
      apply double_reduction_exit_agree.
      eapply temp_agree_weaken; [|exact FRAME]; intros key MEMBER; cbn; auto.
  - exists prepared_after; split; [|exact EXIT].
    unfold double_reduction_quotient_guarded_code.
    eapply exec_Sseq_1 with (le1:=prepared) (m1:=memory) (t1:=E0) (t2:=E0); [exact CAPTURE|].
    eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false); [constructor; exact FLAG|reflexivity|exact FALLBACK].
Qed.


Print Assumptions checked_double_header_quotient_guarded_execution.
