From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightTempFrame ClightTempFootprint ClightRegionProgress ClightGlobalScope.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDoubleLocations
  GuardMemoryDoubleSourceInstruction GuardMemoryDoubleInitializedReductionData
  GuardMemoryDoubleInitializedReductionSource GuardMemoryDoubleInitializedNestData
  GuardMemoryDoubleInitializedNestExit GuardMemoryDoubleInitializedNestSyntax
  GuardMemoryDoubleInitializedNestSource GuardMemoryDoubleInitializedNestModel
  GuardMemoryDoubleInitializedRawNest GuardMemoryDoubleInitializedBounds
  GuardMemoryDoubleInitializedEntry GuardMemoryDoubleInitializedPipeline
  GuardMemoryDoublePolyhedral GuardMemoryLongRangeCapture.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma double_initialized_checked_limit limit description :
  double_initialized_entry_bounds_check limit description=true -> 0<limit<=Int.max_signed.
Proof.
  unfold double_initialized_entry_bounds_check; intro CHECK.
  apply andb_true_iff in CHECK as [CHECK _]; apply andb_true_iff in CHECK as [CHECK _].
  apply andb_true_iff in CHECK as [POSITIVE MAXIMUM]; apply Z.ltb_lt in POSITIVE;
    apply Z.leb_le in MAXIMUM; split; assumption.
Qed.
Theorem checked_double_initialized_entry_header p source outers description ge locals :
  checked_double_initialized_raw_nest p [] source=Some (outers,description) ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_initialized_reduction_globals description) locals ->
  exists header_block, double_global_binding ge locals (initialized_reduction_header description) header_block.
Proof.
  intros CHECK GLOBAL LOCAL.
  destruct (@checked_double_initialized_raw_nest_sound p [] source outers description CHECK) as [RAW [CANONICAL EQUIV]].
  destruct (@checked_double_initialized_nest_sound p [] (double_initialized_nest_code outers description)
    outers description CANONICAL) as [CODE [LEAF FRESH]].
  eapply checked_double_initialized_reduction_header_binding; eassumption.
Qed.
Theorem checked_double_initialized_raw_pipeline_execution p source outers description limit fe ge locals
  header_block count temps memory after final :
  checked_double_initialized_raw_nest p [] source=Some (outers,description) ->
  double_initialized_entry_bounds_check limit description=true ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_initialized_reduction_globals description) locals ->
  double_global_binding ge locals (initialized_reduction_header description) header_block ->
  Z.of_nat count<=limit -> Mem.load Mint64 memory header_block 0=Some (Vlong (Int64.repr (Z.of_nat count))) ->
  (exec_stmt fe ge locals temps memory source E0 after final Out_normal <->
   DoubleAssignmentIRs.Loop.loop_semantics (double_initialized_pipeline_model outers description) [Z.of_nat count]
     (RuntimeState (global_double_locations ge (double_initialized_reduction_layouts description)) memory)
     (RuntimeState (global_double_locations ge (double_initialized_reduction_layouts description)) final) /\
   after=double_initialized_nest_exit outers (initialized_reduction_iterator description) count temps).
Proof.
  intros CHECK BOUNDS GLOBAL LOCAL HEADER UPPER LOAD.
  pose proof (@double_initialized_checked_limit limit description BOUNDS) as LIMIT.
  destruct (@checked_double_initialized_raw_nest_sound p [] source outers description CHECK) as [RAW [CANONICAL EQUIV]].
  rewrite (@EQUIV fe ge locals temps memory E0 after final Out_normal).
  pose proof (@checked_double_initialized_nest_source_model p fe ge locals header_block count GLOBAL
    ltac:(change (Z.of_nat count<=9223372036854775807); change (0<limit<=2147483647) in LIMIT; lia)
    [] (fun _=>0) (double_initialized_nest_code outers description) outers description temps memory after final
    CANONICAL LOCAL HEADER
    (@double_initialized_entry_bounds_check_ready p source outers description limit ge locals count
      CHECK BOUNDS GLOBAL LOCAL UPPER) ltac:(split; [intros key MEMBER; contradiction|exact LOAD])) as MODEL.
  rewrite double_initialized_pipeline_model_execution in MODEL; exact MODEL.
Qed.
Theorem checked_double_initialized_capture_model p source iterator rest description limit fe ge locals temps memory
  cache flag live after final :
  checked_double_initialized_raw_nest p [] source=Some (iterator::rest,description) ->
  double_initialized_entry_bounds_check limit description=true ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_initialized_reduction_globals description) locals ->
  cache<>flag -> (forall key, In key (statement_temps source++live) -> ~ In key [cache;flag]) ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists (accepted : bool) prepared prepared_after,
    exec_stmt fe ge locals temps memory
      (memory_long_range_capture (initialized_reduction_header description) cache flag limit)
      E0 prepared memory Out_normal /\
    prepared ! flag=Some (Vint (if accepted then Int.one else Int.zero)) /\
    temp_agree live temps prepared /\
    exec_stmt fe ge locals prepared memory source E0 prepared_after final Out_normal /\
    temp_agree live after prepared_after /\
    (accepted=true -> exists count,
      Z.of_nat count<=limit /\ prepared ! cache=Some (Vint (Int.repr (Z.of_nat count))) /\
      DoubleAssignmentIRs.Loop.loop_semantics (double_initialized_pipeline_model (iterator::rest) description) [Z.of_nat count]
        (RuntimeState (global_double_locations ge (double_initialized_reduction_layouts description)) memory)
        (RuntimeState (global_double_locations ge (double_initialized_reduction_layouts description)) final) /\
      prepared_after=double_initialized_nest_exit (iterator::rest) (initialized_reduction_iterator description) count prepared).
Proof.
  intros CHECK BOUNDS GLOBAL LOCAL DISTINCT PRIVATE SOURCE.
  pose proof (@double_initialized_checked_limit limit description BOUNDS) as LIMIT.
  destruct (@checked_double_initialized_entry_header p source (iterator::rest) description ge locals CHECK GLOBAL LOCAL)
    as [header_block HEADER].
  destruct (@checked_double_initialized_raw_source_capture p [] source iterator rest description fe ge locals temps memory
    header_block cache flag limit after final CHECK HEADER ltac:(lia) DISTINCT SOURCE)
    as [accepted [prepared [CAPTURE [FLAG FACTS]]]].
  destruct (@checked_double_initialized_capture_source_transport p [] source (iterator::rest) description
    fe ge locals temps memory cache flag limit live prepared after final CHECK PRIVATE CAPTURE SOURCE)
    as [prepared_after [PREPARED EXIT]].
  exists accepted,prepared,prepared_after; split; [exact CAPTURE|split; [exact FLAG|split]].
  - eapply double_initialized_capture_public_frame; [|exact CAPTURE].
    intros key MEMBER; apply PRIVATE; apply in_or_app; right; exact MEMBER.
  - split; [exact PREPARED|split; [exact EXIT|intro TRUE]].
    destruct (FACTS TRUE) as [count [RANGE [CACHE LOAD]]].
    destruct (proj1 (@checked_double_initialized_raw_pipeline_execution p source (iterator::rest) description limit
      fe ge locals header_block count prepared memory prepared_after final CHECK BOUNDS GLOBAL LOCAL HEADER RANGE LOAD)
      PREPARED) as [MODEL SET].
    exists count; repeat split; assumption.
Qed.

Print Assumptions double_initialized_checked_limit.
Print Assumptions checked_double_initialized_entry_header.
Print Assumptions checked_double_initialized_raw_pipeline_execution.
Print Assumptions checked_double_initialized_capture_model.
