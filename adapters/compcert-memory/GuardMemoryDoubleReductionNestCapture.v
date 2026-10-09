From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightTempFrame ClightTempFootprint ClightProjectedExecution ClightGlobalScope ClightRegionProgress.
From GuardInterface Require Import ClightCheckPlanFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDoubleLocations GuardMemoryDoubleSourceInstruction
  GuardMemoryDoubleReductionNestData GuardMemoryDoubleReductionNestEntry GuardMemoryDoubleReductionNestModel
  GuardMemoryDoublePolyhedral GuardMemoryLongRangeCapture GuardMemoryLongControl.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem double_reduction_capture_public_frame fe ge locals temps memory header cache flag limit live trace after final outcome :
  (forall key, In key live -> ~ In key [cache;flag]) ->
  exec_stmt fe ge locals temps memory (memory_long_range_capture header cache flag limit) trace after final outcome ->
  temp_agree live temps after.
Proof. intros PRIVATE RUN; eapply structured_temp_frame; [apply memory_long_range_capture_writes|exact PRIVATE|exact RUN]. Qed.
Theorem checked_double_reduction_capture_model p source description limit fe ge locals temps memory
  cache flag live after final :
  checked_double_reduction_raw_nest p [] source=Some description -> double_reduction_entry_bounds_check limit description=true ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_reduction_globals description) locals ->
  cache<>flag -> (forall key, In key (statement_temps source++live) -> ~ In key [cache;flag]) ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists (accepted : bool) prepared prepared_after,
    exec_stmt fe ge locals temps memory (memory_long_range_capture (reduction_nest_header description) cache flag limit)
      E0 prepared memory Out_normal /\
    prepared ! flag=Some (Vint (if accepted then Int.one else Int.zero)) /\
    temp_agree live temps prepared /\ exec_stmt fe ge locals prepared memory source E0 prepared_after final Out_normal /\
    temp_agree live after prepared_after /\
    (accepted=true -> exists count,
      Z.of_nat count<=limit /\ prepared ! cache=Some (Vint (Int.repr (Z.of_nat count))) /\
      DoubleAssignmentIRs.Loop.loop_semantics (double_reduction_pipeline_model description) [Z.of_nat count]
        (RuntimeState (global_double_locations ge (double_source_instruction_layouts (reduction_nest_instruction description))) memory)
        (RuntimeState (global_double_locations ge (double_source_instruction_layouts (reduction_nest_instruction description))) final) /\
      prepared_after=double_reduction_nest_exit (reduction_nest_iterators description) count prepared).
Proof.
  intros CHECK BOUNDS GLOBAL LOCAL DISTINCT PRIVATE SOURCE.
  pose proof (@double_reduction_checked_limit limit description BOUNDS) as LIMIT.
  destruct (@checked_double_reduction_entry_header p [] source description ge locals CHECK GLOBAL LOCAL) as [header_block HEADER].
  destruct (@checked_double_reduction_raw_header_license p [] source description fe ge locals temps memory
    header_block after final CHECK HEADER SOURCE) as [word LOAD].
  set (accepted := memory_long_range_accept word limit).
  set (prepared := memory_long_range_captured temps cache flag word limit).
  assert (CAPTURE : exec_stmt fe ge locals temps memory
    (memory_long_range_capture (reduction_nest_header description) cache flag limit) E0 prepared memory Out_normal).
  { exact (@memory_long_range_capture_execution fe ge locals temps memory (reduction_nest_header description)
      header_block cache flag word limit HEADER LOAD ltac:(lia)). }
  assert (FRAME : temp_agree (statement_temps source++live) temps prepared).
  { eapply double_reduction_capture_public_frame; [exact PRIVATE|exact CAPTURE]. }
  destruct (@structured_execution_temp_transport fe ge locals temps memory source E0 after final Out_normal SOURCE
    (statement_temps source++live) prepared (statement_temps source)
    (@check_plan_frameable_writes source (@checked_double_reduction_raw_frameable p [] source description CHECK))
    ltac:(unfold statement_scope; intros key MEMBER; apply in_or_app; left; exact MEMBER) FRAME)
    as [prepared_after [PREPARED EXIT]].
  exists accepted,prepared,prepared_after; split; [exact CAPTURE|split; [apply PTree.gss|split]].
  - eapply temp_agree_weaken; [intros key MEMBER; apply in_or_app; right; exact MEMBER|exact FRAME].
  - split; [exact PREPARED|split].
    + eapply temp_agree_weaken; [intros key MEMBER; apply in_or_app; right; exact MEMBER|exact EXIT].
    + intro ACCEPT; unfold accepted in ACCEPT.
      pose proof (proj1 (memory_long_range_accept_spec word limit) ACCEPT) as RANGE.
      assert (COUNT : Z.of_nat (Z.to_nat (Int64.signed word))=Int64.signed word) by (apply Z2Nat.id; lia).
      assert (CACHE : prepared ! cache=Some (Vint (Int.repr (Z.of_nat (Z.to_nat (Int64.signed word)))))).
      { unfold prepared,memory_long_range_captured; rewrite ACCEPT,COUNT; rewrite PTree.gso by congruence.
        rewrite PTree.gss; f_equal; f_equal.
        exact (proj1 (@memory_long_accepted_int_exact word limit ltac:(lia) ACCEPT)). }
      assert (COUNT_LOAD : Mem.load Mint64 memory header_block 0=
        Some (Vlong (Int64.repr (Z.of_nat (Z.to_nat (Int64.signed word)))))).
      { rewrite COUNT,Int64.repr_signed; exact LOAD. }
      destruct (proj1 (@checked_double_reduction_raw_pipeline_execution p source description limit fe ge locals
        header_block (Z.to_nat (Int64.signed word)) prepared memory prepared_after final CHECK BOUNDS GLOBAL LOCAL
        HEADER ltac:(rewrite COUNT; lia) COUNT_LOAD) PREPARED) as [MODEL SET].
      exists (Z.to_nat (Int64.signed word)); split; [rewrite COUNT; lia|split; [exact CACHE|split; assumption]].
Qed.

Print Assumptions double_reduction_capture_public_frame.
Print Assumptions checked_double_reduction_capture_model.
