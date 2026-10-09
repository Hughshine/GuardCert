From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightLoopSyntax ClightTempFrame ClightTempFootprint
  ClightProjectedExecution.
From GuardInterface Require Import ClightCheckPlanFrame.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleAssignmentFactory
  GuardMemoryDoubleSourceInstruction GuardMemoryDoubleInitializedReductionData
  GuardMemoryDoubleInitializedNestData GuardMemoryDoubleInitializedNestSyntax
  GuardMemoryDoubleInitializedRawNest GuardMemoryLongRawLoadedProgress
  GuardMemoryLongControl GuardMemoryLongLoopControl GuardMemoryDoubleMatmulLoops
  GuardMemoryLongHeaderLicense GuardMemoryLongRangeCapture.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Only a nonempty outer nest licenses reading its header before its body.
    The original execution is a proof premise, not runtime pre-execution. *)
Theorem checked_double_initialized_raw_header_license p controls source iterator rest description
  fe ge locals temps memory header_block after final :
  checked_double_initialized_raw_nest p controls source=Some (iterator::rest,description) ->
  double_global_binding ge locals (initialized_reduction_header description) header_block ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists word, Mem.load Mint64 memory header_block 0=Some (Vlong word).
Proof.
  intros CHECK HEADER SOURCE.
  destruct (@checked_double_initialized_raw_nest_sound p controls source (iterator::rest) description CHECK)
    as [RAW [CANONICAL EQUIV]].
  destruct (@checked_double_initialized_nest_sound p controls
    (double_initialized_nest_code (iterator::rest) description) (iterator::rest) description CANONICAL)
    as [CODE [LEAF FRESH]].
  cbn [double_initialized_nest_fresh] in FRESH; destruct FRESH as [HEAD TAIL].
  assert (CHILD : checked_double_initialized_nest p (controls++[iterator])
    (double_initialized_nest_code rest description)=Some (rest,description)).
  { apply checked_double_initialized_nest_complete; [exact TAIL|].
    replace ((controls++[iterator])++rest) with (controls++iterator::rest) by (rewrite <- app_assoc; reflexivity).
    exact LEAF. }
  apply EQUIV in SOURCE; cbn [double_initialized_nest_code] in SOURCE.
  destruct (@memory_global_long_initialized_license fe ge locals temps memory iterator
    (initialized_reduction_header description) header_block (double_initialized_nest_code rest description)
    after final HEADER (@checked_double_initialized_nest_normal p (controls++[iterator])
      (double_initialized_nest_code rest description) rest description CHILD) SOURCE) as [word [LOAD NEXT]].
  exists word; exact LOAD.
Qed.

Theorem checked_double_initialized_raw_source_capture p controls source iterator rest description
  fe ge locals temps memory header_block cache flag limit after final :
  checked_double_initialized_raw_nest p controls source=Some (iterator::rest,description) ->
  double_global_binding ge locals (initialized_reduction_header description) header_block ->
  0<=limit<=Int.max_signed -> cache<>flag ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists (accepted : bool) prepared,
    exec_stmt fe ge locals temps memory
      (memory_long_range_capture (initialized_reduction_header description) cache flag limit)
      E0 prepared memory Out_normal /\
    prepared ! flag=Some (Vint (if accepted then Int.one else Int.zero)) /\
    (accepted=true -> exists count,
      Z.of_nat count<=limit /\
      prepared ! cache=Some (Vint (Int.repr (Z.of_nat count))) /\
      Mem.load Mint64 memory header_block 0=Some (Vlong (Int64.repr (Z.of_nat count)))).
Proof.
  intros CHECK HEADER LIMIT DISTINCT SOURCE.
  destruct (@checked_double_initialized_raw_header_license p controls source iterator rest description
    fe ge locals temps memory header_block after final CHECK HEADER SOURCE) as [word LOAD].
  exists (memory_long_range_accept word limit),(memory_long_range_captured temps cache flag word limit).
  split; [eapply memory_long_range_capture_execution; eassumption|].
  split; [apply PTree.gss|intro ACCEPT].
  pose proof (proj1 (memory_long_range_accept_spec word limit) ACCEPT) as RANGE.
  assert (COUNT : Z.of_nat (Z.to_nat (Int64.signed word))=Int64.signed word) by (apply Z2Nat.id; lia).
  exists (Z.to_nat (Int64.signed word)); rewrite COUNT; split; [lia|split].
  - unfold memory_long_range_captured; rewrite ACCEPT; rewrite PTree.gso by congruence.
    rewrite PTree.gss; f_equal; f_equal.
    exact (proj1 (@memory_long_accepted_int_exact word limit LIMIT ACCEPT)).
  - rewrite Int64.repr_signed; exact LOAD.
Qed.

Theorem double_initialized_capture_public_frame fe ge locals temps memory description cache flag limit
  live trace after final outcome :
  (forall key, In key live -> ~ In key [cache;flag]) ->
  exec_stmt fe ge locals temps memory (memory_long_range_capture (initialized_reduction_header description)
    cache flag limit) trace after final outcome -> temp_agree live temps after.
Proof. intros PRIVATE RUN; eapply structured_temp_frame; [apply memory_long_range_capture_writes|exact PRIVATE|exact RUN]. Qed.

Lemma checked_double_initialized_raw_frameable p controls source outers description :
  checked_double_initialized_raw_nest p controls source=Some (outers,description) ->
  check_plan_frameable source=true.
Proof.
  intro CHECK; destruct (@checked_double_initialized_raw_nest_sound p controls source outers description CHECK)
    as [RAW [CANONICAL EQUIV]].
  destruct (@checked_double_initialized_nest_sound p controls (double_initialized_nest_code outers description)
    outers description CANONICAL) as [CODE [LEAF FRESH]].
  destruct (@checked_double_initialized_reduction_sound p (controls++outers)
    (double_initialized_reduction_code description) description LEAF) as [_ [IC [BC STATIC]]].
  destruct (@checked_double_source_instruction_sound p (controls++outers) (initialized_reduction_initializer description)
    (initialized_reduction_initial_instruction description) IC) as [IDEC _].
  destruct (@checked_double_source_instruction_sound p ((controls++outers)++[initialized_reduction_iterator description])
    (initialized_reduction_body description) (initialized_reduction_body_instruction description) BC) as [BDEC _].
  destruct (@decoded_double_assignment_shape (initialized_reduction_initializer description)
    (double_source_assignment (initialized_reduction_initial_instruction description)) IDEC) as [rhs [INITIAL TYPE]].
  destruct (@decoded_double_assignment_shape (initialized_reduction_body description)
    (double_source_assignment (initialized_reduction_body_instruction description)) BDEC) as [rhs' [BODY TYPE']].
  rewrite RAW; clear CHECK RAW CANONICAL EQUIV CODE LEAF FRESH IC BC STATIC IDEC BDEC.
  induction outers; cbn [double_initialized_raw_nest_code];
    unfold long_raw_initialized_loop,long_raw_loaded_loop; cbn [check_plan_frameable];
    rewrite ?INITIAL,?BODY,?IHouters; reflexivity.
Qed.

Theorem checked_double_initialized_capture_source_transport p controls source outers description
  fe ge locals temps memory cache flag limit live prepared after final :
  checked_double_initialized_raw_nest p controls source=Some (outers,description) ->
  (forall key, In key (statement_temps source++live) -> ~ In key [cache;flag]) ->
  exec_stmt fe ge locals temps memory (memory_long_range_capture (initialized_reduction_header description)
    cache flag limit) E0 prepared memory Out_normal ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists prepared_after,
    exec_stmt fe ge locals prepared memory source E0 prepared_after final Out_normal /\
    temp_agree live after prepared_after.
Proof.
  intros CHECK PRIVATE CAPTURE SOURCE.
  pose proof (@checked_double_initialized_raw_frameable p controls source outers description CHECK) as FRAMEABLE.
  assert (FRAME : temp_agree (statement_temps source++live) temps prepared)
    by (eapply double_initialized_capture_public_frame; eassumption).
  destruct (@structured_execution_temp_transport fe ge locals temps memory source E0 after final Out_normal SOURCE
    (statement_temps source++live) prepared (statement_temps source) (@check_plan_frameable_writes source FRAMEABLE)
    ltac:(unfold statement_scope; intros key MEMBER; apply in_or_app; left; exact MEMBER) FRAME)
    as [prepared_after [RUN PUBLIC]].
  exists prepared_after; split; [exact RUN|].
  eapply temp_agree_weaken; [intros key MEMBER; apply in_or_app; right; exact MEMBER|exact PUBLIC].
Qed.

Print Assumptions checked_double_initialized_raw_header_license.
Print Assumptions checked_double_initialized_raw_source_capture.
Print Assumptions double_initialized_capture_public_frame.
Print Assumptions checked_double_initialized_raw_frameable.
Print Assumptions checked_double_initialized_capture_source_transport.
