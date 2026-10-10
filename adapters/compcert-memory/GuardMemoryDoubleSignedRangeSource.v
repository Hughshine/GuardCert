From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightGuard ClightRegionProgress ClightCondition ClightCountedLoop ClightGlobalScope ClightLoopSyntax ClightSkipPrefix.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryValueInstr GuardMemoryDoubleLocations
  GuardMemoryDoubleSourceInstruction GuardMemoryDoubleSourceTransport GuardMemoryDoubleSourceLoopModel
  GuardMemoryDoubleInitializedReductionSource GuardMemoryDoubleSourceResolvedPoints
  GuardMemoryDoubleNestControl GuardMemoryDoubleHeaderFrame GuardMemoryLongControl GuardMemoryLongLoopControl
  GuardMemoryLongSourceAffine GuardMemoryLongRangeSource GuardMemoryLongRangeHeader
  GuardMemoryLongExpressionCapture GuardMemoryLongRangeCaptureSource GuardMemoryDoubleRangeModel
  GuardMemoryLongRawLoadedProgress GuardMemoryLongProgressControl.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition double_signed_range_entry controls valuation header_block input temps memory :=
  double_source_prefix_words controls valuation temps /\ Mem.load Mint64 memory header_block 0=Some (Vlong input).

(** A checked floating assignment retains its IEEE operation tree and actual
    Mem actions. The remaining point-resolution, scope and arithmetic receipts
    are language/domain premises for a later region factory to construct. *)
Theorem checked_double_signed_offset_source_model p controls body description valuation fe ge locals
  iterator header header_block input offset start upper temps memory after final :
  checked_double_source_instruction p (controls++[iterator]) body=Some description ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_source_instruction_globals description) locals ->
  double_global_binding ge locals header header_block ->
  fst (value_instruction_write (double_source_instruction_model description))<>header ->
  ~ In iterator controls -> Int.min_signed<=start<=Int.max_signed ->
  Int64.min_signed<=upper<=Int64.max_signed -> upper=Int64.signed input-Int.signed offset ->
  (forall value, start<=value<upper ->
    double_source_instruction_resolved description (map valuation controls++[value]) ge
      (double_source_instruction_layouts description)) ->
  double_signed_range_entry controls valuation header_block input temps memory ->
  (exec_stmt fe ge locals temps memory
    (memory_long_from_loop iterator
      (Ecast (Econst_int (Int.repr start) memory_signed_int_type) memory_long_type)
      (Ebinop Olt (Etempvar iterator memory_long_type) (memory_long_offset_bound header offset) memory_signed_int_type) body)
    E0 after final Out_normal <->
   SL.loop_semantics (double_signed_range_model (double_source_instruction_model description) start (length controls))
     (rev (map valuation controls)++[upper])
     (RuntimeState (global_double_locations ge (double_source_instruction_layouts description)) memory)
     (RuntimeState (global_double_locations ge (double_source_instruction_layouts description)) final) /\
   after=PTree.set iterator (Vlong (Int64.repr (Z.max start upper))) temps).
Proof.
  intros LEAF GLOBAL LOCAL BIND WRITE FRESH START UPPER MATH READY ENTRY.
  set (physical := fun value first last => double_source_model_point (double_source_instruction_model description)
    (map valuation controls++[value])
    (RuntimeState (global_double_locations ge (double_source_instruction_layouts description)) first)
    (RuntimeState (global_double_locations ge (double_source_instruction_layouts description)) last)).
  assert (BRIDGE : forall value le m le' m', start<=value<upper ->
    double_signed_range_entry controls valuation header_block input le m ->
    le ! iterator=Some (Vlong (Int64.repr value)) ->
    (exec_stmt fe ge locals le m body E0 le' m' Out_normal <-> physical value m m' /\ le'=le)).
  { intros value le m le' m' RANGE [WORDS LOAD] VALUE.
    pose proof (@double_source_control_values controls valuation iterator value FRESH) as VALUES.
    pose proof (@double_source_control_words controls valuation iterator value le FRESH WORDS VALUE) as EXTENDED.
    destruct (READY value RANGE) as [write [reads [WR RR]]].
    rewrite <- VALUES in WR,RR.
    pose proof (@checked_double_source_instruction_execution_iff p (controls++[iterator]) body description
      (double_source_control_value valuation iterator value) fe ge locals le m write reads m'
      LEAF GLOBAL LOCAL EXTENDED WR RR) as POINT.
    assert (BODY : exec_stmt fe ge locals le m body E0 le m' Out_normal <-> physical value m m').
    { unfold physical,double_source_model_point; rewrite <- VALUES; exact POINT. }
    split.
    - intro RUN; destruct (@checked_double_source_assignment_effects p (controls++[iterator]) body description
        fe ge locals le m E0 le' m' Out_normal LEAF RUN) as [_ [SAME NORMAL]].
      subst le'; split; [apply BODY; exact RUN|reflexivity].
    - intros [MODEL SAME]; subst le'; apply BODY; exact MODEL. }
  assert (SET_ENTRY : forall le m value, double_signed_range_entry controls valuation header_block input le m ->
    double_signed_range_entry controls valuation header_block input (PTree.set iterator (Vlong (Int64.repr value)) le) m).
  { intros le m value [WORDS LOAD]; split; [|exact LOAD].
    intros key MEMBER; rewrite PTree.gso by (intro SAME; subst; contradiction); apply WORDS; exact MEMBER. }
  assert (BODY_ENTRY : forall value le m le' m', start<=value<upper ->
    double_signed_range_entry controls valuation header_block input le m ->
    le ! iterator=Some (Vlong (Int64.repr value)) -> exec_stmt fe ge locals le m body E0 le' m' Out_normal ->
    double_signed_range_entry controls valuation header_block input le' m').
  { intros value le m le' m' RANGE INV VALUE RUN.
    destruct (proj1 (@BRIDGE value le m le' m' RANGE INV VALUE) RUN) as [MODEL SAME]; subst le'.
    destruct INV as [WORDS LOAD]; split; [exact WORDS|].
    unfold physical,double_source_model_point in MODEL.
    rewrite (@double_source_model_preserves_global description (map valuation controls++[value]) ge
      (double_source_instruction_layouts description) m m' header header_block Mint64 0
      (proj2 BIND) WRITE MODEL); exact LOAD. }
  assert (HEADER : forall le m value, double_signed_range_entry controls valuation header_block input le m ->
    start<=value<=Z.max start upper -> le ! iterator=Some (Vlong (Int64.repr value)) ->
    expression_test (Ebinop Olt (Etempvar iterator memory_long_type)
      (memory_long_offset_bound header offset) memory_signed_int_type) (Entry ge locals le m) (value <? upper)).
  { intros le m value [WORDS LOAD] RANGE VALUE.
    assert (RESULT : Int64.sub input (Int64.repr (Int.signed offset))=Int64.repr upper).
    { rewrite <- (Int64.repr_signed input) at 1; rewrite long_source_repr_sub,<- MATH; reflexivity. }
    pose proof (@memory_long_offset_bound_execution ge locals le m header header_block input offset BIND LOAD) as BOUND.
    rewrite RESULT in BOUND; exists (Val.of_bool (value <? upper)); split.
    - eapply memory_long_test_execution; [reflexivity|reflexivity| |exact UPPER|constructor; exact VALUE|exact BOUND].
      pose proof (@memory_i32_range_is_i64 start START) as LOWER.
      destruct (Z_le_dec start upper); rewrite ?Z.max_r,?Z.max_l in RANGE by lia; lia.
    - destruct (value <? upper); reflexivity. }
  pose proof (@memory_long_from_range_equivalence fe ge locals iterator
    (Ecast (Econst_int (Int.repr start) memory_signed_int_type) memory_long_type)
    (Ebinop Olt (Etempvar iterator memory_long_type) (memory_long_offset_bound header offset) memory_signed_int_type)
    body start upper (double_signed_range_entry controls valuation header_block input) physical (fun _ le=>le)
    ltac:(intros; apply memory_long_i32_initial_execution; exact START) HEADER
    ltac:(intros le m tr le' m' out RUN; destruct (@checked_double_source_assignment_effects p (controls++[iterator])
      body description fe ge locals le m tr le' m' out LEAF RUN) as [_ [_ NORMAL]]; exact NORMAL)
    ltac:(intros le m tr le' m' RUN; destruct (@checked_double_source_assignment_effects p (controls++[iterator])
      body description fe ge locals le m tr le' m' Out_normal LEAF RUN) as [_ [SAME _]]; rewrite SAME; reflexivity)
    BRIDGE BODY_ENTRY SET_ENTRY temps memory after final ENTRY) as CORRECT.
  rewrite memory_long_range_identity_exit in CORRECT.
  pose proof (@double_signed_range_model_memory (double_source_instruction_model description) (map valuation controls)
    start upper (global_double_locations ge (double_source_instruction_layouts description)) memory final) as MODEL.
  rewrite map_length in MODEL; rewrite MODEL; exact CORRECT.
Qed.

Lemma long_raw_from_execution iterator initial bound body :
  statement_execution_equivalent (long_raw_from_loop iterator initial bound body)
    (memory_long_from_loop iterator initial
      (Ebinop Olt (Etempvar iterator memory_long_type) bound memory_signed_int_type) body).
Proof.
  apply skip_prefix_execution_equivalent.
  unfold long_raw_from_loop,long_raw_loaded_loop,memory_long_from_loop,memory_long_frontend_loop,
    memory_long_increment,long_counter_increment,long_counter_condition,memory_long_plus_int.
  apply skip_prefix_sequence; [apply skip_prefix_insert; apply skip_prefix_same|].
  apply skip_prefix_loop.
  - apply skip_prefix_sequence; [apply skip_prefix_insert; apply skip_prefix_same|apply skip_prefix_same].
  - apply skip_prefix_insert; apply skip_prefix_same.
Qed.

Print Assumptions checked_double_signed_offset_source_model.
Print Assumptions long_raw_from_execution.
