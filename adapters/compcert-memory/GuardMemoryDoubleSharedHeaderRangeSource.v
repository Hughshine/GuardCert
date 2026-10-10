From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightGuard ClightRegionProgress ClightGlobalScope ClightSkipPrefix.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryValueInstr GuardMemoryDoubleLocations
  GuardMemoryDoubleSourceInstruction GuardMemoryDoubleSourceLoopModel GuardMemoryDoubleInitializedReductionSource
  GuardMemoryLongControl GuardMemoryLongLoopControl GuardMemoryLongRangeSource GuardMemoryLongRangeCaptureSource
  GuardMemoryLongRawLoadedProgress GuardMemoryLongProgressControl GuardMemoryDoubleRangeModel
  GuardMemoryDoubleSignedRangeSource GuardMemoryDoubleAffineRangeModel.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The source and Loop model share the original N. A later sequence/fusion
    client can therefore retain relations between N-2 and N-3. This theorem
    does not assert that an arbitrary I64 N can be encoded by an I32 backend. *)
Theorem checked_double_shared_header_offset_source_model p controls body description valuation fe ge locals
  iterator header header_block input offset start temps memory after final :
  checked_double_source_instruction p (controls++[iterator]) body=Some description ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_source_instruction_globals description) locals ->
  double_global_binding ge locals header header_block ->
  fst (value_instruction_write (double_source_instruction_model description))<>header ->
  ~ In iterator controls -> Int.min_signed<=start<=Int.max_signed ->
  Int64.min_signed<=Int64.signed input-Int.signed offset<=Int64.max_signed ->
  (forall value, start<=value<Int64.signed input-Int.signed offset ->
    double_source_instruction_resolved description (map valuation controls++[value]) ge
      (double_source_instruction_layouts description)) ->
  double_signed_range_entry controls valuation header_block input temps memory ->
  (exec_stmt fe ge locals temps memory
    (memory_long_from_loop iterator
      (Ecast (Econst_int (Int.repr start) memory_signed_int_type) memory_long_type)
      (Ebinop Olt (Etempvar iterator memory_long_type) (memory_long_offset_bound header offset) memory_signed_int_type) body)
    E0 after final Out_normal <->
   SL.loop_semantics (double_shared_header_offset_model (double_source_instruction_model description)
     start (Int.signed offset) (length controls))
     (rev (map valuation controls)++[Int64.signed input])
     (RuntimeState (global_double_locations ge (double_source_instruction_layouts description)) memory)
     (RuntimeState (global_double_locations ge (double_source_instruction_layouts description)) final) /\
   after=PTree.set iterator (Vlong (Int64.repr (Z.max start (Int64.signed input-Int.signed offset)))) temps).
Proof.
  intros LEAF GLOBAL LOCAL BIND WRITE FRESH START UPPER READY ENTRY.
  pose proof (@checked_double_signed_offset_source_model p controls body description valuation fe ge locals
    iterator header header_block input offset start (Int64.signed input-Int.signed offset) temps memory after final
    LEAF GLOBAL LOCAL BIND WRITE FRESH START UPPER eq_refl READY ENTRY) as SOURCE.
  pose proof (@double_signed_range_model_memory (double_source_instruction_model description) (map valuation controls)
    start (Int64.signed input-Int.signed offset) (global_double_locations ge (double_source_instruction_layouts description))
    memory final) as DIRECT.
  pose proof (@double_shared_header_offset_model_memory (double_source_instruction_model description) (map valuation controls)
    start (Int.signed offset) (Int64.signed input) (global_double_locations ge (double_source_instruction_layouts description))
    memory final) as SHARED.
  rewrite map_length in DIRECT,SHARED; rewrite DIRECT in SOURCE; rewrite SHARED; exact SOURCE.
Qed.

Lemma long_raw_from_point_execution iterator initial bound body :
  statement_execution_equivalent (long_raw_from_loop iterator initial bound (Ssequence Sskip body))
    (memory_long_from_loop iterator initial
      (Ebinop Olt (Etempvar iterator memory_long_type) bound memory_signed_int_type) body).
Proof.
  apply skip_prefix_execution_equivalent.
  unfold long_raw_from_loop,long_raw_loaded_loop,memory_long_from_loop,memory_long_frontend_loop,
    memory_long_increment,long_counter_increment,long_counter_condition,memory_long_plus_int.
  apply skip_prefix_sequence; [apply skip_prefix_insert; apply skip_prefix_same|].
  apply skip_prefix_loop.
  - apply skip_prefix_sequence; apply skip_prefix_insert; apply skip_prefix_same.
  - apply skip_prefix_insert; apply skip_prefix_same.
Qed.

Print Assumptions checked_double_shared_header_offset_source_model.
Print Assumptions long_raw_from_point_execution.
