From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightTempFrame ClightRedundantSet ClightRectangularGuard ClightNoWrap.
From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryRecursiveDomain GuardMemoryRecursiveGuard
  GuardMemoryRegistryGuard GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerProjectedCandidate.
From GuardMemory Require Import GuardMemoryLoopGuardFrame.
From GuardMemory Require Import GuardMemoryVectorBounds GuardMemoryVectorGuard GuardMemoryVectorPointerSyntax GuardMemoryVectorPointerProjectedCandidate.
Import ListNotations.
Set Implicit Arguments.

Lemma memory_vector_bounds_accept_temp_frame caps bounds ge locals memory original current :
  temp_agree bounds original current ->
  memory_vector_bounds_accept caps bounds (Entry ge locals current memory) =
  memory_vector_bounds_accept caps bounds (Entry ge locals original memory).
Proof.
  revert bounds; induction caps as [|cap caps IH]; intros [|bound bounds] FRAME;
    cbn [memory_vector_bounds_accept]; try reflexivity.
  assert (HEAD : register_range_flag bound cap (Entry ge locals current memory) =
    register_range_flag bound cap (Entry ge locals original memory)).
  { unfold register_range_flag,register_positive,register_at_most,temp_word; cbn [entry_temps];
    rewrite FRAME by (cbn; auto); reflexivity. }
  rewrite HEAD,IH; [reflexivity|eapply temp_agree_weaken; [|exact FRAME]; cbn; auto].
Qed.
Lemma memory_vector_guard_accept_temp_frame caps nest ge locals memory original current :
  temp_agree (memory_nest_iterators nest++memory_nest_bounds nest) original current ->
  memory_vector_guard_accept caps nest (Entry ge locals current memory) =
  memory_vector_guard_accept caps nest (Entry ge locals original memory).
Proof.
  destruct nest as [source|iterator bound body child]; intro FRAME; cbn [memory_vector_guard_accept]; [reflexivity|].
  assert (HEAD : register_flag iterator Int.zero (Entry ge locals current memory) =
    register_flag iterator Int.zero (Entry ge locals original memory)).
  { unfold register_flag,temp_word; cbn [entry_temps]; rewrite FRAME by (apply in_or_app; left; cbn; auto); reflexivity. }
  rewrite HEAD,(@memory_vector_bounds_accept_temp_frame caps
    (memory_nest_bounds (MemorySourceAxis iterator bound body child)) ge locals memory original current); [reflexivity|].
  eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER; apply in_or_app; right; exact MEMBER.
Qed.

Lemma memory_vector_pointer_runtime_footprint_temp_frame source (package : memory_vector_pointer_region_package source) original current :
  temp_agree (memory_vector_pointer_runtime_context package) original current ->
  memory_vector_pointer_runtime_footprint package current = memory_vector_pointer_runtime_footprint package original.
Proof.
  intro FRAME; unfold memory_vector_pointer_runtime_footprint;
    rewrite (@memory_recursive_parameters_temp_frame (memory_vector_pointer_runtime_context package) original current FRAME); reflexivity.
Qed.

Print Assumptions memory_vector_bounds_accept_temp_frame.
Print Assumptions memory_vector_guard_accept_temp_frame.
Print Assumptions memory_vector_pointer_runtime_footprint_temp_frame.
