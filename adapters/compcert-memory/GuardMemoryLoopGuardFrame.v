From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightTempFrame ClightRedundantSet ClightRectangularGuard ClightNoWrap.
From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryRecursiveDomain GuardMemoryRecursiveGuard
  GuardMemoryRegistryGuard GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerProjectedCandidate.
Import ListNotations.
Set Implicit Arguments.

Lemma memory_recursive_parameters_temp_frame identifiers original current :
  temp_agree identifiers original current ->
  memory_recursive_parameters identifiers current = memory_recursive_parameters identifiers original.
Proof.
  intro FRAME; unfold memory_recursive_parameters; apply map_ext_in; intros identifier MEMBER.
  unfold temp_word; rewrite FRAME by exact MEMBER; reflexivity.
Qed.

Lemma memory_recursive_bounds_accept_temp_frame cap bounds ge locals memory original current :
  temp_agree bounds original current ->
  memory_recursive_bounds_accept cap bounds (Entry ge locals current memory) =
  memory_recursive_bounds_accept cap bounds (Entry ge locals original memory).
Proof.
  induction bounds as [|bound bounds IH]; intro FRAME; cbn [memory_recursive_bounds_accept]; [reflexivity|].
  assert (HEAD : register_range_flag bound cap (Entry ge locals current memory) =
    register_range_flag bound cap (Entry ge locals original memory)).
  { unfold register_range_flag,register_positive,register_at_most,temp_word; cbn [entry_temps];
    rewrite FRAME by (cbn; auto); reflexivity. }
  rewrite HEAD,IH; [reflexivity|eapply temp_agree_weaken; [|exact FRAME]; cbn; auto].
Qed.

Lemma memory_recursive_guard_accept_temp_frame cap nest ge locals memory original current :
  temp_agree (memory_nest_iterators nest++memory_nest_bounds nest) original current ->
  memory_recursive_guard_accept cap [] nest (Entry ge locals current memory) =
  memory_recursive_guard_accept cap [] nest (Entry ge locals original memory).
Proof.
  destruct nest as [source|iterator bound body child]; intro FRAME; cbn [memory_recursive_guard_accept]; [reflexivity|].
  assert (HEAD : register_flag iterator Int.zero (Entry ge locals current memory) =
    register_flag iterator Int.zero (Entry ge locals original memory)).
  { unfold register_flag,temp_word; cbn [entry_temps]; rewrite FRAME by (apply in_or_app; left; cbn; auto); reflexivity. }
  rewrite HEAD,(@memory_recursive_bounds_accept_temp_frame cap
    (memory_nest_bounds (MemorySourceAxis iterator bound body child)) ge locals memory original current); [reflexivity|].
  eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER; apply in_or_app; right; exact MEMBER.
Qed.

Lemma memory_multi_pointer_runtime_footprint_temp_frame source (package : memory_multi_pointer_region_package source) original current :
  temp_agree (memory_multi_pointer_runtime_context package) original current ->
  memory_multi_pointer_runtime_footprint package current = memory_multi_pointer_runtime_footprint package original.
Proof.
  intro FRAME; unfold memory_multi_pointer_runtime_footprint;
    rewrite (@memory_recursive_parameters_temp_frame (memory_multi_pointer_runtime_context package) original current FRAME); reflexivity.
Qed.

Print Assumptions memory_recursive_guard_accept_temp_frame.
Print Assumptions memory_multi_pointer_runtime_footprint_temp_frame.
