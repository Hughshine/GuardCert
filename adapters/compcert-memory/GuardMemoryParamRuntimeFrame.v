From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightTempFrame ClightRedundantSet ClightRectangularGuard ClightNoWrap.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRecursiveSource GuardMemoryRecursiveDomain
  GuardMemoryLoopGuardFrame GuardMemoryVectorRuntimeFrame.
From GuardMemory Require Import GuardMemoryParameterRanges GuardMemoryParamPointerSyntax
  GuardMemoryParamPointerHeader GuardMemoryParamPointerProjectedCandidate.
Import ListNotations.
Set Implicit Arguments.

Lemma memory_parameter_ranges_accept_temp_frame caps parameters ge locals memory original current :
  temp_agree parameters original current ->
  memory_parameter_ranges_accept caps parameters (Entry ge locals current memory) =
  memory_parameter_ranges_accept caps parameters (Entry ge locals original memory).
Proof.
  revert parameters; induction caps as [|cap caps IH]; intros [|identifier parameters] FRAME;
    cbn [memory_parameter_ranges_accept]; try reflexivity.
  assert (HEAD : memory_parameter_range_flag identifier cap (Entry ge locals current memory) =
    memory_parameter_range_flag identifier cap (Entry ge locals original memory)).
  { unfold memory_parameter_range_flag,memory_parameter_nonnegative,register_at_most,temp_word;
    cbn [entry_temps]; rewrite FRAME by (cbn; auto); reflexivity. }
  rewrite HEAD,IH; [reflexivity|eapply temp_agree_weaken; [|exact FRAME]; cbn; auto].
Qed.
Lemma memory_param_pointer_header_accept_temp_frame source (package : memory_param_pointer_region_package source)
  ge locals memory original current :
  temp_agree (memory_nest_iterators (param_pointer_region_nest package)++
    memory_nest_bounds (param_pointer_region_nest package)++param_pointer_region_parameters package) original current ->
  memory_param_pointer_header_accept package (Entry ge locals current memory) =
  memory_param_pointer_header_accept package (Entry ge locals original memory).
Proof.
  intro FRAME; unfold memory_param_pointer_header_accept.
  rewrite (@memory_vector_guard_accept_temp_frame _ _ ge locals memory original current),
    (@memory_parameter_ranges_accept_temp_frame _ _ ge locals memory original current); try reflexivity;
    eapply temp_agree_weaken; [|exact FRAME| |exact FRAME]; intros identifier MEMBER;
    repeat rewrite in_app_iff in *; intuition.
Qed.
Lemma memory_param_pointer_runtime_footprint_temp_frame source (package : memory_param_pointer_region_package source) original current :
  temp_agree (memory_param_pointer_runtime_context package) original current ->
  memory_param_pointer_runtime_footprint package current = memory_param_pointer_runtime_footprint package original.
Proof.
  intro FRAME; unfold memory_param_pointer_runtime_footprint;
    rewrite (@memory_recursive_parameters_temp_frame (memory_param_pointer_runtime_context package) original current FRAME); reflexivity.
Qed.
Print Assumptions memory_parameter_ranges_accept_temp_frame.
Print Assumptions memory_param_pointer_header_accept_temp_frame.
