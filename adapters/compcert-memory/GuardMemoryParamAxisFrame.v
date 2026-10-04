From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightTempFrame ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryRecursiveSource
  GuardMemoryMultiPointerCells GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerProjectedCandidate
  GuardMemoryLinearPointerSyntax GuardMemoryNaryAffineAccess GuardMemoryLoopGuardFrame
  GuardMemoryFootprintCapabilities GuardMemoryBooleanScan GuardMemoryFiniteFootprint GuardMemoryFiniteAliasCondition
  GuardMemoryAffinePointerPairs.
From GuardMemory Require Import GuardMemoryRecursiveDomain GuardMemoryBooleanRectangle GuardMemoryAffineAxisPairScan
  GuardMemoryAxisPointerFootprint GuardMemoryAxisPointerPairs GuardMemoryAxisPointerScan.
From GuardMemory Require Import GuardMemoryParamPointerSyntax GuardMemoryParamPointerProjectedCandidate GuardMemoryParamAxisFootprint GuardMemoryParamAxisPairs GuardMemoryParamAxisScan GuardMemoryParamRuntimeFrame GuardMemoryParamAxisPairScan.
Import ListNotations.
Set Implicit Arguments.

Definition memory_param_axis_pointer_guard_protected source (package : memory_param_pointer_region_package source) live :=
  memory_nest_iterators (param_pointer_region_nest package) ++
  memory_param_pointer_runtime_context package ++ param_pointer_region_pointers package ++ live.

Lemma memory_param_axis_pointer_protected_pointer source (package : memory_param_pointer_region_package source) live pointer :
  In pointer (param_pointer_region_pointers package) -> In pointer (memory_param_axis_pointer_guard_protected package live).
Proof. intro MEMBER; unfold memory_param_axis_pointer_guard_protected; apply in_or_app; right;
  apply in_or_app; right; apply in_or_app; left; exact MEMBER. Qed.

Lemma memory_param_axis_pointer_protected_bound source (package : memory_param_pointer_region_package source) live bound :
  In bound (memory_nest_bounds (param_pointer_region_nest package)) ->
  In bound (memory_param_axis_pointer_guard_protected package live).
Proof.
  intro MEMBER; unfold memory_param_axis_pointer_guard_protected; apply in_or_app; right; apply in_or_app; left.
  unfold memory_param_pointer_runtime_context; apply in_or_app; left; exact MEMBER.
Qed.

Lemma memory_param_axis_pointer_protected_parameter source (package : memory_param_pointer_region_package source) live identifier :
  In identifier (param_pointer_region_parameters package) -> In identifier (memory_param_axis_pointer_guard_protected package live).
Proof.
  intro MEMBER; unfold memory_param_axis_pointer_guard_protected; apply in_or_app; right; apply in_or_app; left.
  unfold memory_param_pointer_runtime_context; apply in_or_app; right; apply in_or_app; left; exact MEMBER.
Qed.

Lemma memory_param_axis_pointer_capabilities_frame source (package : memory_param_pointer_region_package source)
  original current memory counts live :
  memory_nest_bindings (memory_nest_bounds (param_pointer_region_nest package)) counts original ->
  Forall signed_range counts ->
  temp_agree (memory_param_axis_pointer_guard_protected package live) original current ->
  Forall (memory_cell_capable (memory_multi_pointer_locations original (param_pointer_region_window package)) memory)
    (memory_param_pointer_runtime_footprint package original) ->
  Forall (memory_cell_capable (memory_multi_pointer_locations current (param_pointer_region_window package)) memory)
    (memory_param_pointer_runtime_footprint package current).
Proof.
  intros WORDS RANGES FRAME CELLS.
  assert (CONTEXT : temp_agree (memory_param_pointer_runtime_context package) original current).
  { eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER; unfold memory_param_axis_pointer_guard_protected;
    apply in_or_app; right; apply in_or_app; left; exact MEMBER. }
  rewrite (@memory_param_pointer_runtime_footprint_temp_frame _ _ original current CONTEXT).
  apply Forall_forall; intros cell MEMBER.
  pose proof MEMBER as ACCESS; apply (proj1 (@memory_param_axis_pointer_footprint_member source package original counts cell WORDS RANGES))
    in ACCESS as [access [coordinates [ACCESS [COORDINATES ->]]]].
  apply Forall_forall with (x := memory_param_axis_pointer_access_cell access
    (coordinates++memory_recursive_parameters (param_pointer_region_parameters package) original)) in CELLS; [|exact MEMBER].
  destruct CELLS as [location [RESOLVE REST]]; exists location; split; [|exact REST].
  unfold memory_param_axis_pointer_access_cell,memory_multi_pointer_locations in *; cbn [point_cell arr_id] in *.
  rewrite FRAME; [exact RESOLVE|].
  apply memory_param_axis_pointer_protected_pointer; pose proof (memory_param_axis_pointer_accesses_covered package) as COVER.
  apply Forall_forall with (x := access) in COVER; assumption.
Qed.

Lemma memory_param_axis_rectangle_ext first second counts :
  (forall coordinates, first coordinates = second coordinates) -> forall prefix,
  memory_boolean_rectangle_result first counts prefix = memory_boolean_rectangle_result second counts prefix.
Proof.
  intro SAME; induction counts as [|count counts IH]; intro prefix; cbn [memory_boolean_rectangle_result].
  - apply SAME.
  - apply memory_boolean_scan_ext; intro coordinate; apply IH.
Qed.

Lemma memory_param_axis_access_pair_check_frame original current extent counts parameter_values first second :
  temp_agree [memory_nary_access_array first;memory_nary_access_array second] original current ->
  memory_param_axis_access_pair_check (memory_multi_pointer_locations current extent) counts parameter_values (first,second) =
  memory_param_axis_access_pair_check (memory_multi_pointer_locations original extent) counts parameter_values (first,second).
Proof.
  intro FRAME; unfold memory_param_axis_access_pair_check,memory_param_affine_axis_pair_check; cbn [fst snd].
  apply memory_param_axis_rectangle_ext; intro first_coordinates; apply memory_param_axis_rectangle_ext; intro second_coordinates.
  unfold memory_cell_pair_address_check; destruct memory_cell_identity_dec; [reflexivity|].
  unfold memory_multi_pointer_locations; cbn [arr_id point_cell].
  rewrite (FRAME (memory_nary_access_array first) ltac:(cbn; auto)),
    (FRAME (memory_nary_access_array second) ltac:(cbn; auto)); reflexivity.
Qed.

Lemma memory_param_axis_pointer_pairs_check_frame source (package : memory_param_pointer_region_package source)
  original current counts parameter_values :
  temp_agree (param_pointer_region_pointers package) original current ->
  memory_param_axis_pointer_pairs_check package (memory_multi_pointer_locations current (param_pointer_region_window package)) counts parameter_values =
  memory_param_axis_pointer_pairs_check package (memory_multi_pointer_locations original (param_pointer_region_window package)) counts parameter_values.
Proof.
  intro FRAME; unfold memory_param_axis_pointer_pairs_check.
  assert (VALID : memory_param_axis_pointer_pairs_valid package
    (memory_affine_access_pairs (memory_linear_pointer_accesses (param_pointer_region_code package)))).
  { apply Forall_forall; intros [first second] MEMBER; apply memory_affine_access_pair_member in MEMBER; exact MEMBER. }
  unfold memory_param_axis_pointer_pairs_valid in VALID.
  induction VALID as [|[first second] rest [FIRST [SECOND DISTINCT]] VALID IH]; cbn [forallb]; [reflexivity|].
  rewrite IH; f_equal; apply memory_param_axis_access_pair_check_frame.
  pose proof (memory_param_axis_pointer_accesses_covered package) as COVER.
  assert (FIRST_ID : In (memory_nary_access_array first) (param_pointer_region_pointers package))
    by (apply Forall_forall with (x := first) in COVER; assumption).
  assert (SECOND_ID : In (memory_nary_access_array second) (param_pointer_region_pointers package))
    by (apply Forall_forall with (x := second) in COVER; assumption).
  intros identifier MEMBER; apply FRAME; cbn in MEMBER; destruct MEMBER as [<-|[<-|[]]]; assumption.
Qed.
Print Assumptions memory_param_axis_access_pair_check_frame.
