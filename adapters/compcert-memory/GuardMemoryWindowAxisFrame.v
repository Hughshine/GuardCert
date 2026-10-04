From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightTempFrame ClightCountedLoop ClightCondition ClightNoWrap ClightRectangularGuard ClightRedundantSet.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryRecursiveSource
  GuardMemoryMultiPointerCells GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerProjectedCandidate
  GuardMemoryLinearPointerSyntax GuardMemoryNaryAffineAccess GuardMemoryLoopGuardFrame
  GuardMemoryFootprintCapabilities GuardMemoryBooleanScan GuardMemoryFiniteFootprint GuardMemoryFiniteAliasCondition
  GuardMemoryAffinePointerPairs.
From GuardMemory Require Import GuardMemoryRecursiveDomain GuardMemoryBooleanRectangle GuardMemoryAffineAxisPairScan
  GuardMemoryAxisPointerFootprint GuardMemoryAxisPointerPairs GuardMemoryAxisPointerScan.
From GuardMemory Require Import GuardMemoryParamPointerSyntax GuardMemoryParamPointerProjectedCandidate GuardMemoryParamAxisFootprint GuardMemoryParamAxisPairs GuardMemoryParamAxisScan GuardMemoryParamAxisFrame GuardMemoryParamRuntimeFrame GuardMemoryParamAxisPairScan GuardMemoryVectorRuntimeFrame GuardMemoryParameterRanges.
From GuardMemory Require Import GuardMemoryStartedPackage GuardMemoryStartedPointerFootprint GuardMemoryStartedAxisPairs
  GuardMemoryStartedPairScan GuardMemoryStartedBooleanRectangle GuardMemoryStartedBooleanWrapper GuardMemoryStartedAxisScan GuardMemoryStartedPointerHeader GuardMemoryStartedHeader.
From GuardMemory Require Import GuardMemoryWindowPackage GuardMemoryWindowStartedPackage GuardMemoryWindowSyntax GuardMemoryWindowCells GuardMemoryWindowRuntimeFootprint GuardMemoryWindowFootprintExact GuardMemoryWindowPackageBounds GuardMemoryWindowPackageHeader GuardMemoryWindowHeader GuardMemoryIntervalGuard GuardMemoryWindowParameterGuard GuardMemoryWindowAccessMetadata GuardMemoryWindowAxisPairs GuardMemoryWindowAxisScan.
Import ListNotations.
Local Open Scope Z_scope.
Set Implicit Arguments.

Definition window_axis_guard_protected source (package : window_started_package source) live :=
  memory_nest_iterators (window_region_nest (window_started_base package)) ++
  window_package_context package ++ window_region_pointers (window_started_base package) ++ live.

Lemma window_axis_protected_pointer source (package : window_started_package source) live pointer :
  In pointer (window_region_pointers (window_started_base package)) -> In pointer (window_axis_guard_protected package live).
Proof. intro MEMBER; unfold window_axis_guard_protected; apply in_or_app; right;
  apply in_or_app; right; apply in_or_app; left; exact MEMBER. Qed.

Lemma window_axis_protected_bound source (package : window_started_package source) live bound :
  In bound (memory_nest_bounds (window_region_nest (window_started_base package))) -> In bound (window_axis_guard_protected package live).
Proof.
  intro MEMBER; unfold window_axis_guard_protected; apply in_or_app; right; apply in_or_app; left.
  unfold window_package_context; apply in_or_app; left; exact MEMBER.
Qed.
Lemma window_axis_protected_parameter source (package : window_started_package source) live identifier :
  In identifier (window_region_parameters (window_started_base package)) -> In identifier (window_axis_guard_protected package live).
Proof.
  intro MEMBER; unfold window_axis_guard_protected; apply in_or_app; right; apply in_or_app; left.
  unfold window_package_context; apply in_or_app; right; apply in_or_app; left; exact MEMBER.
Qed.

Lemma window_runtime_footprint_temp_frame source (package : window_started_package source) original current :
  temp_agree (window_package_context package) original current ->
  window_runtime_footprint package current = window_runtime_footprint package original.
Proof.
  intro FRAME; unfold window_runtime_footprint;
    rewrite (@memory_recursive_parameters_temp_frame (window_package_context package) original current FRAME); reflexivity.
Qed.
Lemma window_axis_capabilities_frame source (package : window_started_package source)
  original current memory upper counts start live :
  memory_nest_bindings (memory_nest_bounds (window_region_nest (window_started_base package))) (upper::counts) original ->
  Forall signed_range (upper::counts) -> signed_range start ->
  original ! (window_started_iterator package) = Some (Vint (Int.repr start)) ->
  temp_agree (window_axis_guard_protected package live) original current ->
  Forall (memory_cell_capable (window_multi_pointer_locations original (window_region_lower (window_started_base package)) (window_region_upper (window_started_base package))) memory)
    (window_runtime_footprint package original) ->
  Forall (memory_cell_capable (window_multi_pointer_locations current (window_region_lower (window_started_base package)) (window_region_upper (window_started_base package))) memory)
    (window_runtime_footprint package current).
Proof.
  intros WORDS RANGES START ROOT FRAME CELLS.
  assert (CONTEXT : temp_agree (window_package_context package) original current).
  { eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER.
    unfold window_axis_guard_protected; apply in_or_app; right; apply in_or_app; left; exact MEMBER. }
  rewrite (@window_runtime_footprint_temp_frame _ _ original current CONTEXT).
  apply Forall_forall; intros cell MEMBER.
  pose proof MEMBER as ACCESS; apply (proj1 (@window_footprint_member source package original upper counts start cell WORDS RANGES START ROOT))
    in ACCESS as [access [coordinates [ACCESS [COORDINATES ->]]]].
  apply Forall_forall with (x := memory_param_axis_pointer_access_cell access
    (coordinates++memory_recursive_parameters (window_region_parameters (window_started_base package)) original)) in CELLS; [|exact MEMBER].
  destruct CELLS as [location [RESOLVE REST]]; exists location; split; [|exact REST].
  unfold memory_param_axis_pointer_access_cell,window_multi_pointer_locations in *; cbn [point_cell arr_id] in *.
  rewrite FRAME; [exact RESOLVE|].
  apply window_axis_protected_pointer; pose proof (window_accesses_covered (window_started_base package)) as COVER.
  apply Forall_forall with (x := access) in COVER; assumption.
Qed.

Lemma memory_started_axis_rectangle_ext first second counts start :
  (forall coordinates, first coordinates = second coordinates) ->
  memory_boolean_started_all_result first counts start = memory_boolean_started_all_result second counts start.
Proof.
  intro SAME; destruct counts as [|upper counts]; [reflexivity|].
  unfold memory_boolean_started_all_result,memory_boolean_started_rectangle_result.
  apply memory_boolean_scan_ext; intro coordinate; apply memory_param_axis_rectangle_ext; exact SAME.
Qed.
Lemma window_axis_pair_check_frame original current lower upper counts start parameter_values first second :
  temp_agree [memory_nary_access_array first;memory_nary_access_array second] original current ->
  window_axis_access_pair_check (window_multi_pointer_locations current lower upper) counts start parameter_values (first,second) =
  window_axis_access_pair_check (window_multi_pointer_locations original lower upper) counts start parameter_values (first,second).
Proof.
  intro FRAME; unfold window_axis_access_pair_check,memory_started_param_affine_axis_pair_check; cbn [fst snd].
  apply memory_started_axis_rectangle_ext; intro first_coordinates; apply memory_started_axis_rectangle_ext; intro second_coordinates.
  unfold memory_cell_pair_address_check; destruct memory_cell_identity_dec; [reflexivity|].
  unfold window_multi_pointer_locations; cbn [arr_id point_cell].
  rewrite (FRAME (memory_nary_access_array first) ltac:(cbn; auto)),
    (FRAME (memory_nary_access_array second) ltac:(cbn; auto)); reflexivity.
Qed.

Lemma window_axis_pairs_check_frame source (package : window_started_package source)
  original current counts start parameter_values :
  temp_agree (window_region_pointers (window_started_base package)) original current ->
  window_axis_pointer_pairs_check package (window_multi_pointer_locations current (window_region_lower (window_started_base package)) (window_region_upper (window_started_base package))) counts start parameter_values =
  window_axis_pointer_pairs_check package (window_multi_pointer_locations original (window_region_lower (window_started_base package)) (window_region_upper (window_started_base package))) counts start parameter_values.
Proof.
  intro FRAME; unfold window_axis_pointer_pairs_check.
  assert (VALID : window_axis_pairs_valid package
    (memory_affine_access_pairs (memory_linear_pointer_accesses (window_region_operations (window_started_base package))))).
  { apply Forall_forall; intros [first second] MEMBER; apply memory_affine_access_pair_member in MEMBER; exact MEMBER. }
  unfold window_axis_pairs_valid in VALID.
  induction VALID as [|[first second] rest [FIRST [SECOND DISTINCT]] VALID IH]; cbn [forallb]; [reflexivity|].
  rewrite IH; f_equal; apply window_axis_pair_check_frame.
  pose proof (window_accesses_covered (window_started_base package)) as COVER.
  assert (FIRST_ID : In (memory_nary_access_array first) (window_region_pointers (window_started_base package)))
    by (apply Forall_forall with (x := first) in COVER; assumption).
  assert (SECOND_ID : In (memory_nary_access_array second) (window_region_pointers (window_started_base package)))
    by (apply Forall_forall with (x := second) in COVER; assumption).
  intros identifier MEMBER; apply FRAME; cbn in MEMBER; destruct MEMBER as [<-|[<-|[]]]; assumption.
Qed.
Print Assumptions window_axis_pair_check_frame.


Lemma window_parameters_accept_temp_frame bounds identifiers ge locals memory original current :
  temp_agree identifiers original current ->
  window_parameters_accept bounds identifiers (Entry ge locals current memory) =
  window_parameters_accept bounds identifiers (Entry ge locals original memory).
Proof.
  revert identifiers; induction bounds as [|[lower upper] rest IH]; intros [|identifier identifiers] FRAME; cbn [window_parameters_accept]; try reflexivity.
  rewrite IH.
  - unfold signed_interval_flag,signed_interval_lower_flag,register_at_most,temp_word; cbn [entry_temps].
    rewrite (FRAME identifier ltac:(cbn; auto)); reflexivity.
  - intros key MEMBER; apply FRAME; cbn; auto.
Qed.
Lemma window_header_accept_temp_frame source (package : window_started_package source)
  ge locals memory original current live :
  temp_agree (window_axis_guard_protected package live) original current ->
  window_package_header_accept package (Entry ge locals current memory) =
  window_package_header_accept package (Entry ge locals original memory).
Proof.
  intro FRAME.
  assert (ROOT : current ! (window_started_iterator package) = original ! (window_started_iterator package)).
  { apply FRAME; unfold window_axis_guard_protected; apply in_or_app; left.
    rewrite (window_started_nest package); cbn; auto. }
  assert (BOUND : current ! (window_started_bound package) = original ! (window_started_bound package)).
  { apply FRAME; apply window_axis_protected_bound; rewrite (window_started_nest package); cbn; auto. }
  unfold window_package_header_accept,window_header_accept,window_bounds_accept.
  rewrite (@memory_vector_bounds_accept_temp_frame _ _ ge locals memory original current).
  2: { eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER.
    apply window_axis_protected_bound; exact MEMBER. }
  rewrite (@window_parameters_accept_temp_frame _ _ ge locals memory original current).
  2: { eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER.
    apply window_axis_protected_parameter; exact MEMBER. }
  unfold memory_started_active_flag,signed_interval_flag,signed_interval_lower_flag,register_at_most,temp_word.
  cbn [entry_temps]; rewrite ROOT,BOUND; reflexivity.
Qed.
Print Assumptions window_axis_capabilities_frame.
Print Assumptions window_axis_pair_check_frame.
Print Assumptions window_header_accept_temp_frame.
