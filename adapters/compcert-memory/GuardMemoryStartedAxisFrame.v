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
Import ListNotations.
Local Open Scope Z_scope.
Set Implicit Arguments.

Definition memory_started_axis_pointer_guard_protected source (package : memory_started_pointer_package source) live :=
  memory_nest_iterators (param_pointer_region_nest (started_pointer_package package)) ++
  memory_param_pointer_runtime_context (started_pointer_package package) ++ param_pointer_region_pointers (started_pointer_package package) ++ live.

Lemma memory_started_axis_pointer_protected_pointer source (package : memory_started_pointer_package source) live pointer :
  In pointer (param_pointer_region_pointers (started_pointer_package package)) -> In pointer (memory_started_axis_pointer_guard_protected package live).
Proof. intro MEMBER; unfold memory_started_axis_pointer_guard_protected; apply in_or_app; right;
  apply in_or_app; right; apply in_or_app; left; exact MEMBER. Qed.

Lemma memory_started_axis_pointer_protected_bound source (package : memory_started_pointer_package source) live bound :
  In bound (memory_nest_bounds (param_pointer_region_nest (started_pointer_package package))) ->
  In bound (memory_started_axis_pointer_guard_protected package live).
Proof.
  intro MEMBER; unfold memory_started_axis_pointer_guard_protected; apply in_or_app; right; apply in_or_app; left.
  unfold memory_param_pointer_runtime_context; apply in_or_app; left; exact MEMBER.
Qed.

Lemma memory_started_axis_pointer_protected_parameter source (package : memory_started_pointer_package source) live identifier :
  In identifier (param_pointer_region_parameters (started_pointer_package package)) -> In identifier (memory_started_axis_pointer_guard_protected package live).
Proof.
  intro MEMBER; unfold memory_started_axis_pointer_guard_protected; apply in_or_app; right; apply in_or_app; left.
  unfold memory_param_pointer_runtime_context; apply in_or_app; right; apply in_or_app; left; exact MEMBER.
Qed.

Lemma memory_started_pointer_runtime_footprint_temp_frame source (package : memory_started_pointer_package source) original current :
  temp_agree (memory_started_pointer_context package) original current ->
  memory_started_pointer_runtime_footprint package current = memory_started_pointer_runtime_footprint package original.
Proof.
  intro FRAME; unfold memory_started_pointer_runtime_footprint;
    rewrite (@memory_recursive_parameters_temp_frame (memory_started_pointer_context package) original current FRAME); reflexivity.
Qed.
Lemma memory_started_axis_pointer_capabilities_frame source (package : memory_started_pointer_package source)
  original current memory upper counts start live :
  memory_nest_bindings (memory_nest_bounds (param_pointer_region_nest (started_pointer_package package))) (upper::counts) original ->
  Forall signed_range (upper::counts) -> signed_range start ->
  original ! (started_pointer_iterator package) = Some (Vint (Int.repr start)) ->
  temp_agree (memory_started_axis_pointer_guard_protected package live) original current ->
  Forall (memory_cell_capable (memory_multi_pointer_locations original (param_pointer_region_window (started_pointer_package package))) memory)
    (memory_started_pointer_runtime_footprint package original) ->
  Forall (memory_cell_capable (memory_multi_pointer_locations current (param_pointer_region_window (started_pointer_package package))) memory)
    (memory_started_pointer_runtime_footprint package current).
Proof.
  intros WORDS RANGES START ROOT FRAME CELLS.
  assert (CONTEXT : temp_agree (memory_started_pointer_context package) original current).
  { eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER.
    unfold memory_started_pointer_context in MEMBER; apply in_app_or in MEMBER as [MEMBER|MEMBER].
    - unfold memory_started_axis_pointer_guard_protected; apply in_or_app; right; apply in_or_app; left; exact MEMBER.
    - cbn in MEMBER; destruct MEMBER as [<-|[]]; unfold memory_started_axis_pointer_guard_protected.
      apply in_or_app; left; rewrite (started_pointer_nest package); cbn; auto. }
  rewrite (@memory_started_pointer_runtime_footprint_temp_frame _ _ original current CONTEXT).
  apply Forall_forall; intros cell MEMBER.
  pose proof MEMBER as ACCESS; apply (proj1 (@memory_started_pointer_footprint_member source package original upper counts start cell WORDS RANGES START ROOT))
    in ACCESS as [access [coordinates [ACCESS [COORDINATES ->]]]].
  apply Forall_forall with (x := memory_param_axis_pointer_access_cell access
    (coordinates++memory_recursive_parameters (param_pointer_region_parameters (started_pointer_package package)) original)) in CELLS; [|exact MEMBER].
  destruct CELLS as [location [RESOLVE REST]]; exists location; split; [|exact REST].
  unfold memory_param_axis_pointer_access_cell,memory_multi_pointer_locations in *; cbn [point_cell arr_id] in *.
  rewrite FRAME; [exact RESOLVE|].
  apply memory_started_axis_pointer_protected_pointer; pose proof (memory_param_axis_pointer_accesses_covered (started_pointer_package package)) as COVER.
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
Lemma memory_started_axis_access_pair_check_frame original current extent counts start parameter_values first second :
  temp_agree [memory_nary_access_array first;memory_nary_access_array second] original current ->
  memory_started_axis_access_pair_check (memory_multi_pointer_locations current extent) counts start parameter_values (first,second) =
  memory_started_axis_access_pair_check (memory_multi_pointer_locations original extent) counts start parameter_values (first,second).
Proof.
  intro FRAME; unfold memory_started_axis_access_pair_check,memory_started_param_affine_axis_pair_check; cbn [fst snd].
  apply memory_started_axis_rectangle_ext; intro first_coordinates; apply memory_started_axis_rectangle_ext; intro second_coordinates.
  unfold memory_cell_pair_address_check; destruct memory_cell_identity_dec; [reflexivity|].
  unfold memory_multi_pointer_locations; cbn [arr_id point_cell].
  rewrite (FRAME (memory_nary_access_array first) ltac:(cbn; auto)),
    (FRAME (memory_nary_access_array second) ltac:(cbn; auto)); reflexivity.
Qed.

Lemma memory_started_axis_pointer_pairs_check_frame source (package : memory_started_pointer_package source)
  original current counts start parameter_values :
  temp_agree (param_pointer_region_pointers (started_pointer_package package)) original current ->
  memory_started_axis_pointer_pairs_check package (memory_multi_pointer_locations current (param_pointer_region_window (started_pointer_package package))) counts start parameter_values =
  memory_started_axis_pointer_pairs_check package (memory_multi_pointer_locations original (param_pointer_region_window (started_pointer_package package))) counts start parameter_values.
Proof.
  intro FRAME; unfold memory_started_axis_pointer_pairs_check.
  assert (VALID : memory_started_axis_pointer_pairs_valid package
    (memory_affine_access_pairs (memory_linear_pointer_accesses (param_pointer_region_code (started_pointer_package package))))).
  { apply Forall_forall; intros [first second] MEMBER; apply memory_affine_access_pair_member in MEMBER; exact MEMBER. }
  unfold memory_started_axis_pointer_pairs_valid in VALID.
  induction VALID as [|[first second] rest [FIRST [SECOND DISTINCT]] VALID IH]; cbn [forallb]; [reflexivity|].
  rewrite IH; f_equal; apply memory_started_axis_access_pair_check_frame.
  pose proof (memory_param_axis_pointer_accesses_covered (started_pointer_package package)) as COVER.
  assert (FIRST_ID : In (memory_nary_access_array first) (param_pointer_region_pointers (started_pointer_package package)))
    by (apply Forall_forall with (x := first) in COVER; assumption).
  assert (SECOND_ID : In (memory_nary_access_array second) (param_pointer_region_pointers (started_pointer_package package)))
    by (apply Forall_forall with (x := second) in COVER; assumption).
  intros identifier MEMBER; apply FRAME; cbn in MEMBER; destruct MEMBER as [<-|[<-|[]]]; assumption.
Qed.
Print Assumptions memory_started_axis_access_pair_check_frame.

Lemma memory_started_pointer_header_accept_temp_frame source (package : memory_started_pointer_package source)
  ge locals memory original current live :
  temp_agree (memory_started_axis_pointer_guard_protected package live) original current ->
  memory_started_pointer_header_accept package (Entry ge locals current memory) =
  memory_started_pointer_header_accept package (Entry ge locals original memory).
Proof.
  intro FRAME.
  assert (ROOT : current ! (started_pointer_iterator package) = original ! (started_pointer_iterator package)).
  { apply FRAME; unfold memory_started_axis_pointer_guard_protected; apply in_or_app; left.
    rewrite (started_pointer_nest package); cbn; auto. }
  assert (BOUND : current ! (started_pointer_bound package) = original ! (started_pointer_bound package)).
  { apply FRAME; apply memory_started_axis_pointer_protected_bound; rewrite (started_pointer_nest package); cbn; auto. }
  unfold memory_started_pointer_header_accept,memory_started_pointer_bounds_accept,memory_started_bounds_accept.
  rewrite (@memory_vector_bounds_accept_temp_frame _ _ ge locals memory original current).
  2: { eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER.
    apply memory_started_axis_pointer_protected_bound; exact MEMBER. }
  rewrite (@memory_parameter_ranges_accept_temp_frame _ _ ge locals memory original current).
  2: { eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER.
    apply memory_started_axis_pointer_protected_parameter; exact MEMBER. }
  unfold memory_started_active_flag,memory_parameter_range_flag,memory_parameter_nonnegative,register_at_most,temp_word.
  cbn [entry_temps]; rewrite ROOT,BOUND; reflexivity.
Qed.
Print Assumptions memory_started_pointer_header_accept_temp_frame.
