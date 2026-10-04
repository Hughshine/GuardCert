From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryMultiPointerCells
  GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerProjectedCandidate GuardMemoryLinearPointerSyntax
  GuardMemoryNaryAffineAccess GuardMemoryNaryAffineExpressions GuardMemoryFiniteFootprint
  GuardMemoryFiniteAliasCondition GuardMemoryFootprintCapabilities GuardMemoryFootprintRestriction
  GuardMemoryCrossPointerSeparation GuardMemoryAffinePointerPairs GuardMemoryRecursiveSource.
From GuardMemory Require Import GuardMemoryAxisPointerFootprint GuardMemoryAffineAxisPairScan
  GuardMemoryBooleanRectangle GuardMemoryRecursiveDomain.
From GuardMemory Require Import GuardMemoryParamPointerSyntax GuardMemoryParamPointerProjectedCandidate GuardMemoryParamAxisFootprint GuardMemoryParamAxisPairScan.
From GuardMemory Require Import GuardMemoryStartedPackage GuardMemoryStartedPointerFootprint
  GuardMemoryStartedPairScan GuardMemoryStartedBooleanRectangle GuardMemoryStartedBooleanWrapper GuardMemoryStartedBooleanMember.
From GuardMemory Require Import GuardMemoryWindowPackage GuardMemoryWindowStartedPackage GuardMemoryWindowSyntax GuardMemoryWindowCells GuardMemoryWindowRuntimeFootprint GuardMemoryWindowFootprintExact GuardMemoryWindowCrossPointerSeparation.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition window_axis_access_pair_check locations counts start parameter_values pair :=
  memory_started_param_affine_axis_pair_check locations counts start parameter_values
    (memory_nary_access_array (fst pair)) (memory_nary_access_array (snd pair))
    (memory_nary_access_index (fst pair)) (memory_nary_access_index (snd pair)).
Definition window_axis_pointer_pairs_check source (package : window_started_package source) locations counts start parameter_values :=
  forallb (window_axis_access_pair_check locations counts start parameter_values)
    (memory_affine_access_pairs (memory_linear_pointer_accesses (window_region_operations (window_started_base package)))).

Theorem window_axis_pointer_access_capability source (package : window_started_package source)
  temps memory upper counts start :
  memory_nest_bindings (memory_nest_bounds (window_region_nest (window_started_base package))) (upper::counts) temps ->
  Forall signed_range (upper::counts) -> signed_range start ->
  temps ! (window_started_iterator package) = Some (Vint (Int.repr start)) ->
  Forall (memory_cell_capable (window_multi_pointer_locations temps (window_region_lower (window_started_base package)) (window_region_upper (window_started_base package))) memory)
    (window_runtime_footprint package temps) ->
  forall access coordinates,
    In access (memory_linear_pointer_accesses (window_region_operations (window_started_base package))) ->
    memory_started_axis_coordinates start (upper::counts) coordinates ->
    memory_cell_capable (window_multi_pointer_locations temps (window_region_lower (window_started_base package)) (window_region_upper (window_started_base package))) memory
      (memory_param_axis_pointer_access_cell access
        (coordinates++memory_recursive_parameters (window_region_parameters (window_started_base package)) temps)).
Proof.
  intros WORDS RANGES START ROOT CELLS access coordinates MEMBER COORDINATES.
  apply Forall_forall with (x := memory_param_axis_pointer_access_cell access
        (coordinates++memory_recursive_parameters (window_region_parameters (window_started_base package)) temps)) in CELLS; [exact CELLS|].
  apply (proj2 (@window_footprint_member source package temps upper counts start _ WORDS RANGES START ROOT)).
  exists access,coordinates; auto.
Qed.

Theorem window_axis_pointer_pairs_separation source (package : window_started_package source)
  (ge : genv) (locals : env) temps memory upper counts start :
  Forall (fun count => 0 <= count /\ signed_range count) (upper::counts) ->
  start <= upper -> signed_range start ->
  temps ! (window_started_iterator package) = Some (Vint (Int.repr start)) ->
  memory_nest_bindings (memory_nest_bounds (window_region_nest (window_started_base package))) (upper::counts) temps ->
  Forall (memory_cell_capable (window_multi_pointer_locations temps (window_region_lower (window_started_base package)) (window_region_upper (window_started_base package))) memory)
    (window_runtime_footprint package temps) ->
  window_axis_pointer_pairs_check package (window_multi_pointer_locations temps (window_region_lower (window_started_base package)) (window_region_upper (window_started_base package))) (upper::counts) start
    (memory_recursive_parameters (window_region_parameters (window_started_base package)) temps) = true ->
  locations_nonalias (memory_restrict_locations
    (memory_footprint_allowed (window_runtime_footprint package temps))
    (window_multi_pointer_locations temps (window_region_lower (window_started_base package)) (window_region_upper (window_started_base package)))).
Proof.
  intros RANGES ORDER START ROOT WORDS CELLS CHECK.
  assert (SIGNED : Forall signed_range (upper::counts)).
  { eapply Forall_impl; [|exact RANGES]; intros count [POS RANGE]; exact RANGE. }
  assert (NONNEG : Forall (fun count => 0 <= count) (upper::counts)).
  { eapply Forall_impl; [|exact RANGES]; intros count [POS RANGE]; exact POS. }
  apply window_cross_pointer_separation_suffices.
  - exact (proj2 (proj2 (proj2 (window_source_window (window_region_certificate (window_started_base package)))))).
  - intros first second left right FIRST_MEMBER SECOND_MEMBER DISTINCT FIRST SECOND.
    apply memory_footprint_allowed_exact in FIRST_MEMBER,SECOND_MEMBER.
    pose proof FIRST_MEMBER as FIRST_FOOTPRINT; pose proof SECOND_MEMBER as SECOND_FOOTPRINT.
    apply (proj1 (@window_footprint_member source package temps upper counts start first WORDS SIGNED START ROOT))
      in FIRST_MEMBER as [first_access [first_coordinates [FIRST_ACCESS [FIRST_RANGE ->]]]].
    apply (proj1 (@window_footprint_member source package temps upper counts start second WORDS SIGNED START ROOT))
      in SECOND_MEMBER as [second_access [second_coordinates [SECOND_ACCESS [SECOND_RANGE ->]]]].
    unfold window_axis_pointer_pairs_check in CHECK.
    apply forallb_forall with (x := (first_access,second_access)) in CHECK.
    2: { apply memory_affine_access_pair_member; repeat split; assumption. }
    unfold window_axis_access_pair_check,memory_started_param_affine_axis_pair_check in CHECK; cbn [fst snd] in CHECK.
    rewrite (@memory_boolean_started_all_member _ (upper::counts) start ltac:(discriminate) ORDER NONNEG) in CHECK.
    specialize (CHECK first_coordinates FIRST_RANGE); cbn [app] in CHECK.
    rewrite (@memory_boolean_started_all_member _ (upper::counts) start ltac:(discriminate) ORDER NONNEG) in CHECK.
    specialize (CHECK second_coordinates SECOND_RANGE); cbn [app] in CHECK.
    assert (FIRST_CAP : memory_cell_address_binding memory_multi_pointer_cell_code
      (window_multi_pointer_locations temps (window_region_lower (window_started_base package)) (window_region_upper (window_started_base package)))
      (Entry ge locals temps memory) (memory_param_axis_pointer_access_cell first_access
      (first_coordinates++memory_recursive_parameters (window_region_parameters (window_started_base package)) temps))).
    { apply window_multi_pointer_cell_encoding;
      [exact (proj1 (proj2 (window_source_window (window_region_certificate (window_started_base package)))))|
       exact (proj1 (proj2 (proj2 (window_source_window (window_region_certificate (window_started_base package))))))|].
      apply Forall_forall with (x := memory_param_axis_pointer_access_cell first_access
      (first_coordinates++memory_recursive_parameters (window_region_parameters (window_started_base package)) temps)) in CELLS; assumption. }
    assert (SECOND_CAP : memory_cell_address_binding memory_multi_pointer_cell_code
      (window_multi_pointer_locations temps (window_region_lower (window_started_base package)) (window_region_upper (window_started_base package)))
      (Entry ge locals temps memory) (memory_param_axis_pointer_access_cell second_access
      (second_coordinates++memory_recursive_parameters (window_region_parameters (window_started_base package)) temps))).
    { apply window_multi_pointer_cell_encoding;
      [exact (proj1 (proj2 (window_source_window (window_region_certificate (window_started_base package)))))|
       exact (proj1 (proj2 (proj2 (window_source_window (window_region_certificate (window_started_base package))))))|].
      apply Forall_forall with (x := memory_param_axis_pointer_access_cell second_access
      (second_coordinates++memory_recursive_parameters (window_region_parameters (window_started_base package)) temps)) in CELLS; assumption. }
    eapply memory_cell_pair_address_separated; [exact FIRST_CAP|exact SECOND_CAP|exact FIRST|exact SECOND| |exact CHECK].
    left; exact DISTINCT.
Qed.
Print Assumptions window_axis_pointer_pairs_separation.
