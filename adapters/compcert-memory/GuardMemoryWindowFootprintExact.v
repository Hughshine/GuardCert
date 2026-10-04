From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values.
From Guard Require Import ClightCondition ClightNoWrap ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryLoopTrace GuardMemoryRecursiveSource
  GuardMemoryRecursiveDomain GuardMemoryParamAxisFootprint GuardMemoryStartedFootprint GuardMemoryStartedScalarLoop
  GuardMemoryStartedBooleanRectangle GuardMemoryRectangularFootprint GuardMemoryMultiPointerFootprint
  GuardMemoryLinearPointerSyntax GuardMemoryNaryCompute GuardMemoryNaryAffineAccess GuardMemoryFiniteFootprint.
From GuardMemory Require Import GuardMemoryWindowPackage GuardMemoryWindowStartedPackage GuardMemoryWindowPackageBounds GuardMemoryWindowSyntax
  GuardMemoryWindowRuntimeFootprint GuardMemoryWindowPointFootprint.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Theorem window_runtime_footprint_exact source (package : window_started_package source)
  temps upper counts start :
  memory_nest_bindings (memory_nest_bounds (window_region_nest (window_started_base package))) (upper::counts) temps ->
  Forall signed_range (upper::counts) -> signed_range start ->
  temps ! (window_started_iterator package) = Some (Vint (Int.repr start)) ->
  window_runtime_footprint package temps =
    flat_map (fun coordinates => map (fun access => memory_param_axis_pointer_access_cell access
      (coordinates++memory_recursive_parameters (window_region_parameters (window_started_base package)) temps))
      (memory_linear_pointer_accesses (window_region_operations (window_started_base package))))
      (memory_started_rectangular_points upper counts start).
Proof.
  intros WORDS RANGES START ROOT.
  assert (DIMENSIONS : length (memory_nest_iterators (window_region_nest (window_started_base package))) = S (length counts)).
  { rewrite memory_nest_lengths; unfold memory_nest_bindings in WORDS; apply Forall2_length in WORDS; exact WORDS. }
  assert (ROOT_VALUE : Int.signed (temp_word (window_started_iterator package) temps) = start).
  { unfold temp_word; rewrite ROOT,Int.signed_repr by exact START; reflexivity. }
  unfold window_runtime_footprint,window_package_loop,window_package_context,memory_recursive_parameters; rewrite !map_app; cbn [map]; repeat rewrite <-app_assoc.
  change (memory_events_footprint (memory_loop_trace
    (memory_started_scalar_loop (length (memory_nest_iterators (window_region_nest (window_started_base package))))
      (length (window_region_parameters (window_started_base package)++window_region_scalars (window_started_base package)))
      (window_region_instructions (window_started_base package)))
    (memory_recursive_parameters (memory_nest_bounds (window_region_nest (window_started_base package))) temps++
      memory_recursive_parameters (window_region_parameters (window_started_base package)) temps++
       memory_recursive_parameters (window_region_scalars (window_started_base package)) temps++
      [Int.signed (temp_word (window_started_iterator package) temps)])) =
    flat_map (fun coordinates => map (fun access => memory_param_axis_pointer_access_cell access
      (coordinates++memory_recursive_parameters (window_region_parameters (window_started_base package)) temps))
      (memory_linear_pointer_accesses (window_region_operations (window_started_base package))))
      (memory_started_rectangular_points upper counts start)).
  rewrite DIMENSIONS,ROOT_VALUE,(memory_param_axis_pointer_parameters WORDS RANGES).
  replace (length (window_region_parameters (window_started_base package)++window_region_scalars (window_started_base package))) with
    (length (memory_recursive_parameters (window_region_parameters (window_started_base package)) temps++
      memory_recursive_parameters (window_region_scalars (window_started_base package)) temps))
    by (unfold memory_recursive_parameters; rewrite !length_app,!length_map; reflexivity).
  rewrite (app_assoc (memory_recursive_parameters (window_region_parameters (window_started_base package)) temps)
    (memory_recursive_parameters (window_region_scalars (window_started_base package)) temps) [start]).
  rewrite memory_started_scalar_loop_footprint.
  apply memory_flat_map_ext_in; intros coordinates MEMBER.
  apply memory_started_rectangular_points_member in MEMBER.
  assert (COORD_LENGTH : length coordinates = S (length counts)).
  { destruct coordinates as [|x tail]; [contradiction|]; destruct MEMBER as [RANGE TAIL].
    apply Forall2_length in TAIL; cbn; lia. }
  rewrite app_assoc.
  transitivity (memory_point_footprint (window_region_instructions (window_started_base package))
    (coordinates++memory_recursive_parameters (window_region_parameters (window_started_base package)) temps)).
  - unfold window_region_instructions; apply window_point_footprint_prefix with
      (bounds := window_source_coordinate_bounds (window_region_root_lower (window_started_base package))
        (window_region_caps (window_started_base package))++window_region_parameter_bounds (window_started_base package))
      (layout := memory_nest_iterators (window_region_nest (window_started_base package))++window_region_parameters (window_started_base package))
      (lower := window_region_lower (window_started_base package)) (upper := window_region_upper (window_started_base package)).
    + exact (window_source_operations (window_region_certificate (window_started_base package))).
    + rewrite !length_app; unfold memory_recursive_parameters; rewrite length_map,DIMENSIONS,COORD_LENGTH; reflexivity.
  - unfold window_region_instructions; apply memory_param_axis_pointer_point_footprint.
Qed.
Theorem window_footprint_member source (package : window_started_package source)
  temps upper counts start cell :
  memory_nest_bindings (memory_nest_bounds (window_region_nest (window_started_base package))) (upper::counts) temps ->
  Forall signed_range (upper::counts) -> signed_range start ->
  temps ! (window_started_iterator package) = Some (Vint (Int.repr start)) ->
  (In cell (window_runtime_footprint package temps) <->
    exists access coordinates,
      In access (memory_linear_pointer_accesses (window_region_operations (window_started_base package))) /\
      memory_started_axis_coordinates start (upper::counts) coordinates /\
      cell = memory_param_axis_pointer_access_cell access
        (coordinates++memory_recursive_parameters (window_region_parameters (window_started_base package)) temps)).
Proof.
  intros WORDS RANGES START ROOT; rewrite (window_runtime_footprint_exact package WORDS RANGES START ROOT).
  rewrite in_flat_map; split.
  - intros [coordinates [COORDINATES CELL]].
    apply memory_started_rectangular_points_member in COORDINATES; apply in_map_iff in CELL as [access [SAME MEMBER]].
    exists access,coordinates; auto.
  - intros [access [coordinates [MEMBER [COORDINATES ->]]]].
    exists coordinates; split; [apply memory_started_rectangular_points_member; exact COORDINATES|].
    apply in_map_iff; exists access; auto.
Qed.
Print Assumptions window_source_runtime_domain.
Print Assumptions window_runtime_footprint_exact.
Print Assumptions window_footprint_member.
