From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles GuardMemoryLoops GuardMemoryLoopTrace
  GuardMemoryRecursiveSource GuardMemoryRecursiveDomain GuardMemoryParamPointerSyntax GuardMemoryParamPointerProjectedCandidate
  GuardMemoryParamAxisFootprint GuardMemoryMultiPointerCells GuardMemoryMultiPointerFootprint GuardMemoryLinearPointerSyntax GuardMemoryInstructionPadding GuardMemoryFootprintCapabilities GuardMemoryFiniteFootprint GuardMemoryActivatedRectangle GuardMemoryRectangularFootprint.
From GuardMemory Require Import GuardMemoryStartedScalarLoop GuardMemoryStartedPackage GuardMemoryStartedPointerHeader
  GuardMemoryStartedPointerDomain GuardMemoryStartedFootprint GuardMemoryStartedBooleanRectangle.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition memory_started_pointer_runtime_footprint source (package : memory_started_pointer_package source) temps :=
  memory_events_footprint (memory_loop_trace (memory_started_pointer_loop package)
    (memory_recursive_parameters (memory_started_pointer_context package) temps)).
Definition memory_started_pointer_runtime_domain source (package : memory_started_pointer_package source) s :=
  memory_started_pointer_header_domain package s /\
  (memory_started_pointer_header_accept package s = true ->
    Forall (memory_cell_capable (memory_multi_pointer_locations (entry_temps s)
      (param_pointer_region_window (started_pointer_package package))) (entry_memory s))
      (memory_started_pointer_runtime_footprint package (entry_temps s))).
Theorem memory_started_pointer_source_runtime_domain source (package : memory_started_pointer_package source)
  fe ge locals temps memory after final :
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  memory_started_pointer_runtime_domain package (Entry ge locals temps memory).
Proof.
  intro SOURCE.
  pose proof (@memory_started_pointer_source_header_domain source package fe ge locals temps memory after final SOURCE) as DOMAIN.
  split; [exact DOMAIN|]; intro ACCEPT.
  destruct (@memory_started_pointer_header_sound source package (Entry ge locals temps memory) DOMAIN ACCEPT)
    as [ACTIVE [RANGES PARAM_RANGES]].
  destruct (@memory_started_pointer_source_under_ranges source (started_pointer_package package)
    (started_pointer_iterator package) (started_pointer_bound package) (started_pointer_body package) (started_pointer_child package)
    fe ge locals temps memory after final (started_pointer_nest package) ACTIVE RANGES PARAM_RANGES SOURCE)
    as [PARAMETERS [SCALARS [LOOP EXIT]]].
  pose proof (@memory_loop_source_capabilities _ _
    (RuntimeState (memory_multi_pointer_locations temps (param_pointer_region_window (started_pointer_package package))) memory)
    (RuntimeState (memory_multi_pointer_locations temps (param_pointer_region_window (started_pointer_package package))) final)
    (memory_multi_pointer_locations_int32 temps (param_pointer_region_window (started_pointer_package package))) LOOP) as CAPABLE.
  unfold memory_started_pointer_runtime_footprint,memory_started_pointer_loop,memory_started_pointer_context,
    memory_param_pointer_runtime_context,memory_recursive_parameters; rewrite !map_app; cbn [map].
  repeat rewrite <-app_assoc in CAPABLE.
  repeat rewrite <-app_assoc.
  apply Forall_forall; intros cell MEMBER.
  unfold memory_events_footprint in MEMBER; apply in_flat_map in MEMBER as [event [EVENT ACCESS]].
  apply Forall_forall with (x := event) in CAPABLE; [|exact EVENT].
  apply Forall_forall with (x := cell) in CAPABLE; [exact CAPABLE|exact ACCESS].
Qed.
Theorem memory_started_pointer_runtime_footprint_exact source (package : memory_started_pointer_package source)
  temps upper counts start :
  memory_nest_bindings (memory_nest_bounds (param_pointer_region_nest (started_pointer_package package))) (upper::counts) temps ->
  Forall signed_range (upper::counts) -> signed_range start ->
  temps ! (started_pointer_iterator package) = Some (Vint (Int.repr start)) ->
  memory_started_pointer_runtime_footprint package temps =
    flat_map (fun coordinates => map (fun access => memory_param_axis_pointer_access_cell access
      (coordinates++memory_recursive_parameters (param_pointer_region_parameters (started_pointer_package package)) temps))
      (memory_linear_pointer_accesses (param_pointer_region_code (started_pointer_package package))))
      (memory_started_rectangular_points upper counts start).
Proof.
  intros WORDS RANGES START ROOT.
  assert (DIMENSIONS : length (memory_nest_iterators (param_pointer_region_nest (started_pointer_package package))) = S (length counts)).
  { rewrite memory_nest_lengths; unfold memory_nest_bindings in WORDS; apply Forall2_length in WORDS; exact WORDS. }
  assert (ROOT_VALUE : Int.signed (temp_word (started_pointer_iterator package) temps) = start).
  { unfold temp_word; rewrite ROOT,Int.signed_repr by exact START; reflexivity. }
  unfold memory_started_pointer_runtime_footprint,memory_started_pointer_loop,memory_started_pointer_context,
    memory_param_pointer_runtime_context,memory_recursive_parameters; rewrite !map_app; cbn [map]; repeat rewrite <-app_assoc.
  change (memory_events_footprint (memory_loop_trace
    (memory_started_scalar_loop (length (memory_nest_iterators (param_pointer_region_nest (started_pointer_package package))))
      (length (param_pointer_region_parameters (started_pointer_package package)++param_pointer_region_scalars (started_pointer_package package)))
      (memory_param_pointer_region_instructions (started_pointer_package package)))
    (memory_recursive_parameters (memory_nest_bounds (param_pointer_region_nest (started_pointer_package package))) temps++
      memory_recursive_parameters (param_pointer_region_parameters (started_pointer_package package)) temps++
       memory_recursive_parameters (param_pointer_region_scalars (started_pointer_package package)) temps++
      [Int.signed (temp_word (started_pointer_iterator package) temps)])) =
    flat_map (fun coordinates => map (fun access => memory_param_axis_pointer_access_cell access
      (coordinates++memory_recursive_parameters (param_pointer_region_parameters (started_pointer_package package)) temps))
      (memory_linear_pointer_accesses (param_pointer_region_code (started_pointer_package package))))
      (memory_started_rectangular_points upper counts start)).
  rewrite DIMENSIONS,ROOT_VALUE,(memory_param_axis_pointer_parameters WORDS RANGES).
  replace (length (param_pointer_region_parameters (started_pointer_package package)++param_pointer_region_scalars (started_pointer_package package))) with
    (length (memory_recursive_parameters (param_pointer_region_parameters (started_pointer_package package)) temps++
      memory_recursive_parameters (param_pointer_region_scalars (started_pointer_package package)) temps))
    by (unfold memory_recursive_parameters; rewrite !length_app,!length_map; reflexivity).
  rewrite (app_assoc (memory_recursive_parameters (param_pointer_region_parameters (started_pointer_package package)) temps)
    (memory_recursive_parameters (param_pointer_region_scalars (started_pointer_package package)) temps) [start]).
  rewrite memory_started_scalar_loop_footprint.
  apply memory_flat_map_ext_in; intros coordinates MEMBER.
  apply memory_started_rectangular_points_member in MEMBER.
  assert (COORD_LENGTH : length coordinates = S (length counts)).
  { destruct coordinates as [|x tail]; [contradiction|]; destruct MEMBER as [RANGE TAIL].
    apply Forall2_length in TAIL; cbn; lia. }
  rewrite app_assoc.
  transitivity (memory_point_footprint (memory_param_pointer_region_instructions (started_pointer_package package))
    (coordinates++memory_recursive_parameters (param_pointer_region_parameters (started_pointer_package package)) temps)).
  - unfold memory_param_pointer_region_instructions; apply memory_multi_pointer_point_footprint_prefix with
      (limits := param_pointer_region_limits (started_pointer_package package)++param_pointer_region_parameter_limits (started_pointer_package package))
      (layout := memory_nest_iterators (param_pointer_region_nest (started_pointer_package package))++param_pointer_region_parameters (started_pointer_package package))
      (extent := param_pointer_region_window (started_pointer_package package)).
    + exact (param_pointer_region_operations (param_pointer_region_syntax (started_pointer_package package))).
    + rewrite !length_app; unfold memory_recursive_parameters; rewrite length_map,DIMENSIONS,COORD_LENGTH; reflexivity.
  - unfold memory_param_pointer_region_instructions; apply memory_param_axis_pointer_point_footprint.
Qed.
Theorem memory_started_pointer_footprint_member source (package : memory_started_pointer_package source)
  temps upper counts start cell :
  memory_nest_bindings (memory_nest_bounds (param_pointer_region_nest (started_pointer_package package))) (upper::counts) temps ->
  Forall signed_range (upper::counts) -> signed_range start ->
  temps ! (started_pointer_iterator package) = Some (Vint (Int.repr start)) ->
  (In cell (memory_started_pointer_runtime_footprint package temps) <->
    exists access coordinates,
      In access (memory_linear_pointer_accesses (param_pointer_region_code (started_pointer_package package))) /\
      memory_started_axis_coordinates start (upper::counts) coordinates /\
      cell = memory_param_axis_pointer_access_cell access
        (coordinates++memory_recursive_parameters (param_pointer_region_parameters (started_pointer_package package)) temps)).
Proof.
  intros WORDS RANGES START ROOT; rewrite (memory_started_pointer_runtime_footprint_exact package WORDS RANGES START ROOT).
  rewrite in_flat_map; split.
  - intros [coordinates [COORDINATES CELL]].
    apply memory_started_rectangular_points_member in COORDINATES; apply in_map_iff in CELL as [access [SAME MEMBER]].
    exists access,coordinates; auto.
  - intros [access [coordinates [MEMBER [COORDINATES ->]]]].
    exists coordinates; split; [apply memory_started_rectangular_points_member; exact COORDINATES|].
    apply in_map_iff; exists access; auto.
Qed.
Print Assumptions memory_started_pointer_source_runtime_domain.
Print Assumptions memory_started_pointer_runtime_footprint_exact.
Print Assumptions memory_started_pointer_footprint_member.
