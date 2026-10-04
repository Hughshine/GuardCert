From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightNoWrap.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryLoopTrace GuardMemoryRecursiveSource
  GuardMemoryRecursiveDomain GuardMemoryFiniteFootprint GuardMemoryFootprintCapabilities.
From GuardMemory Require Import GuardMemoryWindowPackage GuardMemoryWindowStartedPackage GuardMemoryWindowPackageHeader GuardMemoryWindowPackageBounds
  GuardMemoryWindowSourceDomain GuardMemoryWindowCells.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition window_runtime_footprint source (package : window_started_package source) temps :=
  memory_events_footprint (memory_loop_trace (window_package_loop package)
    (memory_recursive_parameters (window_package_context package) temps)).
Definition window_runtime_domain source (package : window_started_package source) s :=
  window_package_header_domain package s /\
  (window_package_header_accept package s = true ->
    Forall (memory_cell_capable (window_multi_pointer_locations (entry_temps s)
      (window_region_lower (window_started_base package)) (window_region_upper (window_started_base package))) (entry_memory s))
      (window_runtime_footprint package (entry_temps s))).
Theorem window_source_runtime_domain source (package : window_started_package source)
  fe ge locals temps memory after final :
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  window_runtime_domain package (Entry ge locals temps memory).
Proof.
  intro SOURCE.
  pose proof (@window_package_source_header_domain source package fe ge locals temps memory after final SOURCE) as DOMAIN.
  split; [exact DOMAIN|]; intro ACCEPT.
  destruct (@window_package_header_sound source package (Entry ge locals temps memory) DOMAIN ACCEPT)
    as [ACTIVE [ROOT [RANGES PARAM_RANGES]]].
  destruct (@window_source_under_ranges source (window_started_base package)
    (window_started_iterator package) (window_started_bound package) (window_started_body package) (window_started_child package)
    fe ge locals temps memory after final (window_started_nest package) ACTIVE RANGES PARAM_RANGES SOURCE)
    as [PARAMETERS [SCALARS [LOOP EXIT]]].
  pose proof (@memory_loop_source_capabilities _ _
    (RuntimeState (window_multi_pointer_locations temps (window_region_lower (window_started_base package))
      (window_region_upper (window_started_base package))) memory)
    (RuntimeState (window_multi_pointer_locations temps (window_region_lower (window_started_base package))
      (window_region_upper (window_started_base package))) final)
    (window_multi_pointer_locations_int32 temps (window_region_lower (window_started_base package))
      (window_region_upper (window_started_base package))) LOOP) as CAPABLE.
  unfold window_runtime_footprint,window_package_loop,window_package_context,memory_recursive_parameters.
  rewrite !map_app; cbn [map]; repeat rewrite <-app_assoc.
  repeat rewrite <-app_assoc in CAPABLE.
  apply Forall_forall; intros cell MEMBER.
  unfold memory_events_footprint in MEMBER; apply in_flat_map in MEMBER as [event [EVENT ACCESS]].
  apply Forall_forall with (x := event) in CAPABLE; [|exact EVENT].
  apply Forall_forall with (x := cell) in CAPABLE; [exact CAPABLE|exact ACCESS].
Qed.
Print Assumptions window_source_runtime_domain.
