From Stdlib Require Import List Bool ZArith Lia.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion.
From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryRuntime GuardMemoryLoops
  GuardMemoryArrayBackend GuardMemoryVectorChecker.
From GuardMemory Require Import GuardMemoryWindowPackage GuardMemoryWindowStartedPackage GuardMemoryWindowPackageBounds GuardMemoryWindowStaticBounds
  GuardMemoryWindowSyntax GuardMemoryWindowCompiler GuardMemoryWindowTiling.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition check_window_tiled_package live pool source (package : window_started_package source) bi bj :=
  let base := window_started_base package in
  let dimensions := length (memory_nest_iterators (window_region_nest base)) in
  let scalars := length (window_region_parameters base++window_region_scalars base) in
  let candidate := window_tiled_loop dimensions scalars (window_region_instructions base) (window_region_root_lower base) bi bj in
  if (2 <=? dimensions)%nat && (window_region_root_lower base <=? 0) && (0 <? bi) && (0 <? bj) then
    check_window_region_candidate live pool package candidate
      (checked_window_tiling (window_package_static_bounds package) (window_package_loop package)
        dimensions scalars (window_region_instructions base) (window_package_context package)
        (window_region_pointers base) (window_region_root_lower base) bi bj)
  else pure None.
Theorem check_window_tiled_package_sound live pool source (package : window_started_package source) bi bj target :
  mayReturn (check_window_tiled_package live pool package bi bj) (Some target) -> projected_region_contract live source target.
Proof.
  unfold check_window_tiled_package.
  destruct ((2 <=? length (memory_nest_iterators (window_region_nest (window_started_base package))))%nat &&
    (window_region_root_lower (window_started_base package) <=? 0) && (0 <? bi) && (0 <? bj)) eqn:SIZE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  rewrite !andb_true_iff,Nat.leb_le,Z.leb_le,Z.ltb_lt,Z.ltb_lt in SIZE.
  destruct SIZE as [[[DIMENSIONS LOWER] BI] BJ].
  apply check_window_region_candidate_sound.
  pose proof (window_source_caps_length (window_region_certificate (window_started_base package))) as LENGTH.
  destruct (window_region_caps (window_started_base package)) as [|first [|second rest]] eqn:CAPS; cbn in LENGTH; try lia.
  eapply checked_window_tiling_correct with (first_cap := first) (second_cap := second).
  - unfold window_package_static_bounds,window_static_base_bounds; rewrite CAPS; reflexivity.
  - unfold window_package_static_bounds,window_static_base_bounds; rewrite CAPS; reflexivity.
  - unfold window_package_context; rewrite !length_app; cbn [length].
    pose proof (memory_nest_lengths (window_region_nest (window_started_base package))); lia.
  - exact LOWER.
  - exact BI.
  - exact BJ.
Qed.
Print Assumptions check_window_tiled_package_sound.
