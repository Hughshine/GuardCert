From Stdlib Require Import List ZArith.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion.
From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryRuntime GuardMemoryLoops GuardMemoryArrayBackend GuardMemoryAffineReindex
  GuardMemoryScalarCandidates GuardMemoryScheduleProducer GuardMemoryVectorChecker GuardMemoryBoundedSourceChecker.
From GuardMemory Require Import GuardMemoryWindowPackage GuardMemoryWindowStartedPackage GuardMemoryWindowPackageBounds GuardMemoryWindowCompiler.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.
Definition check_window_mapped_package live pool source (package : window_started_package source) raw_candidate steps :=
  let base := window_started_base package in
  let dimensions := length (memory_nest_iterators (window_region_nest base)) in
  let arity := length (window_region_parameters base++window_region_scalars base) in
  let candidate := memory_carry_scalar_arguments O dimensions arity raw_candidate in
  check_window_region_candidate live pool package candidate
    (checked_memory_bounded_source_candidate (window_package_static_bounds package) (window_package_loop package)
      (window_package_context package) (window_region_pointers base) candidate steps).
Theorem check_window_mapped_package_sound live pool source (package : window_started_package source) candidate steps target :
  mayReturn (check_window_mapped_package live pool package candidate steps) (Some target) -> projected_region_contract live source target.
Proof.
  unfold check_window_mapped_package; apply check_window_region_candidate_sound; apply checked_memory_bounded_source_candidate_correct.
Qed.
Definition check_window_scheduled_package live pool source (package : window_started_package source) schedules steps :=
  let context := window_package_context package in
  let vars := map (fun identifier => (identifier,tt)) (context++window_region_pointers (window_started_base package)) in
  BIND candidate <- memory_generate_scheduled_loop
    (memory_bounded_assumed_loop (map (fun cap => MemoryNested.A.Interval 1 cap) (window_region_caps (window_started_base package)))
      (window_package_loop package),context,vars) schedules -;
  match candidate with Some candidate => check_window_mapped_package live pool package candidate steps | None => pure None end.
Theorem check_window_scheduled_package_sound live pool source (package : window_started_package source) schedules steps target :
  mayReturn (check_window_scheduled_package live pool package schedules steps) (Some target) -> projected_region_contract live source target.
Proof.
  unfold check_window_scheduled_package; intro RUN; bind_imp_destruct RUN candidate GENERATED;
    destruct candidate as [candidate|]; [eapply check_window_mapped_package_sound; exact RUN|apply mayReturn_pure in RUN; discriminate].
Qed.
Print Assumptions check_window_mapped_package_sound.
Print Assumptions check_window_scheduled_package_sound.
