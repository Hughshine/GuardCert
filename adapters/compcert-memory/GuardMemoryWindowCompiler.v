From Stdlib Require Import List Bool ZArith.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion ClightCondition.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryRecursiveSource GuardMemoryRecursiveCandidate
  GuardMemorySequentialCondition GuardMemoryProjectedCondition GuardMemoryTiledCompiler GuardMemoryBoundedSourceChecker.
From GuardMemory Require Import GuardMemoryWindowPackage GuardMemoryWindowStartedPackage GuardMemoryWindowPackageHeader GuardMemoryWindowPackageBounds GuardMemoryWindowBackend GuardMemoryWindowCandidate.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.
Definition window_region_target source (package : window_started_package source) code :=
  memory_sequential_guarded_statement (tree_statement (window_package_header_tree package) Sskip Sbreak)
    (memory_recursive_candidate code (window_region_nest (window_started_base package))) source.
Theorem window_region_target_sound source (package : window_started_package source) pointer live pool candidate code :
  window_region_pointers (window_started_base package) = [pointer] ->
  compile_window_multi_pointer_buffer_loop (window_region_pointers (window_started_base package))
    (window_package_context package) (window_package_pointer_bounds package) live pool candidate = Some code ->
  memory_bounded_source_certificate (window_package_static_bounds package) (window_package_loop package)
    (window_package_context package) candidate ->
  projected_region_contract live source (window_region_target package code).
Proof.
  intros SINGLE COMPILE CERT; unfold window_region_target.
  eapply memory_projected_private_rule_sound with (rule := @window_single_candidate_rule source package pointer SINGLE live pool candidate code COMPILE CERT).
  intros fe s DOMAIN; exists (window_package_header_accept package s),(entry_temps s); split.
  - apply memory_projected_check_from_exact,memory_decision_check_statement.
    apply (proj2 (window_package_header_exact DOMAIN _)); reflexivity.
  - intro ACCEPT; destruct s; exact ACCEPT.
Qed.
Definition check_window_region_candidate live pool source (package : window_started_package source) candidate (check : CoreAlarmed.Base.imp bool) :=
  match window_region_pointers (window_started_base package),private_counter_pairs pool with
  | [pointer],Some pairs => match compile_window_multi_pointer_buffer_loop [pointer]
      (window_package_context package) (window_package_pointer_bounds package) live pairs candidate with
      | Some code => BIND valid <- check -; pure (if valid then Some (window_region_target package code) else None)
      | None => pure None end
  | _,_ => pure None end.
Theorem check_window_region_candidate_sound live pool source (package : window_started_package source) candidate check target :
  (mayReturn check true -> memory_bounded_source_certificate (window_package_static_bounds package)
    (window_package_loop package) (window_package_context package) candidate) ->
  mayReturn (check_window_region_candidate live pool package candidate check) (Some target) ->
  projected_region_contract live source target.
Proof.
  intros CERT; unfold check_window_region_candidate.
  destruct (window_region_pointers (window_started_base package)) as [|pointer [|other rest]] eqn:POINTERS;
    try (intro RUN; apply mayReturn_pure in RUN; discriminate).
  destruct (private_counter_pairs pool) as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_window_multi_pointer_buffer_loop [pointer] (window_package_context package)
    (window_package_pointer_bounds package) live pairs candidate) as [code|] eqn:COMPILE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN; destruct valid; [|discriminate].
  inversion RUN; subst target.
  eapply window_region_target_sound; [exact POINTERS|rewrite POINTERS; exact COMPILE|apply CERT; exact VALID].
Qed.
Print Assumptions window_region_target_sound.
Print Assumptions check_window_region_candidate_sound.
