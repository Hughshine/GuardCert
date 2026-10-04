From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryAffineReindex
  GuardMemoryRecursiveSource GuardMemoryRecursiveCandidate GuardMemoryRecursiveChecker
  GuardMemoryScalarChecker GuardMemoryScalarLoops GuardMemoryScalarCandidates GuardMemoryScheduleProducer
  GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerCompiler GuardMemoryMultiPointerProjectedCandidate
  GuardMemoryLinearPointerSyntax GuardMemoryProjectedCondition GuardMemoryRecursiveSyntax
  GuardMemoryTiledCompiler GuardMemorySequentialCondition GuardMemoryStatefulRule.
From GuardMemory Require Import GuardMemoryAxisPointerFrame GuardMemoryAxisPointerGuard.
From GuardMemory Require Import GuardMemoryMultiPointerBackend.
From GuardMemory Require Import GuardMemoryVectorChecker.
From GuardMemory Require Import GuardMemoryParamPointerBounds GuardMemoryParamPointerSyntax GuardMemoryParamPointerProjectedCandidate GuardMemoryParamAxisFrame GuardMemoryParamAxisGuard.
From GuardMemory Require Import GuardMemoryStartedPackage GuardMemoryStartedPointerBounds GuardMemoryStartedPointerCandidate
  GuardMemoryStartedAxisGuard GuardMemoryStartedAxisFrame GuardMemoryBoundedSourceChecker.
From GuardMemory Require Import GuardMemoryWindowPackage GuardMemoryWindowStartedPackage GuardMemoryWindowSyntax GuardMemoryWindowPackageBounds GuardMemoryWindowBackend GuardMemoryWindowProjectedCandidate GuardMemoryWindowAxisGuard GuardMemoryWindowAxisFrame.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition window_axis_region_context source (package : window_started_package source) :=
  window_package_context package.
Definition window_axis_region_arity source (package : window_started_package source) :=
  length (window_region_parameters (window_started_base package)++window_region_scalars (window_started_base package)).
Definition window_axis_region_arrays source (package : window_started_package source) :=
  window_region_pointers (window_started_base package).
Definition compile_window_axis_region_candidate source (package : window_started_package source) live pool candidate :=
  compile_window_multi_pointer_buffer_loop (window_region_pointers (window_started_base package)) (window_axis_region_context package)
    (window_package_pointer_bounds package) live pool candidate.

Definition window_axis_guard_names_check source (package : window_started_package source)
  live left_counters right_counters flag :=
  Nat.eqb (length left_counters) (length (memory_nest_iterators (window_region_nest (window_started_base package)))) &&
  Nat.eqb (length right_counters) (length (memory_nest_iterators (window_region_nest (window_started_base package)))) &&
  memory_identifiers_unique_check ((left_counters++right_counters)++[flag]) &&
  forallb (fun identifier => negb (existsb (Pos.eqb identifier) (window_axis_guard_protected package live)))
    ((left_counters++right_counters)++[flag]) &&
  memory_identifiers_unique_check (left_counters++window_region_parameters (window_started_base package)) &&
  memory_identifiers_unique_check (right_counters++window_region_parameters (window_started_base package)).

Lemma window_axis_guard_names_sound source (package : window_started_package source)
  live left_counters right_counters flag :
  window_axis_guard_names_check package live left_counters right_counters flag = true ->
  length left_counters = length (memory_nest_iterators (window_region_nest (window_started_base package))) /\
  length right_counters = length (memory_nest_iterators (window_region_nest (window_started_base package))) /\
  NoDup (left_counters++right_counters) /\
  NoDup (left_counters++window_region_parameters (window_started_base package)) /\
  NoDup (right_counters++window_region_parameters (window_started_base package)) /\
  (forall identifier, In identifier (left_counters++right_counters) ->
    ~ In identifier (window_axis_guard_protected package live) /\ identifier <> flag) /\
  ~ In flag (window_axis_guard_protected package live).
Proof.
  unfold window_axis_guard_names_check; rewrite !andb_true_iff,!Nat.eqb_eq.
  intros [[[[[LEFT RIGHT] UNIQUE] FRESH] LEFT_PARAM] RIGHT_PARAM].
  apply memory_identifiers_unique_check_sound in LEFT_PARAM,RIGHT_PARAM.
  apply memory_identifiers_unique_check_sound in UNIQUE.
  pose proof (@NoDup_app_remove_r _ (left_counters++right_counters) [flag] UNIQUE) as COUNTERS.
  pose proof (@NoDup_remove_2 _ (left_counters++right_counters) [] flag UNIQUE) as FLAG_PRIVATE.
  rewrite app_nil_r in FLAG_PRIVATE.
  assert (ALL : forall identifier, In identifier ((left_counters++right_counters)++[flag]) ->
    ~ In identifier (window_axis_guard_protected package live)).
  { intros identifier MEMBER BAD; apply forallb_forall with (x := identifier) in FRESH; [|exact MEMBER].
    apply negb_true_iff in FRESH.
    assert (FOUND : existsb (Pos.eqb identifier) (window_axis_guard_protected package live) = true).
    { apply existsb_exists; exists identifier; split; [exact BAD|apply Pos.eqb_refl]. } congruence. }
  split; [exact LEFT|split; [exact RIGHT|split; [exact COUNTERS|split; [exact LEFT_PARAM|split; [exact RIGHT_PARAM|split]]]]].
  - intros identifier MEMBER; split; [apply ALL; apply in_or_app; left; exact MEMBER|].
    intro SAME; subst; apply FLAG_PRIVATE; exact MEMBER.
  - apply ALL; apply in_or_app; right; cbn; auto.
Qed.

Definition window_axis_region_target source (package : window_started_package source)
  left_counters right_counters flag code :=
  memory_sequential_guarded_statement
    (window_axis_guard_statement package left_counters right_counters flag)
    (memory_recursive_candidate code (window_region_nest (window_started_base package))) source.

Theorem window_axis_region_target_sound source (package : window_started_package source)
  live pairs candidate code left_counters right_counters flag :
  window_axis_guard_names_check package live left_counters right_counters flag = true ->
  compile_window_axis_region_candidate package live pairs candidate = Some code ->
  memory_bounded_source_certificate (window_package_static_bounds package) (window_package_loop package)
    (window_axis_region_context package) candidate ->
  projected_region_contract live source
    (window_axis_region_target package left_counters right_counters flag code).
Proof.
  intros NAMES COMPILE CHECK.
  destruct (@window_axis_guard_names_sound source package live left_counters right_counters flag NAMES)
    as [LEFT [RIGHT [UNIQUE [LEFT_PARAM [RIGHT_PARAM [FRESH FLAG]]]]]].
  unfold window_axis_region_target.
  eapply memory_projected_private_rule_stateful_sound with
    (rule := @window_projected_candidate_rule source package live pairs candidate code COMPILE CHECK).
  intros fe s DOMAIN; eapply window_axis_guard_execution; eassumption.
Qed.

Definition check_window_axis_candidate live pool source (package : window_started_package source)
  candidate (check : CoreAlarmed.Base.imp bool) : CoreAlarmed.Base.imp (option statement) :=
  if Nat.leb (length (memory_linear_pointer_accesses (window_region_operations (window_started_base package)))) 32%nat then
  match private_counter_pairs pool with
  | Some pairs =>
      let dimensions := length (memory_nest_iterators (window_region_nest (window_started_base package))) in
      let selected := firstn dimensions pairs in
      let left_counters := map fst selected in
      let right_counters := map snd selected in
      match nth_error pairs dimensions with
      | Some (flag,spare) =>
          if window_axis_guard_names_check package live left_counters right_counters flag then
            match compile_window_axis_region_candidate package live pairs candidate with
            | Some code => BIND valid <- check -;
                pure (if valid then Some (window_axis_region_target package left_counters right_counters flag code) else None)
            | None => pure None end
          else pure None
      | None => pure None end
  | None => pure None end else pure None.

Theorem check_window_axis_candidate_sound live pool source (package : window_started_package source)
  candidate check target :
  (mayReturn check true -> memory_bounded_source_certificate (window_package_static_bounds package) (window_package_loop package)
    (window_axis_region_context package) candidate) ->
  mayReturn (check_window_axis_candidate live pool package candidate check) (Some target) ->
  projected_region_contract live source target.
Proof.
  intros CERT; unfold check_window_axis_candidate.
  destruct (Nat.leb (length (memory_linear_pointer_accesses (window_region_operations (window_started_base package)))) 32%nat);
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (private_counter_pairs pool) as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (nth_error pairs (length (memory_nest_iterators (window_region_nest (window_started_base package))))) as [[flag spare]|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (window_axis_guard_names_check package live
    (map fst (firstn (length (memory_nest_iterators (window_region_nest (window_started_base package)))) pairs))
    (map snd (firstn (length (memory_nest_iterators (window_region_nest (window_started_base package)))) pairs)) flag) eqn:NAMES;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_window_axis_region_candidate package live pairs candidate) as [code|] eqn:COMPILE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN;
    destruct valid; [inversion RUN; subst target|discriminate].
  eapply window_axis_region_target_sound; [exact NAMES|exact COMPILE|apply CERT; exact VALID].
Qed.
Print Assumptions check_window_axis_candidate_sound.
