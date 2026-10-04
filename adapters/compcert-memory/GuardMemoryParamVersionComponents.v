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
From GuardMemory Require Import GuardMemoryVersionFamily.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.
Local Open Scope Z_scope.

From GuardMemory Require Import GuardMemoryParamAxisCompiler.

Definition memory_peel_guard_components target : option memory_version_components :=
  match target with
  | Sloop (Ssequence (Sswitch _ (LScons _ (Ssequence check (Ssequence candidate Scontinue)) LSnil)) _) Sbreak =>
      Some (check,candidate)
  | _ => None
  end.
Lemma memory_peel_guard_components_exact check candidate source :
  memory_peel_guard_components (memory_sequential_guarded_statement check candidate source) = Some (check,candidate).
Proof. reflexivity. Qed.

Theorem memory_param_axis_pointer_components_valid source (package : memory_param_pointer_region_package source)
  live pairs candidate code left_counters right_counters flag :
  memory_param_axis_pointer_guard_names_check package live left_counters right_counters flag = true ->
  compile_memory_param_pointer_region_candidate package live pairs candidate = Some code ->
  memory_bounded_candidate_certificate (memory_param_static_bounds (param_pointer_region_limits package)
      (param_pointer_region_parameter_limits package) (length (param_pointer_region_scalars package))) (length (memory_nest_iterators (param_pointer_region_nest package)))
    (memory_param_pointer_region_arity package)
    (memory_param_pointer_region_instructions package) (memory_param_pointer_region_context package) candidate ->
  memory_version_components_valid live source
    (memory_param_axis_pointer_guard_statement package left_counters right_counters flag,
      memory_recursive_candidate code (param_pointer_region_nest package)).
Proof.
  intros NAMES COMPILE CHECK.
  destruct (@memory_param_axis_pointer_guard_names_sound source package live left_counters right_counters flag NAMES)
    as [LEFT [RIGHT [UNIQUE [LEFT_PARAM [RIGHT_PARAM [FRESH FLAG]]]]]].
  exists (@memory_param_pointer_projected_candidate_rule source package live pairs candidate code COMPILE CHECK).
  intros fe s DOMAIN; eapply memory_param_axis_pointer_guard_execution; eassumption.
Qed.

Theorem check_memory_param_axis_pointer_region_components_sound live pool source (package : memory_param_pointer_region_package source)
  candidate check target :
  (mayReturn check true -> memory_bounded_candidate_certificate (memory_param_static_bounds (param_pointer_region_limits package)
      (param_pointer_region_parameter_limits package) (length (param_pointer_region_scalars package)))
    (length (memory_nest_iterators (param_pointer_region_nest package))) (memory_param_pointer_region_arity package) (memory_param_pointer_region_instructions package)
    (memory_param_pointer_region_context package) candidate) ->
  mayReturn (check_memory_param_axis_pointer_region_candidate live pool package candidate check) (Some target) ->
  exists components, memory_peel_guard_components target = Some components /\
    memory_version_components_valid live source components.
Proof.
  intros CERT; unfold check_memory_param_axis_pointer_region_candidate.
  destruct (Nat.leb (length (memory_linear_pointer_accesses (param_pointer_region_code package))) 32%nat);
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (private_counter_pairs pool) as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (nth_error pairs (length (memory_nest_iterators (param_pointer_region_nest package)))) as [[flag spare]|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (memory_param_axis_pointer_guard_names_check package live
    (map fst (firstn (length (memory_nest_iterators (param_pointer_region_nest package))) pairs))
    (map snd (firstn (length (memory_nest_iterators (param_pointer_region_nest package))) pairs)) flag) eqn:NAMES;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_memory_param_pointer_region_candidate package live pairs candidate) as [code|] eqn:COMPILE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN;
    destruct valid; [inversion RUN; subst target|discriminate].
  eexists; split.
  - apply memory_peel_guard_components_exact.
  - eapply memory_param_axis_pointer_components_valid; [exact NAMES|exact COMPILE|apply CERT; exact VALID].
Qed.
