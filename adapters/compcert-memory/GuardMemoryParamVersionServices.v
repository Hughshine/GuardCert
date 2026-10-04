From Stdlib Require Import List Bool ZArith Lia.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryAffineReindex
  GuardMemoryRecursiveSource GuardMemoryRecursiveCandidate GuardMemoryRecursiveChecker
  GuardMemoryScalarChecker GuardMemoryScalarLoops GuardMemoryScalarCandidates GuardMemoryScalarTiling
  GuardMemoryScheduleProducer GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerCompiler
  GuardMemoryRecursiveSyntax GuardMemoryTiledCompiler.
From GuardMemory Require Import GuardMemoryAxisPointerCompiler GuardMemoryArrayBackend.
From GuardMemory Require Import GuardMemoryArrayBackend.
From GuardMemory Require Import GuardMemoryVectorChecker GuardMemoryVectorTiling.
From GuardMemory Require Import GuardMemoryParamPointerSyntax GuardMemoryParamPointerProjectedCandidate GuardMemoryParamPointerBounds GuardMemoryParamAxisCompiler.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.
Local Open Scope Z_scope.

From GuardMemory Require Import GuardMemoryParamAxisServices GuardMemoryParamAxisDescribe.
From GuardMemory Require Import GuardMemoryVersionFamily GuardMemoryParamVersionComponents.
Theorem check_memory_param_axis_pointer_mapped_package_components_sound live pool source (package : memory_param_pointer_region_package source)
  candidate steps target :
  mayReturn (check_memory_param_axis_pointer_mapped_package live pool package candidate steps) (Some target) ->
  exists components, memory_peel_guard_components target = Some components /\
    memory_version_components_valid live source components.
Proof.
  unfold check_memory_param_axis_pointer_mapped_package; apply check_memory_param_axis_pointer_region_components_sound;
    apply checked_memory_bounded_candidate_correct.
Qed.

Theorem check_memory_param_axis_pointer_scheduled_package_components_sound live pool source (package : memory_param_pointer_region_package source)
  schedules steps target :
  mayReturn (check_memory_param_axis_pointer_scheduled_package live pool package schedules steps) (Some target) ->
  exists components, memory_peel_guard_components target = Some components /\
    memory_version_components_valid live source components.
Proof.
  unfold check_memory_param_axis_pointer_scheduled_package; intro RUN;
    bind_imp_destruct RUN candidate GENERATED; destruct candidate as [candidate|];
    [eapply check_memory_param_axis_pointer_mapped_package_components_sound; exact RUN|apply mayReturn_pure in RUN; discriminate].
Qed.

Theorem check_memory_param_axis_pointer_tiled_package_components_sound live pool source (package : memory_param_pointer_region_package source) bi bj target :
  mayReturn (check_memory_param_axis_pointer_tiled_package live pool package bi bj) (Some target) ->
  exists components, memory_peel_guard_components target = Some components /\
    memory_version_components_valid live source components.
Proof.
  unfold check_memory_param_axis_pointer_tiled_package.
  destruct ((2 <=? length (memory_nest_iterators (param_pointer_region_nest package)))%nat && (0 <? bi) && (0 <? bj)) eqn:SIZE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  rewrite !andb_true_iff,Nat.leb_le,Z.ltb_lt,Z.ltb_lt in SIZE; destruct SIZE as [[DIMENSIONS BI] BJ].
  apply check_memory_param_axis_pointer_region_components_sound.
  pose proof (param_pointer_region_limits_length (param_pointer_region_syntax package)) as LENGTH.
  destruct (param_pointer_region_limits package) as [|first [|second rest]] eqn:LIMITS; cbn in LENGTH; try lia.
  eapply checked_memory_bounded_tiling_correct with (first_cap := first) (second_cap := second).
  - unfold memory_param_static_bounds; reflexivity.
  - unfold memory_param_static_bounds; reflexivity.
  - unfold memory_param_pointer_region_context,memory_param_pointer_runtime_context,memory_param_pointer_region_arity;
      rewrite !length_app; f_equal; symmetry; apply memory_nest_lengths.
  - exact DIMENSIONS.
  - exact BI.
  - exact BJ.
Qed.
