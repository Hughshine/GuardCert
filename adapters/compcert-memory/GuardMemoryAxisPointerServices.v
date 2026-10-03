From Stdlib Require Import List Bool ZArith.
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
From GuardMemory Require Import GuardMemoryAxisPointerCompiler.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition check_memory_axis_pointer_mapped_package live pool source (package : memory_multi_pointer_region_package source)
  raw_candidate steps :=
  let dimensions := length (memory_nest_iterators (multi_pointer_region_nest package)) in
  let candidate := memory_carry_scalar_arguments 0 dimensions (memory_multi_pointer_region_arity package) raw_candidate in
  check_memory_axis_pointer_region_candidate live pool package candidate
    (checked_memory_scalar_candidate dimensions (multi_pointer_region_limit package)
      (memory_multi_pointer_region_arity package) (memory_multi_pointer_region_instructions package)
      (memory_multi_pointer_region_context package) (memory_multi_pointer_region_arrays package) candidate steps).
Theorem check_memory_axis_pointer_mapped_package_sound live pool source (package : memory_multi_pointer_region_package source)
  candidate steps target :
  mayReturn (check_memory_axis_pointer_mapped_package live pool package candidate steps) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_axis_pointer_mapped_package; apply check_memory_axis_pointer_region_candidate_sound;
    apply checked_memory_scalar_candidate_correct.
Qed.

Definition check_memory_axis_pointer_scheduled_package live pool source (package : memory_multi_pointer_region_package source)
  schedules steps :=
  let dimensions := length (memory_nest_iterators (multi_pointer_region_nest package)) in
  let context := memory_multi_pointer_region_context package in
  let vars := map (fun identifier => (identifier,tt)) (context++memory_multi_pointer_region_arrays package) in
  BIND candidate <- memory_generate_scheduled_loop
    (memory_recursive_assumed_loop dimensions (multi_pointer_region_limit package)
      (memory_scalar_rectangle 0 dimensions (memory_multi_pointer_region_arity package)
        (memory_multi_pointer_region_instructions package)),context,vars) schedules -;
  match candidate with
  | Some candidate => check_memory_axis_pointer_mapped_package live pool package candidate steps
  | None => pure None end.
Theorem check_memory_axis_pointer_scheduled_package_sound live pool source (package : memory_multi_pointer_region_package source)
  schedules steps target :
  mayReturn (check_memory_axis_pointer_scheduled_package live pool package schedules steps) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_axis_pointer_scheduled_package; intro RUN;
    bind_imp_destruct RUN candidate GENERATED; destruct candidate as [candidate|];
    [eapply check_memory_axis_pointer_mapped_package_sound; exact RUN|apply mayReturn_pure in RUN; discriminate].
Qed.

Definition check_memory_axis_pointer_tiled_package live pool source (package : memory_multi_pointer_region_package source) bi bj :=
  let dimensions := length (memory_nest_iterators (multi_pointer_region_nest package)) in
  if (2 <=? dimensions)%nat && (0 <? bi) && (0 <? bj) then
    check_memory_axis_pointer_region_candidate live pool package
      (memory_scalar_tiled_loop dimensions (memory_multi_pointer_region_arity package)
        (memory_multi_pointer_region_instructions package) bi bj true)
      (checked_memory_scalar_tiling dimensions (multi_pointer_region_limit package) (memory_multi_pointer_region_arity package)
        (memory_multi_pointer_region_instructions package) (memory_multi_pointer_region_context package)
        (memory_multi_pointer_region_arrays package) bi bj)
  else pure None.
Theorem check_memory_axis_pointer_tiled_package_sound live pool source (package : memory_multi_pointer_region_package source) bi bj target :
  mayReturn (check_memory_axis_pointer_tiled_package live pool package bi bj) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_axis_pointer_tiled_package.
  destruct ((2 <=? length (memory_nest_iterators (multi_pointer_region_nest package)))%nat && (0 <? bi) && (0 <? bj)) eqn:SIZE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  rewrite !andb_true_iff,Nat.leb_le,Z.ltb_lt,Z.ltb_lt in SIZE; destruct SIZE as [[DIMENSIONS BI] BJ].
  apply check_memory_axis_pointer_region_candidate_sound; apply checked_memory_scalar_tiling_correct;
    [unfold memory_multi_pointer_region_context,memory_multi_pointer_region_arity;
      rewrite length_app; f_equal; symmetry; apply memory_nest_lengths|exact DIMENSIONS|exact BI|exact BJ].
Qed.
Print Assumptions check_memory_axis_pointer_tiled_package_sound.
