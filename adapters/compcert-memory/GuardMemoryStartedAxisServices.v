From Stdlib Require Import List Bool ZArith Lia.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryAffineReindex
  GuardMemoryScalarCandidates GuardMemoryScheduleProducer GuardMemoryArrayBackend GuardMemoryVectorChecker
  GuardMemoryScalarTiling GuardMemoryRecursiveSource GuardMemoryParamPointerSyntax
  GuardMemoryParamPointerBounds GuardMemoryParamPointerProjectedCandidate.
From GuardMemory Require Import GuardMemoryStartedPackage GuardMemoryStartedPointerBounds GuardMemoryStartedAxisCompiler
  GuardMemoryBoundedSourceChecker GuardMemoryBoundedSourceTiling GuardMemoryStartedScalarTiling.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition check_memory_started_axis_pointer_mapped_package live pool source (package : memory_started_pointer_package source)
  raw_candidate steps :=
  let dimensions := length (memory_nest_iterators (param_pointer_region_nest (started_pointer_package package))) in
  let candidate := memory_carry_scalar_arguments O dimensions (memory_started_pointer_region_arity package) raw_candidate in
  check_memory_started_axis_pointer_region_candidate live pool package candidate
    (checked_memory_bounded_source_candidate (memory_started_static_bounds package) (memory_started_pointer_loop package)
      (memory_started_pointer_region_context package) (memory_started_pointer_region_arrays package) candidate steps).
Theorem check_memory_started_axis_pointer_mapped_package_sound live pool source (package : memory_started_pointer_package source)
  candidate steps target :
  mayReturn (check_memory_started_axis_pointer_mapped_package live pool package candidate steps) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_started_axis_pointer_mapped_package; apply check_memory_started_axis_pointer_region_candidate_sound;
    apply checked_memory_bounded_source_candidate_correct.
Qed.
(** Generate with count constraints only. Scalar signed32 ranges remain in the
    independent validator and lowerer: their negated lower bound cannot safely
    be emitted as a machine integer expression at Int.min_signed. *)
Definition check_memory_started_axis_pointer_scheduled_package live pool source (package : memory_started_pointer_package source)
  schedules steps :=
  let context := memory_started_pointer_region_context package in
  let vars := map (fun identifier => (identifier,tt)) (context++memory_started_pointer_region_arrays package) in
  BIND candidate <- memory_generate_scheduled_loop
    (memory_bounded_assumed_loop
      (map (fun cap => MemoryNested.A.Interval 1 cap) (param_pointer_region_limits (started_pointer_package package)))
      (memory_started_pointer_loop package),context,vars) schedules -;
  match candidate with
  | Some candidate => check_memory_started_axis_pointer_mapped_package live pool package candidate steps
  | None => pure None end.
Theorem check_memory_started_axis_pointer_scheduled_package_sound live pool source (package : memory_started_pointer_package source)
  schedules steps target :
  mayReturn (check_memory_started_axis_pointer_scheduled_package live pool package schedules steps) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_started_axis_pointer_scheduled_package; intro RUN;
    bind_imp_destruct RUN candidate GENERATED; destruct candidate as [candidate|];
    [eapply check_memory_started_axis_pointer_mapped_package_sound; exact RUN|apply mayReturn_pure in RUN; discriminate].
Qed.
Definition check_memory_started_axis_pointer_tiled_package live pool source (package : memory_started_pointer_package source) bi bj :=
  let dimensions := length (memory_nest_iterators (param_pointer_region_nest (started_pointer_package package))) in
  let candidate := memory_started_scalar_tiled_loop dimensions (memory_started_pointer_region_arity package)
    (memory_param_pointer_region_instructions (started_pointer_package package)) bi bj in
  if (2 <=? dimensions)%nat && (0 <? bi) && (0 <? bj) then
    check_memory_started_axis_pointer_region_candidate live pool package candidate
      (checked_memory_started_scalar_tiling (memory_started_static_bounds package) (memory_started_pointer_loop package)
        dimensions (memory_started_pointer_region_arity package) (memory_param_pointer_region_instructions (started_pointer_package package))
        (memory_started_pointer_region_context package) (memory_started_pointer_region_arrays package)
        bi bj)
  else pure None.
Theorem check_memory_started_axis_pointer_tiled_package_sound live pool source (package : memory_started_pointer_package source) bi bj target :
  mayReturn (check_memory_started_axis_pointer_tiled_package live pool package bi bj) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_started_axis_pointer_tiled_package.
  destruct ((2 <=? length (memory_nest_iterators (param_pointer_region_nest (started_pointer_package package))))%nat && (0 <? bi) && (0 <? bj)) eqn:SIZE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  rewrite !andb_true_iff,Nat.leb_le,Z.ltb_lt,Z.ltb_lt in SIZE; destruct SIZE as [[DIMENSIONS BI] BJ].
  apply check_memory_started_axis_pointer_region_candidate_sound.
  pose proof (param_pointer_region_limits_length (param_pointer_region_syntax (started_pointer_package package))) as LENGTH.
  destruct (param_pointer_region_limits (started_pointer_package package)) as [|first [|second rest]] eqn:LIMITS; cbn in LENGTH; try lia.
  eapply checked_memory_started_scalar_tiling_correct with (first_cap := first) (second_cap := second).
  - unfold memory_started_static_bounds,memory_param_static_bounds; rewrite LIMITS; reflexivity.
  - unfold memory_started_static_bounds,memory_param_static_bounds; rewrite LIMITS; reflexivity.
  - unfold memory_started_pointer_region_context,memory_started_pointer_context,memory_param_pointer_runtime_context;
      rewrite !length_app; cbn [length].
    pose proof (memory_nest_lengths (param_pointer_region_nest (started_pointer_package package))); lia.
  - exact BI.
  - exact BJ.
Qed.
Print Assumptions check_memory_started_axis_pointer_mapped_package_sound.
Print Assumptions check_memory_started_axis_pointer_scheduled_package_sound.
Print Assumptions check_memory_started_axis_pointer_tiled_package_sound.
