From Stdlib Require Import List Bool ZArith.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRule ClightPrivateRegion ClightRectangularSelector.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryLoops GuardMemorySequenceLoops
  GuardMemoryNamedOperations GuardMemoryNamedRegistrySource GuardMemoryAffineReindex
  GuardMemoryNamedCompiler GuardMemoryNamedMappedCompiler GuardMemoryNamedRaggedCompiler
  GuardMemoryRaggedLoops GuardMemoryNamedRaggedChecker GuardMemoryProposedClight GuardMemoryScheduleProducer.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.

Definition check_memory_ragged_scheduled_region live pool schedules steps source : CoreAlarmed.Base.imp (option statement) :=
  match describe_memory_ragged source with
  | Some package =>
    let d := ragged_description package in
    let instructions := map named_operation_instruction (ragged_operations package) in
    let context := [rectangle_bound d;ragged_parameter package] in
    let vars := map (fun array => (array,tt)) (context++flat_map named_operation_arrays (ragged_operations package)) in
    BIND candidate <- memory_generate_scheduled_loop
      (memory_ragged_assumed_loop (described_shape d) (memory_ragged_sequence instructions),context,vars)
      schedules -;
    match candidate with
    | Some candidate => check_memory_ragged_mapped_region live pool (fun _ => Some (candidate,steps)) source
    | None => pure None end
  | None => pure None end.
Theorem check_memory_ragged_scheduled_region_sound live pool schedules steps source target :
  mayReturn (check_memory_ragged_scheduled_region live pool schedules steps source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_ragged_scheduled_region.
  destruct (describe_memory_ragged source) as [package|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN generated GENERATED.
  destruct generated as [candidate|]; [|apply mayReturn_pure in RUN; discriminate].
  eapply check_memory_ragged_mapped_region_sound; exact RUN.
Qed.
Definition check_memory_named_scheduled_region live pool schedules steps source : CoreAlarmed.Base.imp (option statement) :=
  match describe_memory_named source with
  | Some package =>
    let d := named_description package in
    let instructions := map named_operation_instruction (named_operations package) in
    let context := [rectangle_bound d;rectangle_inner_bound d] in
    let vars := map (fun array => (array,tt)) (context++flat_map named_operation_arrays (named_operations package)) in
    BIND candidate <- memory_generate_scheduled_loop
      (memory_array_assumed_loop (described_shape d) (memory_rectangle_sequence instructions),context,vars)
      schedules -;
    match candidate with
    | Some candidate => check_memory_named_mapped_region live pool (fun _ => Some (candidate,steps)) source
    | None => pure None end
  | None => check_memory_ragged_scheduled_region live pool schedules steps source end.
Theorem check_memory_named_scheduled_region_sound live pool schedules steps source target :
  mayReturn (check_memory_named_scheduled_region live pool schedules steps source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_named_scheduled_region.
  destruct (describe_memory_named source) as [package|];
    [|apply check_memory_ragged_scheduled_region_sound].
  intro RUN; bind_imp_destruct RUN generated GENERATED.
  destruct generated as [candidate|]; [|apply mayReturn_pure in RUN; discriminate].
  eapply check_memory_named_mapped_region_sound; exact RUN.
Qed.
Print Assumptions check_memory_named_scheduled_region_sound.
