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
From GuardInterface Require Import ClightParamPointerPreservation.
From GuardMemory Require Import GuardMemoryParamAxisDescribe.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.
Local Open Scope Z_scope.

Record pointer_preserving_request := PointerPreservingRequest {
  pointer_request_instructions : list memory_instruction;
  pointer_request_coordinates : nat;
  pointer_request_context_arity : nat;
  pointer_request_limits : list Z;
  pointer_request_parameter_limits : list Z
}.
Inductive pointer_preserving_proposal :=
| PointerMappedProposal (candidate : L.stmt) (steps : list memory_affine_reindex)
| PointerTilingProposal (rows columns : Z)
| PointerScheduleProposal (schedules : list (list (list Z * Z))) (steps : list memory_affine_reindex).
Definition pointer_preserving_proposer := pointer_preserving_request -> option pointer_preserving_proposal.

Definition check_private_scan_param_pointer_mapped_package live pool source (package : memory_param_pointer_region_package source)
  raw_candidate steps :=
  let dimensions := length (memory_nest_iterators (param_pointer_region_nest package)) in
  let candidate := memory_carry_scalar_arguments 0 dimensions (memory_param_pointer_region_arity package) raw_candidate in
  check_private_scan_param_pointer_candidate live pool package candidate
    (checked_memory_bounded_candidate (memory_param_static_bounds (param_pointer_region_limits package)
      (param_pointer_region_parameter_limits package) (length (param_pointer_region_scalars package))) dimensions
      (memory_param_pointer_region_arity package) (memory_param_pointer_region_instructions package)
      (memory_param_pointer_region_context package) (memory_param_pointer_region_arrays package) candidate steps).
Theorem check_private_scan_param_pointer_mapped_package_sound live pool source (package : memory_param_pointer_region_package source)
  candidate steps target :
  mayReturn (check_private_scan_param_pointer_mapped_package live pool package candidate steps) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_private_scan_param_pointer_mapped_package; apply check_private_scan_param_pointer_candidate_sound;
    apply checked_memory_bounded_candidate_correct.
Qed.

Definition check_private_scan_param_pointer_scheduled_package live pool source (package : memory_param_pointer_region_package source)
  schedules steps :=
  let dimensions := length (memory_nest_iterators (param_pointer_region_nest package)) in
  let context := memory_param_pointer_region_context package in
  let vars := map (fun identifier => (identifier,tt)) (context++memory_param_pointer_region_arrays package) in
  BIND candidate <- memory_generate_scheduled_loop
    (memory_bounded_assumed_loop (map (fun cap => MemoryNested.A.Interval 1 cap) (param_pointer_region_limits package))
      (memory_scalar_rectangle 0 dimensions (memory_param_pointer_region_arity package)
        (memory_param_pointer_region_instructions package)),context,vars) schedules -;
  match candidate with
  | Some candidate => check_private_scan_param_pointer_mapped_package live pool package candidate steps
  | None => pure None end.
Theorem check_private_scan_param_pointer_scheduled_package_sound live pool source (package : memory_param_pointer_region_package source)
  schedules steps target :
  mayReturn (check_private_scan_param_pointer_scheduled_package live pool package schedules steps) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_private_scan_param_pointer_scheduled_package; intro RUN;
    bind_imp_destruct RUN candidate GENERATED; destruct candidate as [candidate|];
    [eapply check_private_scan_param_pointer_mapped_package_sound; exact RUN|apply mayReturn_pure in RUN; discriminate].
Qed.

Definition check_private_scan_param_pointer_tiled_package live pool source (package : memory_param_pointer_region_package source) bi bj :=
  let dimensions := length (memory_nest_iterators (param_pointer_region_nest package)) in
  if (2 <=? dimensions)%nat && (0 <? bi) && (0 <? bj) then
    check_private_scan_param_pointer_candidate live pool package
      (memory_scalar_tiled_loop dimensions (memory_param_pointer_region_arity package)
        (memory_param_pointer_region_instructions package) bi bj true)
      (checked_memory_bounded_tiling (memory_param_static_bounds (param_pointer_region_limits package)
        (param_pointer_region_parameter_limits package) (length (param_pointer_region_scalars package))) dimensions (memory_param_pointer_region_arity package)
        (memory_param_pointer_region_instructions package) (memory_param_pointer_region_context package)
        (memory_param_pointer_region_arrays package) bi bj)
  else pure None.
Theorem check_private_scan_param_pointer_tiled_package_sound live pool source (package : memory_param_pointer_region_package source) bi bj target :
  mayReturn (check_private_scan_param_pointer_tiled_package live pool package bi bj) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_private_scan_param_pointer_tiled_package.
  destruct ((2 <=? length (memory_nest_iterators (param_pointer_region_nest package)))%nat && (0 <? bi) && (0 <? bj)) eqn:SIZE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  rewrite !andb_true_iff,Nat.leb_le,Z.ltb_lt,Z.ltb_lt in SIZE; destruct SIZE as [[DIMENSIONS BI] BJ].
  apply check_private_scan_param_pointer_candidate_sound.
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
Print Assumptions check_private_scan_param_pointer_tiled_package_sound.

Print Assumptions check_private_scan_param_pointer_mapped_package_sound.
Print Assumptions check_private_scan_param_pointer_scheduled_package_sound.

Definition pointer_preserving_request_of source (package : memory_param_pointer_region_package source) :=
  PointerPreservingRequest (memory_param_pointer_region_instructions package)
    (length (memory_nest_iterators (param_pointer_region_nest package)))
    (length (memory_param_pointer_region_context package)) (param_pointer_region_limits package)
    (param_pointer_region_parameter_limits package).
Definition check_private_scan_param_pointer_source live pool (propose : pointer_preserving_proposer) source :=
  @check_memory_param_axis_profiles source
    (fun package => match propose (pointer_preserving_request_of package) with
      | Some (PointerMappedProposal candidate steps) =>
          check_private_scan_param_pointer_mapped_package live pool package candidate steps
      | Some (PointerTilingProposal rows columns) =>
          check_private_scan_param_pointer_tiled_package live pool package rows columns
      | Some (PointerScheduleProposal schedules steps) =>
          check_private_scan_param_pointer_scheduled_package live pool package schedules steps
      | None => pure None end) (propose_memory_param_axis_profiles source).
Theorem check_private_scan_param_pointer_source_sound live pool propose source target :
  mayReturn (check_private_scan_param_pointer_source live pool propose source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_private_scan_param_pointer_source; intro RUN.
  eapply check_memory_param_axis_profiles_sound; [|exact RUN].
  intros package chosen ACCEPTED; cbn beta in ACCEPTED.
  destruct (propose (pointer_preserving_request_of package)) as [proposal|].
  - destruct proposal.
    + eapply check_private_scan_param_pointer_mapped_package_sound; exact ACCEPTED.
    + eapply check_private_scan_param_pointer_tiled_package_sound; exact ACCEPTED.
    + eapply check_private_scan_param_pointer_scheduled_package_sound; exact ACCEPTED.
  - apply mayReturn_pure in ACCEPTED; discriminate.
Qed.

Print Assumptions check_private_scan_param_pointer_source_sound.
