From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Clight Csyntax Csem Cstrategy SimplExpr SimplExprproof
  SimplLocals SimplLocalsproof.
From compcert.driver Require Import Compiler.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightGuard ClightCondition ClightPrivateRule ClightPrivateRegion
  ClightPrivateRegionProof ClightPrivatePool ClightTempFootprint ClightTempScope
  ClightStructuredProgress ClightRectangularSelector ClightRectangularStore
  ClightRectangularGuard ClightRectangularRegion ClightRectangularLoops GuardCompiler
  ClightFrontendLoopProtocol ClightFrontendRegion ClightStraightLine ClightSharedRegion ClightSyntaxEquality.
From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryAffineSourceContext.
From GuardMemory Require Import GuardMemoryAxisPointerServices GuardMemoryAxisPointerDescribe.
From GuardMemory Require Import GuardMemoryVectorPointerSyntax GuardMemoryVectorAxisCompiler GuardMemoryVectorAxisServices GuardMemoryVectorAxisDescribe.
From GuardMemory Require Import GuardMemoryParamPointerSyntax GuardMemoryParamAxisCompiler GuardMemoryParamAxisServices GuardMemoryParamAxisDescribe.
From GuardMemory Require Import GuardMemoryClightRectangles GuardMemoryCompiler GuardMemoryTiledClight GuardMemoryTiledCompiler
  GuardMemoryArrayFamilyBackend GuardMemoryOperationsClight GuardMemoryOperationsTiledClight GuardMemoryOperationsCompiler
  GuardMemoryInstr GuardMemoryLoops GuardMemoryProposedClight GuardMemoryProposedCompiler
  GuardMemoryNamedOperations GuardMemoryNamedCompiler GuardMemoryAffineReindex GuardMemoryNamedMappedCompiler GuardMemoryNamedRaggedCompiler
  GuardMemoryScheduledCompiler GuardMemoryParametricSyntax GuardMemoryParametricCompiler
  GuardMemoryLayoutCopySyntax GuardMemoryLayoutCopyCompiler
  GuardMemoryParametricRegion GuardMemoryParametricRegionInstances GuardMemoryParametricRegionCompiler GuardMemoryParametricWidthSearch
  GuardMemoryTripleSyntax GuardMemoryTripleCompiler GuardMemoryRecursiveSyntax GuardMemoryRecursiveCompiler GuardMemoryPointerSyntax GuardMemoryPointerCompiler GuardMemoryScalarPointerSyntax GuardMemoryScalarPointerCompiler GuardMemoryScalarArraySyntax GuardMemoryScalarArrayCompiler GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerCompiler GuardMemoryLinearPointerSyntax GuardMemoryLinearPointerPair GuardMemoryLinearPointerCompiler GuardMemoryAffinePointerSyntax GuardMemoryAffinePointerCompiler.
From GuardMemory Require Import GuardMemoryVersionFamily GuardMemoryParamVersionComponents GuardMemoryParamVersionServices GuardMemoryParamVersionGroups.
From GuardMemory Require Import GuardMemoryPrefilterGroups.
Import CoreAlarmed ListNotations PrivateRegion.
Import Clight.
Set Implicit Arguments.
Local Open Scope Z_scope.

Inductive guarded_memory_candidate :=
| GuardedAffineCandidate (candidate : L.stmt) (swaps : list nat)
| GuardedMappedCandidate (candidate : L.stmt) (steps : list memory_affine_reindex)
| GuardedTilingCandidate (rows columns : Z)
| GuardedScheduleCandidate (schedules : list (list (list Z * Z))) (steps : list memory_affine_reindex).
(** Proposal metadata comes from the checked source package. The context arity
    counts loop bounds and stable parameters, including unused columns.
    Correctness remains quantified over every untrusted proposer. *)
From GuardMemory Require Import GuardMemoryStartedPackage GuardMemoryStartedPackageBuilder
  GuardMemoryStartedAxisCompiler GuardMemoryStartedAxisServices.
From GuardMemory Require Import GuardMemoryWindowPackage GuardMemoryWindowStartedPackage GuardMemoryWindowPackageBounds
  GuardMemoryWindowServices GuardMemoryWindowDescribe.
Record guarded_memory_request := BuildGuardedMemoryRequest {
  request_instructions : list memory_instruction;
  request_coordinates : nat;
  request_context_arity : nat;
  request_count_limits : list Z;
  request_address_limits : list Z;
  request_per_axis_bounds : bool;
  request_runtime_versions : bool;
  request_guard_prefilter : bool;
  request_source_loop : option L.stmt;
  request_signed_window : option (Z * list (Z*Z) * Z * Z)
}.
Definition GuardedMemoryRequest instructions coordinates arity :=
  BuildGuardedMemoryRequest instructions coordinates arity [] [] false false false None None.
Definition guarded_memory_proposer := guarded_memory_request -> option guarded_memory_candidate.
Definition memory_multi_pointer_unified_request source (package : memory_multi_pointer_region_package source) :=
  GuardedMemoryRequest (memory_multi_pointer_region_instructions package)
    (length (memory_nest_iterators (multi_pointer_region_nest package))) (length (memory_multi_pointer_region_context package)).
Definition check_memory_finite_multi_pointer_unified_region live pool (propose : guarded_memory_proposer) source :=
  match describe_memory_multi_pointer_region source with
  | Some package => match propose (memory_multi_pointer_unified_request package) with
      | Some (GuardedAffineCandidate candidate swaps) =>
          check_memory_multi_pointer_mapped_region live pool (fun _ => Some (candidate,map MemoryReindexSwap swaps)) source
      | Some (GuardedMappedCandidate candidate steps) =>
          check_memory_multi_pointer_mapped_region live pool (fun _ => Some (candidate,steps)) source
      | Some (GuardedTilingCandidate rows columns) => check_memory_multi_pointer_tiled_region live pool rows columns source
      | Some (GuardedScheduleCandidate schedules steps) => check_memory_multi_pointer_scheduled_region live pool schedules steps source
      | None => CoreAlarmed.Base.pure None end
  | None => CoreAlarmed.Base.pure None end.
Theorem check_memory_finite_multi_pointer_unified_region_sound live pool propose source target :
  mayReturn (check_memory_finite_multi_pointer_unified_region live pool propose source) (Some target) -> projected_region_contract live source target.
Proof.
  unfold check_memory_finite_multi_pointer_unified_region; destruct (describe_memory_multi_pointer_region source) as [package|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (propose (memory_multi_pointer_unified_request package)) as [candidate|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct candidate; intro RUN.
  - eapply check_memory_multi_pointer_mapped_region_sound; exact RUN.
  - eapply check_memory_multi_pointer_mapped_region_sound; exact RUN.
  - eapply check_memory_multi_pointer_tiled_region_sound; exact RUN.
  - eapply check_memory_multi_pointer_scheduled_region_sound; exact RUN.
Qed.
Definition check_memory_linear_pointer_unified_region live pool (propose : guarded_memory_proposer) source :=
  match describe_memory_linear_pointer_pair source with
  | Some package => match propose (memory_multi_pointer_unified_request (linear_pointer_region (linear_pointer_pair_region package))) with
      | Some (GuardedAffineCandidate candidate swaps) =>
          check_memory_linear_pointer_mapped_package live pool package candidate (map MemoryReindexSwap swaps)
      | Some (GuardedMappedCandidate candidate steps) =>
          check_memory_linear_pointer_mapped_package live pool package candidate steps
      | Some (GuardedScheduleCandidate schedules steps) =>
          check_memory_linear_pointer_scheduled_package live pool package schedules steps
      | _ => CoreAlarmed.Base.pure None end
  | None => CoreAlarmed.Base.pure None end.
Theorem check_memory_linear_pointer_unified_region_sound live pool propose source target :
  mayReturn (check_memory_linear_pointer_unified_region live pool propose source) (Some target) -> projected_region_contract live source target.
Proof.
  unfold check_memory_linear_pointer_unified_region; destruct (describe_memory_linear_pointer_pair source) as [package|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (propose (memory_multi_pointer_unified_request (linear_pointer_region (linear_pointer_pair_region package)))) as [candidate|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct candidate; intro RUN.
  - eapply check_memory_linear_pointer_mapped_package_sound; exact RUN.
  - eapply check_memory_linear_pointer_mapped_package_sound; exact RUN.
  - apply mayReturn_pure in RUN; discriminate.
  - eapply check_memory_linear_pointer_scheduled_package_sound; exact RUN.
Qed.
Definition check_memory_affine_pointer_unified_region live pool (propose : guarded_memory_proposer) source :=
  match describe_memory_affine_pointer_region source with
  | Some package => match propose (memory_multi_pointer_unified_request (affine_pointer_region package)) with
      | Some (GuardedAffineCandidate candidate swaps) =>
          check_memory_affine_pointer_mapped_package live pool package candidate (map MemoryReindexSwap swaps)
      | Some (GuardedMappedCandidate candidate steps) =>
          check_memory_affine_pointer_mapped_package live pool package candidate steps
      | Some (GuardedScheduleCandidate schedules steps) =>
          check_memory_affine_pointer_scheduled_package live pool package schedules steps
      | _ => CoreAlarmed.Base.pure None end
  | None => CoreAlarmed.Base.pure None end.
Theorem check_memory_affine_pointer_unified_region_sound live pool propose source target :
  mayReturn (check_memory_affine_pointer_unified_region live pool propose source) (Some target) -> projected_region_contract live source target.
Proof.
  unfold check_memory_affine_pointer_unified_region; destruct (describe_memory_affine_pointer_region source) as [package|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (propose (memory_multi_pointer_unified_request (affine_pointer_region package))) as [candidate|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct candidate; intro RUN.
  - eapply check_memory_affine_pointer_mapped_package_sound; exact RUN.
  - eapply check_memory_affine_pointer_mapped_package_sound; exact RUN.
  - apply mayReturn_pure in RUN; discriminate.
  - eapply check_memory_affine_pointer_scheduled_package_sound; exact RUN.
Qed.
Definition memory_vector_axis_unified_request source (package : memory_vector_pointer_region_package source) :=
  BuildGuardedMemoryRequest (memory_vector_pointer_region_instructions package)
    (length (memory_nest_iterators (vector_pointer_region_nest package)))
    (length (memory_vector_pointer_region_context package)) (vector_pointer_region_limits package) [] true false false None None.
Definition check_memory_vector_axis_unified_region live pool propose source :=
  @check_memory_vector_axis_profiles source
    (fun package => match propose (memory_vector_axis_unified_request package) with
      | Some (GuardedAffineCandidate candidate swaps) =>
          check_memory_vector_axis_pointer_mapped_package live pool package candidate (map MemoryReindexSwap swaps)
      | Some (GuardedMappedCandidate candidate steps) =>
          check_memory_vector_axis_pointer_mapped_package live pool package candidate steps
      | Some (GuardedTilingCandidate rows columns) =>
          check_memory_vector_axis_pointer_tiled_package live pool package rows columns
      | Some (GuardedScheduleCandidate schedules steps) =>
          check_memory_vector_axis_pointer_scheduled_package live pool package schedules steps
      | None => CoreAlarmed.Base.pure None end) (propose_memory_vector_axis_profiles source).
Theorem check_memory_vector_axis_unified_region_sound live pool propose source target :
  mayReturn (check_memory_vector_axis_unified_region live pool propose source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_vector_axis_unified_region; intro RUN.
  eapply check_memory_vector_axis_profiles_sound; [|exact RUN].
  intros package chosen CERT_ACCEPTED; cbn beta in CERT_ACCEPTED.
  destruct (propose (memory_vector_axis_unified_request package)) as [candidate|].
  - destruct candidate.
    + eapply check_memory_vector_axis_pointer_mapped_package_sound; exact CERT_ACCEPTED.
    + eapply check_memory_vector_axis_pointer_mapped_package_sound; exact CERT_ACCEPTED.
    + eapply check_memory_vector_axis_pointer_tiled_package_sound; exact CERT_ACCEPTED.
    + eapply check_memory_vector_axis_pointer_scheduled_package_sound; exact CERT_ACCEPTED.
  - apply mayReturn_pure in CERT_ACCEPTED; discriminate.
Qed.
Definition memory_param_axis_unified_request source (package : memory_param_pointer_region_package source) :=
  BuildGuardedMemoryRequest (memory_param_pointer_region_instructions package)
    (length (memory_nest_iterators (param_pointer_region_nest package)))
    (length (memory_param_pointer_region_context package)) (param_pointer_region_limits package)
    (param_pointer_region_parameter_limits package) true false false None None.
Definition check_memory_param_axis_unified_region live pool propose source :=
  @check_memory_param_axis_profiles source
    (fun package => match propose (memory_param_axis_unified_request package) with
      | Some (GuardedAffineCandidate candidate swaps) =>
          check_memory_param_axis_pointer_mapped_package live pool package candidate (map MemoryReindexSwap swaps)
      | Some (GuardedMappedCandidate candidate steps) =>
          check_memory_param_axis_pointer_mapped_package live pool package candidate steps
      | Some (GuardedTilingCandidate rows columns) =>
          check_memory_param_axis_pointer_tiled_package live pool package rows columns
      | Some (GuardedScheduleCandidate schedules steps) =>
          check_memory_param_axis_pointer_scheduled_package live pool package schedules steps
      | None => CoreAlarmed.Base.pure None end) (propose_memory_param_axis_profiles source).
Theorem check_memory_param_axis_unified_region_sound live pool propose source target :
  mayReturn (check_memory_param_axis_unified_region live pool propose source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_param_axis_unified_region; intro RUN.
  eapply check_memory_param_axis_profiles_sound; [|exact RUN].
  intros package chosen CERT_ACCEPTED; cbn beta in CERT_ACCEPTED.
  destruct (propose (memory_param_axis_unified_request package)) as [candidate|].
  - destruct candidate.
    + eapply check_memory_param_axis_pointer_mapped_package_sound; exact CERT_ACCEPTED.
    + eapply check_memory_param_axis_pointer_mapped_package_sound; exact CERT_ACCEPTED.
    + eapply check_memory_param_axis_pointer_tiled_package_sound; exact CERT_ACCEPTED.
    + eapply check_memory_param_axis_pointer_scheduled_package_sound; exact CERT_ACCEPTED.
  - apply mayReturn_pure in CERT_ACCEPTED; discriminate.
Qed.
Definition memory_param_version_unified_request source (package : memory_param_pointer_region_package source) :=
  BuildGuardedMemoryRequest (memory_param_pointer_region_instructions package)
    (length (memory_nest_iterators (param_pointer_region_nest package)))
    (length (memory_param_pointer_region_context package)) (param_pointer_region_limits package)
    (param_pointer_region_parameter_limits package) true true false None None.
Definition check_memory_param_version_unified_region live pool (propose : guarded_memory_proposer) source :=
  @compile_memory_param_version_groups source
    (fun package => match propose (memory_param_version_unified_request package) with
      | Some (GuardedAffineCandidate candidate swaps) =>
          check_memory_param_axis_pointer_mapped_package live pool package candidate (map MemoryReindexSwap swaps)
      | Some (GuardedMappedCandidate candidate steps) =>
          check_memory_param_axis_pointer_mapped_package live pool package candidate steps
      | Some (GuardedTilingCandidate rows columns) =>
          check_memory_param_axis_pointer_tiled_package live pool package rows columns
      | Some (GuardedScheduleCandidate schedules steps) =>
          check_memory_param_axis_pointer_scheduled_package live pool package schedules steps
      | None => CoreAlarmed.Base.pure None end) (propose_memory_param_version_groups source).
Theorem check_memory_param_version_unified_region_sound live pool propose source target :
  mayReturn (check_memory_param_version_unified_region live pool propose source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_param_version_unified_region; intro RUN.
  eapply compile_memory_param_version_groups_sound; [|exact RUN].
  intros package chosen CERT_ACCEPTED; cbn beta in CERT_ACCEPTED.
  destruct (propose (memory_param_version_unified_request package)) as [candidate|].
  - destruct candidate.
    + eapply check_memory_param_axis_pointer_mapped_package_components_sound; exact CERT_ACCEPTED.
    + eapply check_memory_param_axis_pointer_mapped_package_components_sound; exact CERT_ACCEPTED.
    + eapply check_memory_param_axis_pointer_tiled_package_components_sound; exact CERT_ACCEPTED.
    + eapply check_memory_param_axis_pointer_scheduled_package_components_sound; exact CERT_ACCEPTED.
  - apply mayReturn_pure in CERT_ACCEPTED; discriminate.
Qed.
Definition memory_param_prefilter_unified_request source (package : memory_param_pointer_region_package source) :=
  BuildGuardedMemoryRequest (memory_param_pointer_region_instructions package)
    (length (memory_nest_iterators (param_pointer_region_nest package)))
    (length (memory_param_pointer_region_context package)) (param_pointer_region_limits package)
    (param_pointer_region_parameter_limits package) true true true None None.
Definition check_memory_param_prefilter_unified_region live pool (propose : guarded_memory_proposer) source :=
  @compile_memory_param_prefilter_groups source
    (fun package => match propose (memory_param_prefilter_unified_request package) with
      | Some (GuardedAffineCandidate candidate swaps) =>
          check_memory_param_axis_pointer_mapped_package live pool package candidate (map MemoryReindexSwap swaps)
      | Some (GuardedMappedCandidate candidate steps) =>
          check_memory_param_axis_pointer_mapped_package live pool package candidate steps
      | Some (GuardedTilingCandidate rows columns) =>
          check_memory_param_axis_pointer_tiled_package live pool package rows columns
      | Some (GuardedScheduleCandidate schedules steps) =>
          check_memory_param_axis_pointer_scheduled_package live pool package schedules steps
      | None => CoreAlarmed.Base.pure None end) (propose_memory_param_version_groups source).
Theorem check_memory_param_prefilter_unified_region_sound live pool propose source target :
  mayReturn (check_memory_param_prefilter_unified_region live pool propose source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_param_prefilter_unified_region; intro RUN.
  eapply compile_memory_param_prefilter_groups_sound; [|exact RUN].
  intros package chosen CERT_ACCEPTED; cbn beta in CERT_ACCEPTED.
  destruct (propose (memory_param_prefilter_unified_request package)) as [candidate|].
  - destruct candidate.
    + eapply check_memory_param_axis_pointer_mapped_package_components_sound; exact CERT_ACCEPTED.
    + eapply check_memory_param_axis_pointer_mapped_package_components_sound; exact CERT_ACCEPTED.
    + eapply check_memory_param_axis_pointer_tiled_package_components_sound; exact CERT_ACCEPTED.
    + eapply check_memory_param_axis_pointer_scheduled_package_components_sound; exact CERT_ACCEPTED.
  - apply mayReturn_pure in CERT_ACCEPTED; discriminate.
Qed.
Definition memory_started_axis_unified_request source (package : memory_started_pointer_package source) :=
  BuildGuardedMemoryRequest (memory_param_pointer_region_instructions (started_pointer_package package))
    (length (memory_nest_iterators (param_pointer_region_nest (started_pointer_package package))))
    (length (memory_started_pointer_region_context package)) (param_pointer_region_limits (started_pointer_package package))
    (param_pointer_region_parameter_limits (started_pointer_package package)) true false false (Some (memory_started_pointer_loop package)) None.
Definition check_memory_started_axis_unified_region live pool propose source :=
  @check_memory_param_axis_profiles source
    (fun original => match make_memory_started_pointer_package original with
      | Some package => match propose (memory_started_axis_unified_request package) with
        | Some (GuardedAffineCandidate candidate swaps) =>
            check_memory_started_axis_pointer_mapped_package live pool package candidate (map MemoryReindexSwap swaps)
        | Some (GuardedMappedCandidate candidate steps) =>
            check_memory_started_axis_pointer_mapped_package live pool package candidate steps
        | Some (GuardedTilingCandidate rows columns) =>
            check_memory_started_axis_pointer_tiled_package live pool package rows columns
        | Some (GuardedScheduleCandidate schedules steps) =>
            check_memory_started_axis_pointer_scheduled_package live pool package schedules steps
        | None => CoreAlarmed.Base.pure None end
      | None => CoreAlarmed.Base.pure None end) (propose_memory_param_axis_profiles source).
Theorem check_memory_started_axis_unified_region_sound live pool propose source target :
  mayReturn (check_memory_started_axis_unified_region live pool propose source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_started_axis_unified_region; intro RUN.
  eapply check_memory_param_axis_profiles_sound; [|exact RUN].
  intros original chosen ACCEPT; cbn beta in ACCEPT.
  destruct (make_memory_started_pointer_package original) as [package|];
    [|apply mayReturn_pure in ACCEPT; discriminate].
  destruct (propose (memory_started_axis_unified_request package)) as [candidate|].
  - destruct candidate.
    + eapply check_memory_started_axis_pointer_mapped_package_sound; exact ACCEPT.
    + eapply check_memory_started_axis_pointer_mapped_package_sound; exact ACCEPT.
    + eapply check_memory_started_axis_pointer_tiled_package_sound; exact ACCEPT.
    + eapply check_memory_started_axis_pointer_scheduled_package_sound; exact ACCEPT.
  - apply mayReturn_pure in ACCEPT; discriminate.
Qed.
Definition memory_window_unified_request source (package : window_started_package source) :=
  let base := window_started_base package in
  BuildGuardedMemoryRequest (window_region_instructions base)
    (length (memory_nest_iterators (window_region_nest base))) (length (window_package_context package))
    (window_region_caps base) (map snd (window_region_parameter_bounds base)) true false false
    (Some (window_package_loop package))
    (Some (window_region_root_lower base,window_region_parameter_bounds base,window_region_lower base,window_region_upper base)).
Definition check_memory_window_unified_region live pool propose source :=
  @check_window_profiles source (fun package => match propose (memory_window_unified_request package) with
    | Some (GuardedAffineCandidate candidate swaps) => check_window_mapped_package live pool package candidate (map MemoryReindexSwap swaps)
    | Some (GuardedMappedCandidate candidate steps) => check_window_mapped_package live pool package candidate steps
    | Some (GuardedScheduleCandidate schedules steps) => check_window_scheduled_package live pool package schedules steps
    | _ => CoreAlarmed.Base.pure None end) (propose_window_profiles source).
Theorem check_memory_window_unified_region_sound live pool propose source target :
  mayReturn (check_memory_window_unified_region live pool propose source) (Some target) -> projected_region_contract live source target.
Proof.
  unfold check_memory_window_unified_region; intro RUN; eapply check_window_profiles_sound; [|exact RUN].
  intros package chosen ACCEPT; cbn beta in ACCEPT; destruct (propose (memory_window_unified_request package)) as [candidate|].
  - destruct candidate.
    + eapply check_window_mapped_package_sound; exact ACCEPT.
    + eapply check_window_mapped_package_sound; exact ACCEPT.
    + apply mayReturn_pure in ACCEPT; discriminate.
    + eapply check_window_scheduled_package_sound; exact ACCEPT.
  - apply mayReturn_pure in ACCEPT; discriminate.
Qed.
Definition check_memory_multi_pointer_unified_region live pool propose source :=
  BIND target <- check_memory_affine_pointer_unified_region live pool propose source -;
  match target with
  | Some target => CoreAlarmed.Base.pure (Some target)
  | None => BIND target <- check_memory_linear_pointer_unified_region live pool propose source -;
      match target with
      | Some target => CoreAlarmed.Base.pure (Some target)
      | None => BIND target <- @check_memory_axis_pointer_caps source
          (fun package => match propose (memory_multi_pointer_unified_request package) with
            | Some (GuardedAffineCandidate candidate swaps) =>
                check_memory_axis_pointer_mapped_package live pool package candidate (map MemoryReindexSwap swaps)
            | Some (GuardedMappedCandidate candidate steps) =>
                check_memory_axis_pointer_mapped_package live pool package candidate steps
            | Some (GuardedTilingCandidate rows columns) =>
                check_memory_axis_pointer_tiled_package live pool package rows columns
            | Some (GuardedScheduleCandidate schedules steps) =>
                check_memory_axis_pointer_scheduled_package live pool package schedules steps
            | None => CoreAlarmed.Base.pure None end) memory_axis_pointer_search_caps -;
          match target with Some target => CoreAlarmed.Base.pure (Some target)
            | None => BIND target <- check_memory_vector_axis_unified_region live pool propose source -;
                match target with Some target => CoreAlarmed.Base.pure (Some target)
                  | None => BIND target <- check_memory_param_axis_unified_region live pool propose source -;
                    match target with Some target => CoreAlarmed.Base.pure (Some target)
                      | None => BIND target <- check_memory_param_version_unified_region live pool propose source -;
                        match target with Some target => CoreAlarmed.Base.pure (Some target)
                          | None => BIND target <- check_memory_param_prefilter_unified_region live pool propose source -;
                            match target with Some target => CoreAlarmed.Base.pure (Some target)
                              | None => BIND target <- check_memory_started_axis_unified_region live pool propose source -;
                                match target with Some target => CoreAlarmed.Base.pure (Some target)
                                  | None => BIND target <- check_memory_window_unified_region live pool propose source -;
                                    match target with Some target => CoreAlarmed.Base.pure (Some target)
                                      | None => check_memory_finite_multi_pointer_unified_region live pool propose source end end end end end end end end end.
Theorem check_memory_multi_pointer_unified_region_sound live pool propose source target :
  mayReturn (check_memory_multi_pointer_unified_region live pool propose source) (Some target) -> projected_region_contract live source target.
Proof.
  unfold check_memory_multi_pointer_unified_region; intro RUN;
    bind_imp_destruct RUN candidate CHECK; destruct candidate as [candidate|].
  - apply mayReturn_pure in RUN; inversion RUN; subst;
      eapply check_memory_affine_pointer_unified_region_sound; exact CHECK.
  - bind_imp_destruct RUN affine AFFINE; destruct affine as [affine|].
    + apply mayReturn_pure in RUN; inversion RUN; subst;
        eapply check_memory_linear_pointer_unified_region_sound; exact AFFINE.
    + bind_imp_destruct RUN axis AXIS; destruct axis as [axis|].
      * apply mayReturn_pure in RUN; inversion RUN; subst.
        eapply check_memory_axis_pointer_caps_sound; [|exact AXIS].
        intros package chosen CERT_ACCEPTED; cbn beta in CERT_ACCEPTED.
        destruct (propose (memory_multi_pointer_unified_request package)) as [candidate|].
        -- destruct candidate.
           ++ eapply check_memory_axis_pointer_mapped_package_sound; exact CERT_ACCEPTED.
           ++ eapply check_memory_axis_pointer_mapped_package_sound; exact CERT_ACCEPTED.
           ++ eapply check_memory_axis_pointer_tiled_package_sound; exact CERT_ACCEPTED.
           ++ eapply check_memory_axis_pointer_scheduled_package_sound; exact CERT_ACCEPTED.
        -- apply mayReturn_pure in CERT_ACCEPTED; discriminate.
      * bind_imp_destruct RUN vector VECTOR; destruct vector as [vector|].
        -- apply mayReturn_pure in RUN; inversion RUN; subst;
             eapply check_memory_vector_axis_unified_region_sound; exact VECTOR.
        -- bind_imp_destruct RUN parameters PARAMETERS; destruct parameters as [parameters|].
           ++ apply mayReturn_pure in RUN; inversion RUN; subst;
                eapply check_memory_param_axis_unified_region_sound; exact PARAMETERS.
           ++ bind_imp_destruct RUN versions VERSIONS; destruct versions as [versions|].
              ** apply mayReturn_pure in RUN; inversion RUN; subst;
                   eapply check_memory_param_version_unified_region_sound; exact VERSIONS.
              ** bind_imp_destruct RUN pref PREF; destruct pref as [pref|].
                 --- apply mayReturn_pure in RUN; inversion RUN; subst;
                       eapply check_memory_param_prefilter_unified_region_sound; exact PREF.
                 --- bind_imp_destruct RUN started STARTED; destruct started as [started|].
                     +++ apply mayReturn_pure in RUN; inversion RUN; subst;
                           eapply check_memory_started_axis_unified_region_sound; exact STARTED.
                     +++ bind_imp_destruct RUN window WINDOW; destruct window as [window|].
                         *** apply mayReturn_pure in RUN; inversion RUN; subst;
                               eapply check_memory_window_unified_region_sound; exact WINDOW.
                         *** eapply check_memory_finite_multi_pointer_unified_region_sound; exact RUN.
Qed.
Definition memory_scalar_pointer_unified_request source (package : memory_scalar_pointer_region_package source) :=
  GuardedMemoryRequest (memory_scalar_pointer_region_instructions package)
    (length (memory_nest_iterators (scalar_pointer_region_nest package))) (length (memory_scalar_pointer_region_context package)).
Definition check_memory_scalar_pointer_unified_region live pool (propose : guarded_memory_proposer) source :=
  match describe_memory_scalar_pointer_region source with
  | Some package => match propose (memory_scalar_pointer_unified_request package) with
      | Some (GuardedAffineCandidate candidate swaps) =>
          check_memory_scalar_pointer_mapped_region live pool (fun _ => Some (candidate,map MemoryReindexSwap swaps)) source
      | Some (GuardedMappedCandidate candidate steps) =>
          check_memory_scalar_pointer_mapped_region live pool (fun _ => Some (candidate,steps)) source
      | Some (GuardedTilingCandidate rows columns) => check_memory_scalar_pointer_tiled_region live pool rows columns source
      | Some (GuardedScheduleCandidate schedules steps) => check_memory_scalar_pointer_scheduled_region live pool schedules steps source
      | None => CoreAlarmed.Base.pure None end
  | None => check_memory_multi_pointer_unified_region live pool propose source end.
Theorem check_memory_scalar_pointer_unified_region_sound live pool propose source target :
  mayReturn (check_memory_scalar_pointer_unified_region live pool propose source) (Some target) -> projected_region_contract live source target.
Proof.
  unfold check_memory_scalar_pointer_unified_region; destruct (describe_memory_scalar_pointer_region source) as [package|];
    [|apply check_memory_multi_pointer_unified_region_sound].
  destruct (propose (memory_scalar_pointer_unified_request package)) as [candidate|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct candidate; intro RUN.
  - eapply check_memory_scalar_pointer_mapped_region_sound; exact RUN.
  - eapply check_memory_scalar_pointer_mapped_region_sound; exact RUN.
  - eapply check_memory_scalar_pointer_tiled_region_sound; exact RUN.
  - eapply check_memory_scalar_pointer_scheduled_region_sound; exact RUN.
Qed.
Definition memory_pointer_unified_request source (package : memory_pointer_region_package source) :=
  GuardedMemoryRequest (memory_pointer_region_instructions package)
    (length (memory_nest_iterators (pointer_region_nest package))) (length (memory_nest_bounds (pointer_region_nest package))).
Definition check_memory_pointer_unified_region live pool (propose : guarded_memory_proposer) source :=
  match describe_memory_pointer_region source with
  | Some package => match propose (memory_pointer_unified_request package) with
      | Some (GuardedAffineCandidate candidate swaps) =>
          check_memory_pointer_mapped_region live pool (fun _ => Some (candidate,map MemoryReindexSwap swaps)) source
      | Some (GuardedMappedCandidate candidate steps) =>
          check_memory_pointer_mapped_region live pool (fun _ => Some (candidate,steps)) source
      | Some (GuardedTilingCandidate rows columns) => check_memory_pointer_tiled_region live pool rows columns source
      | Some (GuardedScheduleCandidate schedules steps) => check_memory_pointer_scheduled_region live pool schedules steps source
      | None => CoreAlarmed.Base.pure None end
  | None => check_memory_scalar_pointer_unified_region live pool propose source end.
Theorem check_memory_pointer_unified_region_sound live pool propose source target :
  mayReturn (check_memory_pointer_unified_region live pool propose source) (Some target) -> projected_region_contract live source target.
Proof.
  unfold check_memory_pointer_unified_region; destruct (describe_memory_pointer_region source) as [package|];
    [|apply check_memory_scalar_pointer_unified_region_sound].
  destruct (propose (memory_pointer_unified_request package)) as [candidate|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct candidate; intro RUN.
  - eapply check_memory_pointer_mapped_region_sound; exact RUN.
  - eapply check_memory_pointer_mapped_region_sound; exact RUN.
  - eapply check_memory_pointer_tiled_region_sound; exact RUN.
  - eapply check_memory_pointer_scheduled_region_sound; exact RUN.
Qed.
Definition memory_scalar_array_unified_request source (package : memory_scalar_array_region_package source) :=
  GuardedMemoryRequest (memory_scalar_array_region_instructions package)
    (length (memory_nest_iterators (scalar_array_region_nest package))) (length (memory_scalar_array_region_context package)).
Definition check_memory_scalar_array_unified_region live pool (propose : guarded_memory_proposer) source :=
  match describe_memory_scalar_array_region source with
  | Some package => match propose (memory_scalar_array_unified_request package) with
      | Some (GuardedAffineCandidate candidate swaps) =>
          check_memory_scalar_array_mapped_region live pool (fun _ => Some (candidate,map MemoryReindexSwap swaps)) source
      | Some (GuardedMappedCandidate candidate steps) =>
          check_memory_scalar_array_mapped_region live pool (fun _ => Some (candidate,steps)) source
      | Some (GuardedTilingCandidate rows columns) => check_memory_scalar_array_tiled_region live pool rows columns source
      | Some (GuardedScheduleCandidate schedules steps) => check_memory_scalar_array_scheduled_region live pool schedules steps source
      | None => CoreAlarmed.Base.pure None end
  | None => check_memory_pointer_unified_region live pool propose source end.
Theorem check_memory_scalar_array_unified_region_sound live pool propose source target :
  mayReturn (check_memory_scalar_array_unified_region live pool propose source) (Some target) -> projected_region_contract live source target.
Proof.
  unfold check_memory_scalar_array_unified_region; destruct (describe_memory_scalar_array_region source) as [package|];
    [|apply check_memory_pointer_unified_region_sound].
  destruct (propose (memory_scalar_array_unified_request package)) as [candidate|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct candidate; intro RUN.
  - eapply check_memory_scalar_array_mapped_region_sound; exact RUN.
  - eapply check_memory_scalar_array_mapped_region_sound; exact RUN.
  - eapply check_memory_scalar_array_tiled_region_sound; exact RUN.
  - eapply check_memory_scalar_array_scheduled_region_sound; exact RUN.
Qed.
Definition memory_recursive_unified_request source (package : memory_recursive_region_package source) :=
  GuardedMemoryRequest (memory_recursive_region_instructions package)
    (length (memory_nest_iterators (recursive_region_nest package))) (length (memory_nest_bounds (recursive_region_nest package))).
Definition check_memory_recursive_unified_region live pool (propose : guarded_memory_proposer) source :=
  match describe_memory_recursive_region source with
  | Some package => match propose (memory_recursive_unified_request package) with
      | Some (GuardedAffineCandidate candidate swaps) =>
          check_memory_recursive_mapped_region live pool (fun _ => Some (candidate,map MemoryReindexSwap swaps)) source
      | Some (GuardedMappedCandidate candidate steps) =>
          check_memory_recursive_mapped_region live pool (fun _ => Some (candidate,steps)) source
      | Some (GuardedTilingCandidate rows columns) => check_memory_recursive_tiled_region live pool rows columns source
      | Some (GuardedScheduleCandidate schedules steps) => check_memory_recursive_scheduled_region live pool schedules steps source
      | None => CoreAlarmed.Base.pure None end
  | None => check_memory_scalar_array_unified_region live pool propose source end.
Theorem check_memory_recursive_unified_region_sound live pool propose source target :
  mayReturn (check_memory_recursive_unified_region live pool propose source) (Some target) -> projected_region_contract live source target.
Proof.
  unfold check_memory_recursive_unified_region; destruct (describe_memory_recursive_region source) as [package|];
    [|apply check_memory_scalar_array_unified_region_sound].
  destruct (propose (memory_recursive_unified_request package)) as [candidate|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct candidate; intro RUN.
  - eapply check_memory_recursive_mapped_region_sound; exact RUN.
  - eapply check_memory_recursive_mapped_region_sound; exact RUN.
  - eapply check_memory_recursive_tiled_region_sound; exact RUN.
  - eapply check_memory_recursive_scheduled_region_sound; exact RUN.
Qed.
Definition memory_triple_unified_request source (package : memory_triple_region_package source) :=
  GuardedMemoryRequest (memory_triple_region_instructions package)
    3%nat 3%nat.
Definition check_memory_triple_unified_region live pool (propose : guarded_memory_proposer) source :=
  match describe_memory_triple_region source with
  | Some package => match propose (memory_triple_unified_request package) with
      | Some (GuardedAffineCandidate candidate swaps) =>
          check_memory_triple_mapped_region live pool (fun _ => Some (candidate,map MemoryReindexSwap swaps)) source
      | Some (GuardedMappedCandidate candidate steps) =>
          check_memory_triple_mapped_region live pool (fun _ => Some (candidate,steps)) source
      | Some (GuardedTilingCandidate rows columns) => check_memory_triple_tiled_region live pool rows columns source
      | Some (GuardedScheduleCandidate schedules steps) => check_memory_triple_scheduled_region live pool schedules steps source
      | None => CoreAlarmed.Base.pure None end
  | None => check_memory_recursive_unified_region live pool propose source end.
Theorem check_memory_triple_unified_region_sound live pool propose source target :
  mayReturn (check_memory_triple_unified_region live pool propose source) (Some target) -> projected_region_contract live source target.
Proof.
  unfold check_memory_triple_unified_region; destruct (describe_memory_triple_region source) as [package|];
    [|apply check_memory_recursive_unified_region_sound].
  destruct (propose (memory_triple_unified_request package)) as [candidate|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct candidate; intro RUN.
  - eapply check_memory_triple_mapped_region_sound; exact RUN.
  - eapply check_memory_triple_mapped_region_sound; exact RUN.
  - eapply check_memory_triple_tiled_region_sound; exact RUN.
  - eapply check_memory_triple_scheduled_region_sound; exact RUN.
Qed.
Definition memory_layout_copy_unified_request source (package : memory_layout_copy_package source) :=
  GuardedMemoryRequest (memory_layout_copy_package_instructions package)
    2%nat (length (memory_source_context (rectangle_row (layout_copy_description package)) (rectangle_bound (layout_copy_description package)) (layout_copy_expression package))).
Definition check_memory_layout_copy_unified_region live pool (propose : guarded_memory_proposer) source :=
  match describe_memory_layout_copy source with
  | Some package =>
    match propose (memory_layout_copy_unified_request package) with
    | Some (GuardedAffineCandidate candidate swaps) =>
      check_memory_layout_copy_mapped_region live pool (fun _ => Some (candidate,map MemoryReindexSwap swaps)) source
    | Some (GuardedMappedCandidate candidate steps) =>
      check_memory_layout_copy_mapped_region live pool (fun _ => Some (candidate,steps)) source
    | Some (GuardedTilingCandidate rows columns) => check_memory_layout_copy_tiled_region live pool rows columns source
    | Some (GuardedScheduleCandidate schedules steps) => check_memory_layout_copy_scheduled_region live pool schedules steps source
    | None => CoreAlarmed.Base.pure None end
  | None => CoreAlarmed.Base.pure None end.
Theorem check_memory_layout_copy_unified_region_sound live pool propose source target :
  mayReturn (check_memory_layout_copy_unified_region live pool propose source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_layout_copy_unified_region.
  destruct (describe_memory_layout_copy source) as [package|];
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (propose (memory_layout_copy_unified_request package)) as [candidate|];
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct candidate; intro CHECK.
  - eapply check_memory_layout_copy_mapped_region_sound; exact CHECK.
  - eapply check_memory_layout_copy_mapped_region_sound; exact CHECK.
  - eapply check_memory_layout_copy_tiled_region_sound; exact CHECK.
  - eapply check_memory_layout_copy_scheduled_region_sound; exact CHECK.
Qed.
Definition memory_parametric_unified_request source (package : memory_parametric_region_package source) :=
  GuardedMemoryRequest (memory_parametric_region_instructions package)
    2%nat (length (memory_source_context (rectangle_row (parametric_region_description package)) (rectangle_bound (parametric_region_description package)) (parametric_region_expression package))).
Definition check_memory_parametric_unified_region live pool (propose : guarded_memory_proposer) source :=
  match describe_memory_parametric_region source with
  | Some package =>
    match propose (memory_parametric_unified_request package) with
    | Some (GuardedAffineCandidate candidate swaps) =>
      check_memory_parametric_with_widths
        (fun describe source => check_memory_parametric_region_conditioned live pool describe
          (fun _ => Some (candidate,map MemoryReindexSwap swaps)) source)
        describe_memory_parametric_region [1] source
    | Some (GuardedMappedCandidate candidate steps) =>
      check_memory_parametric_with_widths
        (fun describe source => check_memory_parametric_region_conditioned live pool describe
          (fun _ => Some (candidate,steps)) source)
        describe_memory_parametric_region [1] source
    | Some (GuardedTilingCandidate rows columns) =>
      check_memory_parametric_with_widths
        (fun describe source => check_memory_parametric_region_conditioned_tiling live pool describe rows columns source)
        describe_memory_parametric_region [1] source
    | Some (GuardedScheduleCandidate schedules steps) =>
      check_memory_parametric_with_widths
        (fun describe source => check_memory_parametric_region_scheduled live pool describe schedules steps source)
        describe_memory_parametric_region [1] source
    | None => CoreAlarmed.Base.pure None end
  | None => check_memory_triple_unified_region live pool propose source end.
Theorem check_memory_parametric_unified_region_sound live pool propose source target :
  mayReturn (check_memory_parametric_unified_region live pool propose source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_parametric_unified_region.
  destruct (describe_memory_parametric_region source) as [package|];
    [|apply check_memory_triple_unified_region_sound].
  destruct (propose (memory_parametric_unified_request package)) as [candidate|];
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct candidate; intro CHECK.
  - eapply check_memory_parametric_with_widths_sound; [|exact CHECK].
    intros describe original chosen ACCEPT; eapply check_memory_parametric_region_conditioned_sound; exact ACCEPT.
  - eapply check_memory_parametric_with_widths_sound; [|exact CHECK].
    intros describe original chosen ACCEPT; eapply check_memory_parametric_region_conditioned_sound; exact ACCEPT.
  - eapply check_memory_parametric_with_widths_sound; [|exact CHECK].
    intros describe original chosen ACCEPT; eapply check_memory_parametric_region_conditioned_tiling_sound; exact ACCEPT.
  - eapply check_memory_parametric_with_widths_sound; [|exact CHECK].
    intros describe original chosen ACCEPT; eapply check_memory_parametric_region_scheduled_sound; exact ACCEPT.
Qed.
Definition memory_ragged_unified_request source (package : memory_ragged_package source) :=
  GuardedMemoryRequest (map named_operation_instruction (ragged_operations package))
    2%nat 2%nat.
Definition check_memory_ragged_unified_region live pool (propose : guarded_memory_proposer) source :=
  match describe_memory_ragged source with
  | Some package =>
    match propose (memory_ragged_unified_request package) with
    | Some (GuardedAffineCandidate candidate swaps) =>
      check_memory_ragged_mapped_region live pool
        (fun _ => Some (candidate,map MemoryReindexSwap swaps)) source
    | Some (GuardedMappedCandidate candidate steps) =>
      check_memory_ragged_mapped_region live pool (fun _ => Some (candidate,steps)) source
    | Some (GuardedTilingCandidate rows columns) => check_memory_ragged_tiled_region live pool rows columns source
    | Some (GuardedScheduleCandidate schedules steps) => check_memory_ragged_scheduled_region live pool schedules steps source
    | None => CoreAlarmed.Base.pure None end
  | None => check_memory_parametric_unified_region live pool propose source end.
Theorem check_memory_ragged_unified_region_sound live pool propose source target :
  mayReturn (check_memory_ragged_unified_region live pool propose source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_ragged_unified_region.
  destruct (describe_memory_ragged source) as [package|];
    [|apply check_memory_parametric_unified_region_sound].
  destruct (propose (memory_ragged_unified_request package)) as [candidate|];
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct candidate; intro CHECK.
  - eapply check_memory_ragged_mapped_region_sound; exact CHECK.
  - eapply check_memory_ragged_mapped_region_sound; exact CHECK.
  - eapply check_memory_ragged_tiled_region_sound; exact CHECK.
  - eapply check_memory_ragged_scheduled_region_sound; exact CHECK.
Qed.
Definition memory_named_unified_request source (package : memory_named_package source) :=
  GuardedMemoryRequest (map named_operation_instruction (named_operations package))
    2%nat 2%nat.
Definition check_memory_named_unified_region live pool (propose : guarded_memory_proposer) source :=
  match describe_memory_named source with
  | Some package =>
    match propose (memory_named_unified_request package) with
    | Some (GuardedAffineCandidate candidate swaps) =>
      check_memory_named_affine_region live pool (fun _ => Some (candidate,swaps)) source
    | Some (GuardedMappedCandidate candidate steps) =>
      check_memory_named_mapped_region live pool (fun _ => Some (candidate,steps)) source
    | Some (GuardedTilingCandidate rows columns) => check_memory_named_tiled_region live pool rows columns source
    | Some (GuardedScheduleCandidate schedules steps) => check_memory_named_scheduled_region live pool schedules steps source
    | None => CoreAlarmed.Base.pure None end
  | None => check_memory_ragged_unified_region live pool propose source end.
Theorem check_memory_named_unified_region_sound live pool propose source target :
  mayReturn (check_memory_named_unified_region live pool propose source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_named_unified_region.
  destruct (describe_memory_named source) as [package|];
    [|apply check_memory_ragged_unified_region_sound].
  destruct (propose (memory_named_unified_request package)) as [candidate|];
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct candidate; intro CHECK.
  - eapply check_memory_named_affine_region_sound; exact CHECK.
  - eapply check_memory_named_mapped_region_sound; exact CHECK.
  - eapply check_memory_named_tiled_region_sound; exact CHECK.
  - eapply check_memory_named_scheduled_region_sound; exact CHECK.
Qed.
Definition memory_unified_request source (package : memory_operations_package source) :=
  GuardedMemoryRequest (map (operation_instruction 3%positive) (operations_list package))
    2%nat 2%nat.
Definition check_memory_unified_region live pool (propose : guarded_memory_proposer) source :=
  match describe_memory_operations source with
  | Some package =>
    match propose (memory_unified_request package) with
    | Some (GuardedAffineCandidate candidate swaps) =>
      check_memory_proposed_region live pool (fun _ => Some (candidate,swaps)) source
    | Some (GuardedMappedCandidate candidate steps) =>
      check_memory_named_unified_region live pool propose source
    | Some (GuardedTilingCandidate rows columns) =>
      check_memory_operations_region live pool rows columns source
    | Some (GuardedScheduleCandidate schedules steps) =>
      check_memory_named_scheduled_region live pool schedules steps source
    | None => CoreAlarmed.Base.pure None end
  | None => check_memory_named_unified_region live pool propose source end.
Theorem check_memory_unified_region_sound live pool propose source target :
  mayReturn (check_memory_unified_region live pool propose source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_unified_region.
  destruct (describe_memory_operations source) as [package|];
    [|apply check_memory_named_unified_region_sound].
  destruct (propose (memory_unified_request package)) as [candidate|];
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct candidate; intro CHECK.
  - eapply check_memory_proposed_region_sound; exact CHECK.
  - eapply check_memory_named_unified_region_sound; exact CHECK.
  - eapply check_memory_operations_region_sound; exact CHECK.
  - eapply check_memory_named_scheduled_region_sound; exact CHECK.
Qed.
Fixpoint checked_memory_unified_regions live pool propose sources : CoreAlarmed.Base.imp (list (statement * statement)) :=
  match sources with
  | [] => pure []
  | source::rest =>
    BIND candidate <- check_memory_unified_region live pool propose source -;
    BIND table <- checked_memory_unified_regions live pool propose rest -;
    pure (match candidate with Some target => (source,target)::table | None => table end)
  end.
Lemma checked_memory_unified_regions_sound live pool propose sources table :
  mayReturn (checked_memory_unified_regions live pool propose sources) table ->
  Forall (fun pair => projected_region_contract live (fst pair) (snd pair)) table.
Proof.
  revert table; induction sources; intros table CHECK; cbn in CHECK.
  - apply mayReturn_pure in CHECK; subst table; constructor.
  - bind_imp_destruct CHECK candidate CANDIDATE; bind_imp_destruct CHECK rest REST.
    apply mayReturn_pure in CHECK; destruct candidate as [target|]; subst table; [constructor|];
      eauto using check_memory_unified_region_sound.
Qed.
Definition compile_memory_unified_regions propose private_count (program : Csyntax.program) : CoreAlarmed.Base.imp (res Asm.program) :=
  match SimplExpr.transl_program program with
  | Error errors => pure (Error errors)
  | OK clight => match SimplLocals.transf_program clight with
    | Error errors => pure (Error errors)
    | OK normalized =>
      let live := program_temps normalized in
      let pool := propose_private_names live private_count in
      BIND table <- checked_memory_unified_regions live pool propose (memory_program_candidates normalized) -;
      pure (compile_clight_tail (Compiler.print Compiler.print_Clight
        (apply_memory_tiled_table pool table normalized)))
    end
  end.
Theorem memory_unified_cstrategy_forward propose private_count program target :
  mayReturn (compile_memory_unified_regions propose private_count program) (OK target) ->
  forward_simulation (Cstrategy.semantics program) (Asm.semantics target).
Proof.
  unfold compile_memory_unified_regions; destruct (SimplExpr.transl_program program) as [clight|errors] eqn:P1.
  2: intro COMPILED; apply mayReturn_pure in COMPILED; discriminate.
  destruct (SimplLocals.transf_program clight) as [normalized|errors] eqn:P2.
  2: intro COMPILED; apply mayReturn_pure in COMPILED; discriminate.
  intro COMPILED; bind_imp_destruct COMPILED table TABLE.
  apply mayReturn_pure in COMPILED; rewrite Compiler.print_identity in COMPILED.
  eapply compose_forward_simulations.
  { eapply SimplExprproof.transl_program_correct; eauto using SimplExprproof.transf_program_match. }
  eapply compose_forward_simulations.
  { eapply SimplLocalsproof.transf_program_correct; eauto using SimplLocalsproof.match_transf_program. }
  eapply compose_forward_simulations.
  { apply apply_memory_tiled_table_correct; eapply checked_memory_unified_regions_sound; exact TABLE. }
  eapply clight_tail_correct; exact COMPILED.
Qed.
Theorem compile_memory_unified_regions_correct propose private_count program target :
  mayReturn (compile_memory_unified_regions propose private_count program) (OK target) ->
  backward_simulation (Csem.semantics program) (Asm.semantics target).
Proof.
  intro COMPILED.
  apply compose_backward_simulation with (atomic (Cstrategy.semantics program)).
  - eapply sd_traces; eapply Asm.semantics_determinate.
  - apply factor_backward_simulation.
    + apply Cstrategy.strategy_simulation.
    + apply Csem.semantics_single_events.
    + eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.
  - apply forward_to_backward_simulation.
    + apply factor_forward_simulation.
      * apply memory_unified_cstrategy_forward with (propose := propose) (private_count := private_count); exact COMPILED.
      * eapply sd_traces; eapply Asm.semantics_determinate.
    + apply atomic_receptive; apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
Qed.
Print Assumptions compile_memory_unified_regions_correct.

Print Assumptions check_memory_multi_pointer_unified_region_sound.

Print Assumptions check_memory_vector_axis_unified_region_sound.

Print Assumptions check_memory_started_axis_unified_region_sound.

Print Assumptions check_memory_window_unified_region_sound.
