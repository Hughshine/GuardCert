From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight Ctypes.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightCondition ClightPrivateRegion ClightPrivatePool ClightStraightLine.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineInnerPointerSourceDomain GuardMemoryAffineInnerPointerRegionSource
  GuardMemoryParametricWidth GuardMemoryParametricRestore GuardMemoryParametricGuard GuardMemoryParametricChecker GuardMemoryPointerBackend
  GuardMemoryMultiPointerBackend GuardMemoryMultiPointerCompiler GuardMemoryTiledCompiler GuardMemoryScheduleProducer.
From GuardInterface Require Import ClightAffineSnapshotSyntax ClightAffineSnapshotCandidateExecution
  ClightAffineSnapshotCaptureCandidate ClightAffineInnerPointerCandidates ClightAffineInnerPointerCandidate ClightAffineInnerPointerCandidateGuard
  ClightAffineInnerPointerSourceGuard ClightAffinePointerGuard ClightSourceObservation
  ClightObservedPointerSyntax ClightSequenceContracts.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

(** An actual target AST, built before any proof record is assembled. Its
    fallback is the original repeated-load loop, with only private caches
    added to the entry. The independent checker licenses the same candidate
    that the existing CompCert-backed lowering compiles. *)
Definition checked_affine_snapshot_target original(site:affine_snapshot_source_package original)
    loads validator encoder width alias code :=
  let package:=snapshot_cached_package site in
  Ssequence(source_load_prefix loads)
    (Ssequence(affine_snapshot_capture_statement site)
      (tree_statement(affine_snapshot_installed_tree site width alias validator encoder)
        (Ssequence code(memory_parametric_restore
          (affine_inner_pointer_row(affine_inner_pointer_shape package))
          (affine_inner_pointer_bound(affine_inner_pointer_shape package))
          (affine_inner_pointer_column(affine_inner_pointer_shape package))
          (affine_inner_pointer_inner_bound(affine_inner_pointer_shape package))(affine_inner_pointer_expression package)))
        original)).

Definition check_affine_snapshot_certified_package live pool original(site:affine_snapshot_source_package original)
    loads validator encoder candidate(check:Base.imp bool) : Base.imp(option statement) :=
  let package:=snapshot_cached_package site in
  if source_observations_check(affine_inner_pointer_pointers package)loads then
    match compile_memory_source_width(affine_inner_pointer_column_limit package)
      (affine_inner_pointer_row(affine_inner_pointer_shape package))
      (memory_affine_inner_pointer_header(affine_inner_pointer_shape package)(affine_inner_pointer_expression package))
      (affine_inner_pointer_header_bounds(affine_inner_pointer_row_limit package)(affine_inner_pointer_header_limits package))
      (affine_inner_pointer_expression package),compile_affine_inner_pointer_package_envelopes package,
      private_counter_pairs pool with
    | Some width,Some alias,Some pairs =>
      match compile_memory_multi_pointer_buffer_loop(affine_inner_pointer_pointers package)
        (memory_affine_inner_pointer_region_context package)encoder live pairs candidate with
      | Some code => BIND valid <- check -;
        pure(if valid then Some(checked_affine_snapshot_target site loads validator encoder width alias code)else None)
      | None=>pure None end
    | _,_,_=>pure None end
  else pure None.

Theorem check_affine_snapshot_certified_package_sound live pool original(site:affine_snapshot_source_package original)
    (capture:affine_snapshot_capture_package site live)loads validator encoder candidate check target :
  (mayReturn check true -> affine_inner_pointer_candidate_certificate(snapshot_cached_package site)validator candidate) ->
  mayReturn(check_affine_snapshot_certified_package live pool site loads validator encoder candidate check)(Some target) ->
  PrivateRegion.projected_region_contract live(Ssequence(source_load_prefix loads)original)target.
Proof.
  intro CERTIFICATE; unfold check_affine_snapshot_certified_package.
  destruct(source_observations_check _ _)eqn:OBSERVED; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(compile_memory_source_width _ _ _ _ _)as [width|]eqn:WIDTH;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(compile_affine_inner_pointer_package_envelopes _)as [alias|]eqn:ALIAS;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(private_counter_pairs pool)as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(compile_memory_multi_pointer_buffer_loop _ _ _ _ _ _)as [code|]eqn:COMPILE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN;
    destruct valid; [injection RUN as <-|discriminate].
  pose(certified:=@Build_affine_inner_pointer_candidate_package(snapshot_cached_source site)(snapshot_cached_package site)
    live validator encoder candidate pairs code COMPILE(CERTIFICATE VALID)).
  change(PrivateRegion.projected_region_contract live(Ssequence(source_load_prefix loads)original)
    (Ssequence(source_load_prefix loads)(affine_snapshot_captured_guarded_candidate site certified width alias))).
  exact(@affine_snapshot_observed_captured_candidate_contract original site live capture certified width alias WIDTH ALIAS
    loads OBSERVED).
Qed.

Definition check_affine_snapshot_mapped_package live pool original(site:affine_snapshot_source_package original)
    loads validator encoder candidate steps :=
  check_affine_snapshot_certified_package live pool site loads validator encoder candidate
    (check_affine_inner_pointer_model(snapshot_cached_package site)validator candidate steps).
Theorem check_affine_snapshot_mapped_package_sound live pool original(site:affine_snapshot_source_package original)
    (capture:affine_snapshot_capture_package site live)loads validator encoder candidate steps target :
  mayReturn(check_affine_snapshot_mapped_package live pool site loads validator encoder candidate steps)(Some target) ->
  PrivateRegion.projected_region_contract live(Ssequence(source_load_prefix loads)original)target.
Proof.
  eapply check_affine_snapshot_certified_package_sound; [exact capture|apply check_affine_inner_pointer_model_sound].
Qed.

Definition check_affine_snapshot_tiled_package live pool original(site:affine_snapshot_source_package original)
    loads validator encoder candidate witnesses :=
  check_affine_snapshot_certified_package live pool site loads validator encoder candidate
    (check_affine_inner_pointer_tiling_model(snapshot_cached_package site)validator candidate witnesses).
Theorem check_affine_snapshot_tiled_package_sound live pool original(site:affine_snapshot_source_package original)
    (capture:affine_snapshot_capture_package site live)loads validator encoder candidate witnesses target :
  mayReturn(check_affine_snapshot_tiled_package live pool site loads validator encoder candidate witnesses)(Some target) ->
  PrivateRegion.projected_region_contract live(Ssequence(source_load_prefix loads)original)target.
Proof.
  eapply check_affine_snapshot_certified_package_sound; [exact capture|apply check_affine_inner_pointer_tiling_model_sound].
Qed.

Definition check_affine_snapshot_scheduled_package live pool original(site:affine_snapshot_source_package original)
    loads validator encoder schedules steps :=
  let package:=snapshot_cached_package site in
  let context:=memory_affine_inner_pointer_region_context package in
  let arrays:=affine_inner_pointer_pointers package in
  BIND generated <- memory_generate_scheduled_loop
    (memory_parametric_assumed_loop(affine_inner_pointer_candidate_base package)
      (affine_inner_pointer_row(affine_inner_pointer_shape package))context validator
      (affine_inner_pointer_expression package)(memory_affine_inner_pointer_region_model package),context,
      map(fun identifier=>(identifier,tt))(context++arrays))schedules -;
  match generated with
  | Some candidate=>check_affine_snapshot_mapped_package live pool site loads validator encoder
      (propose_affine_inner_candidate_normalization encoder O candidate)steps
  | None=>pure None end.
Theorem check_affine_snapshot_scheduled_package_sound live pool original(site:affine_snapshot_source_package original)
    (capture:affine_snapshot_capture_package site live)loads validator encoder schedules steps target :
  mayReturn(check_affine_snapshot_scheduled_package live pool site loads validator encoder schedules steps)(Some target) ->
  PrivateRegion.projected_region_contract live(Ssequence(source_load_prefix loads)original)target.
Proof.
  unfold check_affine_snapshot_scheduled_package; intro RUN; bind_imp_destruct RUN generated GENERATED.
  destruct generated as [candidate|];
    [eapply check_affine_snapshot_mapped_package_sound; [exact capture|exact RUN]|apply mayReturn_pure in RUN; discriminate].
Qed.

Definition check_affine_snapshot_package live pool(propose:affine_inner_pointer_proposer)
    original(site:affine_snapshot_source_package original)loads :=
  match propose(affine_inner_pointer_request_of(snapshot_cached_package site))with
  | Some proposal =>
    let validator:=affine_proposal_validator_bounds proposal in
    let encoder:=affine_proposal_encoder_bounds proposal in
    match affine_proposal_candidate proposal with
    | AffineInnerMappedProposal candidate steps=>check_affine_snapshot_mapped_package live pool site loads validator encoder candidate steps
    | AffineInnerTilingProposal candidate witnesses=>check_affine_snapshot_tiled_package live pool site loads validator encoder candidate witnesses
    | AffineInnerScheduleProposal schedules steps=>check_affine_snapshot_scheduled_package live pool site loads validator encoder schedules steps
    end
  | None=>pure None end.
Theorem check_affine_snapshot_package_sound live pool propose original(site:affine_snapshot_source_package original)
    (capture:affine_snapshot_capture_package site live)loads target :
  mayReturn(check_affine_snapshot_package live pool propose site loads)(Some target) ->
  PrivateRegion.projected_region_contract live(Ssequence(source_load_prefix loads)original)target.
Proof.
  unfold check_affine_snapshot_package; destruct(propose _)as [proposal|];
    [destruct(affine_proposal_candidate proposal); intro RUN|
     intro RUN; apply mayReturn_pure in RUN; discriminate].
  - eapply check_affine_snapshot_mapped_package_sound; [exact capture|exact RUN].
  - eapply check_affine_snapshot_tiled_package_sound; [exact capture|exact RUN].
  - eapply check_affine_snapshot_scheduled_package_sound; [exact capture|exact RUN].
Qed.

(** Reserve two typed caches, independently describe the original loaded
    loop, check its transport resources, and bind the ordinary proposal to
    that checked source model. No semantic callback is a source-user input. *)
Definition check_affine_snapshot_source live pool profile propose source :=
  match pool with
  | (root_cache,root_type)::(child_cache,child_type)::candidate_pool =>
    if type_eq root_type type_int32s then if type_eq child_type type_int32s then
      match describe_observed_pointer_source source with
      | Some observed=>match describe_affine_snapshot_source profile root_cache child_cache(observed_source_loop observed)with
        | Some site=>match check_affine_snapshot_capture site live with
          | Some capture=>BIND target <- check_affine_snapshot_package live candidate_pool propose site(observed_source_loads observed) -;
            pure(option_map(fun code=>Ssequence code(observed_source_suffix observed))target)
          | None=>pure None end
        | None=>pure None end
      | None=>pure None end
    else pure None else pure None
  | _=>pure None end.
Theorem check_affine_snapshot_source_sound live pool profile propose source target :
  mayReturn(check_affine_snapshot_source live pool profile propose source)(Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  unfold check_affine_snapshot_source; destruct pool as [|[root_cache root_type][|[child_cache child_type]candidate_pool]];
    try solve[intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(type_eq root_type type_int32s); [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(type_eq child_type type_int32s); [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(describe_observed_pointer_source source)as [observed|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(describe_affine_snapshot_source _ _ _ _)as [site|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(check_affine_snapshot_capture site live)as [capture|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN selected ACCEPTED; apply mayReturn_pure in RUN;
    destruct selected as [code|]; [injection RUN as <-|discriminate].
  eapply flattened_projected_region_contract; [exact(observed_source_flat observed)|].
  apply projected_region_quiet_suffix; [exact(observed_source_suffix_quiet observed)|].
  eapply check_affine_snapshot_package_sound; [exact capture|exact ACCEPTED].
Qed.

Print Assumptions check_affine_snapshot_certified_package_sound.
Print Assumptions check_affine_snapshot_mapped_package_sound.
Print Assumptions check_affine_snapshot_tiled_package_sound.
Print Assumptions check_affine_snapshot_scheduled_package_sound.
Print Assumptions check_affine_snapshot_package_sound.
Print Assumptions check_affine_snapshot_source_sound.
