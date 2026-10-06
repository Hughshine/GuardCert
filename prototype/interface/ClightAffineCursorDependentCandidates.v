From Stdlib Require Import List Bool ZArith.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Ctypes.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightCondition ClightPureExpr ClightPrivateRegion ClightPrivatePool ClightStraightLine.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryParametricWidth
  GuardMemoryMultiPointerBackend GuardMemoryAffineInnerPointerRegionSource GuardMemoryParametricRestore
  GuardMemoryScheduleProducer GuardMemoryParametricGuard GuardMemoryParametricChecker GuardMemoryTiledCompiler
  GuardMemoryAffinePointerLoadedDomain.
From GuardInterface Require Import ClightAffineDynamicLoadedSyntax ClightAffinePlannedLoadedRewrite ClightAffineLoadedCheckPlan ClightCheckPlan ClightCheckPlanFrame
  ClightAffineInnerPointerCandidate ClightAffineInnerPointerCandidateGuard ClightAffineInnerPointerCandidates
  ClightAffineInnerPointerSourceGuard ClightAffinePointerSourcePreparation ClightAffineInnerPointerPreservation
  ClightAffinePointerGuard ClightSourceObservation ClightObservedPointerSyntax ClightSequenceContracts ClightAffineDependentSyntax ClightDependentLoadedSource
  ClightDependentCaptureDomain ClightDependentBoundSyntax ClightDependentHeaderObservations ClightDependentSnapshotInsertion
  ClightAffineDependentLoadedPrefix ClightAffineDependentCheckPlan ClightAffineDependentPlannedRewrite
  ClightAffineDependentCursorRewrite ClightAffineDependentCursorResources.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

Definition checked_affine_cursor_dependent_target live source pointer_cache cache
  (region : affine_dependent_region_package live source pointer_cache cache)
  validator_bounds encoder_bounds width alias code result outer inner :=
  let site := dependent_region_site region in
  let observed := dependent_site_observed site in
  let package := dependent_region_package region in
  let shape := affine_inner_pointer_shape package in
  Ssequence
    (Ssequence (dependent_guard_prefix (observed_source_loads observed) (dependent_site_root site) pointer_cache cache)
      (affine_dependent_cursor_guarded_statement package (dependent_site_root site) pointer_cache outer inner result
        width alias validator_bounds encoder_bounds
        (Ssequence code (memory_parametric_restore (affine_inner_pointer_row shape) (affine_inner_pointer_bound shape)
          (affine_inner_pointer_column shape) (affine_inner_pointer_inner_bound shape) (affine_inner_pointer_expression package)))
        (affine_dependent_loaded_source package (dependent_site_root site))))
    (observed_source_suffix observed).

Definition check_affine_cursor_dependent_certified live pool source pointer_cache cache
  (region : affine_dependent_region_package live source pointer_cache cache)
  validator_bounds encoder_bounds candidate (check : CoreAlarmed.Base.imp bool) : CoreAlarmed.Base.imp (option statement) :=
  let site := dependent_region_site region in
  let package := dependent_region_package region in
  let shape := affine_inner_pointer_shape package in
  let protected := [pointer_cache;cache]++live in
  match pool with
  | (outer,outer_type)::(inner,inner_type)::(result,result_type)::counter_pool =>
    if type_eq outer_type type_int32s then if type_eq inner_type type_int32s then if type_eq result_type type_int32s then
  match compile_memory_source_width (affine_inner_pointer_column_limit package)
    (affine_inner_pointer_row shape)
    (memory_affine_inner_pointer_header shape (affine_inner_pointer_expression package))
    (affine_inner_pointer_header_bounds (affine_inner_pointer_row_limit package) (affine_inner_pointer_header_limits package))
    (affine_inner_pointer_expression package),compile_affine_inner_pointer_package_envelopes package,private_counter_pairs counter_pool with
  | Some width,Some alias,Some pairs =>
    match compile_memory_multi_pointer_buffer_loop (affine_inner_pointer_pointers package)
      (memory_affine_inner_pointer_region_context package) encoder_bounds protected pairs candidate with
    | Some code =>
      let yes := Ssequence code (memory_parametric_restore (affine_inner_pointer_row shape) (affine_inner_pointer_bound shape)
        (affine_inner_pointer_column shape) (affine_inner_pointer_inner_bound shape) (affine_inner_pointer_expression package)) in
      let no := affine_dependent_loaded_source package (dependent_site_root site) in
      let scope := affine_dependent_cursor_guard_scope package width alias validator_bounds encoder_bounds yes no protected in
      if check_plan_frameable yes && check_plan_frameable no &&
        affine_dependent_cursor_resources_check package (dependent_site_root site) pointer_cache outer inner result scope then
        BIND valid <- check -;
        pure (if valid then Some (checked_affine_cursor_dependent_target region validator_bounds encoder_bounds width alias code result outer inner) else None)
      else pure None
    | None => pure None end
  | _,_,_ => pure None end
  else pure None else pure None else pure None
  | _ => pure None
  end.

Theorem check_affine_cursor_dependent_certified_sound live pool source pointer_cache cache
  (region : affine_dependent_region_package live source pointer_cache cache)
  validator_bounds encoder_bounds candidate check target :
  (mayReturn check true -> affine_inner_pointer_candidate_certificate
    (dependent_region_package region) validator_bounds candidate) ->
  mayReturn (check_affine_cursor_dependent_certified pool region validator_bounds encoder_bounds candidate check) (Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  intro CERTIFICATE; unfold check_affine_cursor_dependent_certified.
  destruct pool as [|[outer outer_type] [|[inner inner_type] [|[result result_type] counter_pool]]];
    try solve [intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (type_eq outer_type type_int32s), (type_eq inner_type type_int32s), (type_eq result_type type_int32s);
    try solve [intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_memory_source_width _ _ _ _ _) as [width|] eqn:WIDTH;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_affine_inner_pointer_package_envelopes _) as [alias|] eqn:ALIAS;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (private_counter_pairs counter_pool) as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_memory_multi_pointer_buffer_loop _ _ _ _ _ _) as [code|] eqn:COMPILE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (check_plan_frameable _) eqn:YES; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (check_plan_frameable (affine_dependent_loaded_source (dependent_region_package region)
    (dependent_site_root (dependent_region_site region)))) eqn:NO;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  cbn.
  destruct (affine_dependent_cursor_resources_check _ _ _ _ _ _ _) eqn:RESOURCES;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  pose proof (@affine_dependent_cursor_resources_sound _ _ _ _ _ _ _ _ RESOURCES) as PRIVATE.
  intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN;
    destruct valid; [injection RUN as <-|discriminate].
  pose (site := dependent_region_site region).
  pose (package := dependent_region_package region).
  pose (certified := @Build_affine_inner_pointer_candidate_package (dependent_region_cached_source region) package
    ([pointer_cache;cache]++live) validator_bounds encoder_bounds candidate pairs code COMPILE (CERTIFICATE VALID)).
  assert (LOOP : dependent_bound_loop (dependent_site_row site) (dependent_site_root site) (dependent_site_body site) =
    affine_dependent_loaded_source package (dependent_site_root site)).
  { rewrite <- (dependent_site_loop_exact site); exact (dependent_region_loop_exact region). }
  eapply (@dependent_site_prepared_contract live source site pointer_cache cache);
    [exact (dependent_region_pointer_private region)|exact (dependent_region_cache_private region)|].
  eapply flattened_projected_region_contract with
    (canonical:=Ssequence (Ssequence
      (dependent_guard_prefix (observed_source_loads (dependent_site_observed site)) (dependent_site_root site) pointer_cache cache)
      (affine_dependent_loaded_source package (dependent_site_root site))) (observed_source_suffix (dependent_site_observed site))).
  { unfold dependent_site_prepared,dependent_snapshot_prepared,dependent_guard_prefix,dependent_header_capture.
    rewrite LOOP.
    cbn [flatten_region]; repeat rewrite app_assoc; reflexivity. }
  apply projected_region_quiet_suffix; [exact (observed_source_suffix_quiet (dependent_site_observed site))|].
  change (PrivateRegion.projected_region_contract ([pointer_cache;cache]++live)
    (Ssequence (dependent_guard_prefix (observed_source_loads (dependent_site_observed site)) (dependent_site_root site) pointer_cache cache)
      (affine_dependent_loaded_source package (dependent_site_root site)))
    (Ssequence (dependent_guard_prefix (observed_source_loads (dependent_site_observed site)) (dependent_site_root site) pointer_cache cache)
      (affine_dependent_cursor_guarded_candidate (dependent_site_root site) pointer_cache certified width alias outer inner result))).
  assert (PREFIX : dependent_guard_prefix (observed_source_loads (dependent_site_observed site)) (dependent_site_root site) pointer_cache cache =
    dependent_guard_prefix (observed_source_loads (dependent_site_observed site)) (dependent_site_root site) pointer_cache
      (affine_inner_pointer_bound (affine_inner_pointer_shape package))) by
    (unfold package; rewrite (dependent_region_cache_exact region); reflexivity).
  rewrite PREFIX; apply affine_dependent_cursor_prefix_contract;
    [exact (dependent_region_root_fresh region)|exact (dependent_region_pointer_fresh region)|exact WIDTH|exact ALIAS|
     exact YES|exact NO|exact PRIVATE| | | |apply dependent_region_pointer_no_load| |exact (dependent_region_observations region)].
  - exact (proj1 (dependent_region_capture_distinct region)).
  - unfold package; rewrite (dependent_region_cache_exact region); exact (proj1 (proj2 (dependent_region_capture_distinct region))).
  - unfold package; rewrite (dependent_region_cache_exact region); exact (proj2 (proj2 (dependent_region_capture_distinct region))).
  - unfold package; rewrite (dependent_region_cache_exact region); apply dependent_region_cache_no_load.
Qed.

Definition check_affine_cursor_dependent_mapped live pool source pointer_cache cache (region : affine_dependent_region_package live source pointer_cache cache)
  validator_bounds encoder_bounds candidate steps :=
  check_affine_cursor_dependent_certified pool region validator_bounds encoder_bounds candidate
    (check_affine_inner_pointer_model (dependent_region_package region) validator_bounds candidate steps).
Theorem check_affine_cursor_dependent_mapped_sound live pool source pointer_cache cache (region : affine_dependent_region_package live source pointer_cache cache)
  validator_bounds encoder_bounds candidate steps target :
  mayReturn (check_affine_cursor_dependent_mapped pool region validator_bounds encoder_bounds candidate steps) (Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof. apply check_affine_cursor_dependent_certified_sound,check_affine_inner_pointer_model_sound. Qed.

Definition check_affine_cursor_dependent_tiled live pool source pointer_cache cache (region : affine_dependent_region_package live source pointer_cache cache)
  validator_bounds encoder_bounds candidate witnesses :=
  check_affine_cursor_dependent_certified pool region validator_bounds encoder_bounds candidate
    (check_affine_inner_pointer_tiling_model (dependent_region_package region) validator_bounds candidate witnesses).
Theorem check_affine_cursor_dependent_tiled_sound live pool source pointer_cache cache (region : affine_dependent_region_package live source pointer_cache cache)
  validator_bounds encoder_bounds candidate witnesses target :
  mayReturn (check_affine_cursor_dependent_tiled pool region validator_bounds encoder_bounds candidate witnesses) (Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof. apply check_affine_cursor_dependent_certified_sound,check_affine_inner_pointer_tiling_model_sound. Qed.

Definition check_affine_cursor_dependent_scheduled live pool source pointer_cache cache (region : affine_dependent_region_package live source pointer_cache cache)
  validator_bounds encoder_bounds schedules steps :=
  let package := dependent_region_package region in
  let context := memory_affine_inner_pointer_region_context package in
  let arrays := affine_inner_pointer_pointers package in
  BIND generated <- memory_generate_scheduled_loop
    (memory_parametric_assumed_loop (affine_inner_pointer_candidate_base package)
      (affine_inner_pointer_row (affine_inner_pointer_shape package)) context validator_bounds
      (affine_inner_pointer_expression package) (memory_affine_inner_pointer_region_model package),context,
      map (fun identifier => (identifier,tt)) (context++arrays)) schedules -;
  match generated with
  | Some candidate => check_affine_cursor_dependent_mapped pool region validator_bounds encoder_bounds
      (propose_affine_inner_candidate_normalization encoder_bounds O candidate) steps
  | None => pure None end.
Theorem check_affine_cursor_dependent_scheduled_sound live pool source pointer_cache cache (region : affine_dependent_region_package live source pointer_cache cache)
  validator_bounds encoder_bounds schedules steps target :
  mayReturn (check_affine_cursor_dependent_scheduled pool region validator_bounds encoder_bounds schedules steps) (Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  unfold check_affine_cursor_dependent_scheduled; intro RUN; bind_imp_destruct RUN generated GENERATED.
  destruct generated as [candidate|];
    [eapply check_affine_cursor_dependent_mapped_sound; exact RUN|apply mayReturn_pure in RUN; discriminate].
Qed.

Definition check_affine_cursor_dependent_package live pool (propose : affine_inner_pointer_proposer)
  source pointer_cache cache (region : affine_dependent_region_package live source pointer_cache cache) :=
  match propose (affine_inner_pointer_request_of (dependent_region_package region)) with
  | Some proposal =>
    let validator_bounds := affine_proposal_validator_bounds proposal in
    let encoder_bounds := affine_proposal_encoder_bounds proposal in
    match affine_proposal_candidate proposal with
    | AffineInnerMappedProposal candidate steps =>
      check_affine_cursor_dependent_mapped pool region validator_bounds encoder_bounds candidate steps
    | AffineInnerTilingProposal candidate witnesses =>
      check_affine_cursor_dependent_tiled pool region validator_bounds encoder_bounds candidate witnesses
    | AffineInnerScheduleProposal schedules steps =>
      check_affine_cursor_dependent_scheduled pool region validator_bounds encoder_bounds schedules steps
    end
  | None => pure None end.
Theorem check_affine_cursor_dependent_package_sound live pool propose source pointer_cache cache (region : affine_dependent_region_package live source pointer_cache cache) target :
  mayReturn (check_affine_cursor_dependent_package pool propose region) (Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  unfold check_affine_cursor_dependent_package; destruct (propose _) as [proposal|].
  - destruct (affine_proposal_candidate proposal); intro RUN;
      [eapply check_affine_cursor_dependent_mapped_sound|eapply check_affine_cursor_dependent_tiled_sound|
       eapply check_affine_cursor_dependent_scheduled_sound]; exact RUN.
  - intro RUN; apply mayReturn_pure in RUN; discriminate.
Qed.
Definition check_affine_cursor_dependent_source live pool profile propose source :=
  match pool with
  | (pointer_cache,pointer_type)::(cache,cache_type)::check_pool =>
    if type_eq pointer_type signed_pointer_type then if type_eq cache_type type_int32s then
      match describe_affine_dependent_source live pointer_cache cache profile source with
      | Some region => check_affine_cursor_dependent_package check_pool propose region
      | None => pure None end
    else pure None else pure None
  | _ => pure None end.
Theorem check_affine_cursor_dependent_source_sound live pool profile propose source target :
  mayReturn (check_affine_cursor_dependent_source live pool profile propose source) (Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  unfold check_affine_cursor_dependent_source; destruct pool as [|[pointer_cache pointer_type] [|[cache cache_type] check_pool]];
    try solve [intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (type_eq pointer_type signed_pointer_type), (type_eq cache_type type_int32s);
    try solve [intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (describe_affine_dependent_source live pointer_cache cache profile source) as [region|];
    [apply check_affine_cursor_dependent_package_sound|intro RUN; apply mayReturn_pure in RUN; discriminate].
Qed.

Print Assumptions check_affine_cursor_dependent_certified_sound.
Print Assumptions check_affine_cursor_dependent_mapped_sound.
Print Assumptions check_affine_cursor_dependent_tiled_sound.
Print Assumptions check_affine_cursor_dependent_scheduled_sound.
Print Assumptions check_affine_cursor_dependent_package_sound.
Print Assumptions check_affine_cursor_dependent_source_sound.
