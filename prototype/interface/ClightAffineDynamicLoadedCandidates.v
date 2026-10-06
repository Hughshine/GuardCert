From Stdlib Require Import List Bool ZArith.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightCondition ClightPureExpr ClightPrivateRegion ClightPrivatePool ClightStraightLine.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryParametricWidth
  GuardMemoryMultiPointerBackend GuardMemoryAffineInnerPointerRegionSource GuardMemoryParametricRestore
  GuardMemoryScheduleProducer GuardMemoryParametricGuard GuardMemoryParametricChecker GuardMemoryTiledCompiler
  GuardMemoryAffinePointerLoadedDomain.
From GuardInterface Require Import ClightAffineDynamicLoadedSyntax ClightAffineDynamicLoadedRewrite ClightAffineLoadedStability
  ClightAffineInnerPointerCandidate ClightAffineInnerPointerCandidateGuard ClightAffineInnerPointerCandidates
  ClightAffineInnerPointerSourceGuard ClightAffinePointerSourcePreparation ClightAffineInnerPointerPreservation
  ClightAffinePointerGuard ClightSourceObservation ClightObservedPointerSyntax ClightSequenceContracts.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

Definition checked_affine_dynamic_loaded_target source (region : affine_dynamic_loaded_region_package source)
  validator_bounds encoder_bounds width alias code :=
  let observed := dynamic_loaded_region_observed region in
  let body := dynamic_loaded_region_body region in
  let package := dynamic_loaded_body_cached_package body in
  let shape := affine_inner_pointer_shape package in
  Ssequence
    (Ssequence (source_load_prefix (observed_source_loads observed))
      (tree_statement (decision_bind (decision_bind (affine_inner_pointer_package_preparation_tree package width)
        (affine_loaded_stability_tree package (dynamic_loaded_body_pointer body)
          (Z.to_nat (affine_inner_pointer_row_limit package)) 0%Z) (Decision false))
        (affine_inner_pointer_candidate_guard_tree package width alias validator_bounds encoder_bounds) (Decision false))
        (Ssequence code (memory_parametric_restore (affine_inner_pointer_row shape) (affine_inner_pointer_bound shape)
          (affine_inner_pointer_column shape) (affine_inner_pointer_inner_bound shape) (affine_inner_pointer_expression package)))
        (memory_affine_pointer_loaded_source package (dynamic_loaded_body_pointer body))))
    (observed_source_suffix observed).

Definition check_affine_dynamic_loaded_certified live pool source (region : affine_dynamic_loaded_region_package source)
  validator_bounds encoder_bounds candidate (check : CoreAlarmed.Base.imp bool) : CoreAlarmed.Base.imp (option statement) :=
  let package := dynamic_loaded_body_cached_package (dynamic_loaded_region_body region) in
  match compile_memory_source_width (affine_inner_pointer_column_limit package)
    (affine_inner_pointer_row (affine_inner_pointer_shape package))
    (memory_affine_inner_pointer_header (affine_inner_pointer_shape package) (affine_inner_pointer_expression package))
    (affine_inner_pointer_header_bounds (affine_inner_pointer_row_limit package) (affine_inner_pointer_header_limits package))
    (affine_inner_pointer_expression package),compile_affine_inner_pointer_package_envelopes package,private_counter_pairs pool with
  | Some width,Some alias,Some pairs =>
    match compile_memory_multi_pointer_buffer_loop (affine_inner_pointer_pointers package)
      (memory_affine_inner_pointer_region_context package) encoder_bounds live pairs candidate with
    | Some code => BIND valid <- check -;
      pure (if valid then Some (checked_affine_dynamic_loaded_target region validator_bounds encoder_bounds width alias code) else None)
    | None => pure None end
  | _,_,_ => pure None end.

Theorem check_affine_dynamic_loaded_certified_sound live pool source (region : affine_dynamic_loaded_region_package source)
  validator_bounds encoder_bounds candidate check target :
  (mayReturn check true -> affine_inner_pointer_candidate_certificate
    (dynamic_loaded_body_cached_package (dynamic_loaded_region_body region)) validator_bounds candidate) ->
  mayReturn (check_affine_dynamic_loaded_certified live pool region validator_bounds encoder_bounds candidate check) (Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  intro CERTIFICATE; unfold check_affine_dynamic_loaded_certified.
  destruct (compile_memory_source_width _ _ _ _ _) as [width|] eqn:WIDTH;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_affine_inner_pointer_package_envelopes _) as [alias|] eqn:ALIAS;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (private_counter_pairs pool) as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_memory_multi_pointer_buffer_loop _ _ _ _ _ _) as [code|] eqn:COMPILE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN;
    destruct valid; [injection RUN as <-|discriminate].
  pose (body := dynamic_loaded_region_body region).
  pose (package := dynamic_loaded_body_cached_package body).
  pose (certified := @Build_affine_inner_pointer_candidate_package (dynamic_loaded_body_cached_source body) package live
    validator_bounds encoder_bounds candidate pairs code COMPILE (CERTIFICATE VALID)).
  eapply flattened_projected_region_contract; [exact (observed_source_flat (dynamic_loaded_region_observed region))|].
  apply projected_region_quiet_suffix; [exact (observed_source_suffix_quiet (dynamic_loaded_region_observed region))|].
  eapply flattened_projected_region_contract with
    (canonical:=Ssequence (source_load_prefix (observed_source_loads (dynamic_loaded_region_observed region)))
      (memory_affine_pointer_loaded_source package (dynamic_loaded_body_pointer body))).
  { exact (f_equal flatten_region (f_equal
      (fun code => Ssequence (source_load_prefix (observed_source_loads (dynamic_loaded_region_observed region))) code)
      (dynamic_loaded_body_exact body))). }
  change (PrivateRegion.projected_region_contract live
    (Ssequence (source_load_prefix (observed_source_loads (dynamic_loaded_region_observed region)))
      (memory_affine_pointer_loaded_source package (dynamic_loaded_body_pointer body)))
    (Ssequence (source_load_prefix (observed_source_loads (dynamic_loaded_region_observed region)))
      (affine_dynamic_loaded_guarded_candidate (dynamic_loaded_body_pointer body) certified width alias))).
  apply affine_dynamic_loaded_observed_candidate_contract;
    [exact (dynamic_loaded_body_pointer_fresh body)|exact WIDTH|exact ALIAS|
     exact (dynamic_loaded_region_outputs_unique region)|exact (dynamic_loaded_region_observations region)|
     exact (dynamic_loaded_region_snapshot_receipt region)].
Qed.

Definition check_affine_dynamic_loaded_mapped live pool source (region : affine_dynamic_loaded_region_package source)
  validator_bounds encoder_bounds candidate steps :=
  check_affine_dynamic_loaded_certified live pool region validator_bounds encoder_bounds candidate
    (check_affine_inner_pointer_model (dynamic_loaded_body_cached_package (dynamic_loaded_region_body region)) validator_bounds candidate steps).
Theorem check_affine_dynamic_loaded_mapped_sound live pool source (region : affine_dynamic_loaded_region_package source)
  validator_bounds encoder_bounds candidate steps target :
  mayReturn (check_affine_dynamic_loaded_mapped live pool region validator_bounds encoder_bounds candidate steps) (Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof. apply check_affine_dynamic_loaded_certified_sound,check_affine_inner_pointer_model_sound. Qed.

Definition check_affine_dynamic_loaded_tiled live pool source (region : affine_dynamic_loaded_region_package source)
  validator_bounds encoder_bounds candidate witnesses :=
  check_affine_dynamic_loaded_certified live pool region validator_bounds encoder_bounds candidate
    (check_affine_inner_pointer_tiling_model (dynamic_loaded_body_cached_package (dynamic_loaded_region_body region)) validator_bounds candidate witnesses).
Theorem check_affine_dynamic_loaded_tiled_sound live pool source (region : affine_dynamic_loaded_region_package source)
  validator_bounds encoder_bounds candidate witnesses target :
  mayReturn (check_affine_dynamic_loaded_tiled live pool region validator_bounds encoder_bounds candidate witnesses) (Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof. apply check_affine_dynamic_loaded_certified_sound,check_affine_inner_pointer_tiling_model_sound. Qed.

Definition check_affine_dynamic_loaded_scheduled live pool source (region : affine_dynamic_loaded_region_package source)
  validator_bounds encoder_bounds schedules steps :=
  let package := dynamic_loaded_body_cached_package (dynamic_loaded_region_body region) in
  let context := memory_affine_inner_pointer_region_context package in
  let arrays := affine_inner_pointer_pointers package in
  BIND generated <- memory_generate_scheduled_loop
    (memory_parametric_assumed_loop (affine_inner_pointer_candidate_base package)
      (affine_inner_pointer_row (affine_inner_pointer_shape package)) context validator_bounds
      (affine_inner_pointer_expression package) (memory_affine_inner_pointer_region_model package),context,
      map (fun identifier => (identifier,tt)) (context++arrays)) schedules -;
  match generated with
  | Some candidate => check_affine_dynamic_loaded_mapped live pool region validator_bounds encoder_bounds
      (propose_affine_inner_candidate_normalization encoder_bounds O candidate) steps
  | None => pure None end.
Theorem check_affine_dynamic_loaded_scheduled_sound live pool source (region : affine_dynamic_loaded_region_package source)
  validator_bounds encoder_bounds schedules steps target :
  mayReturn (check_affine_dynamic_loaded_scheduled live pool region validator_bounds encoder_bounds schedules steps) (Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  unfold check_affine_dynamic_loaded_scheduled; intro RUN; bind_imp_destruct RUN generated GENERATED.
  destruct generated as [candidate|];
    [eapply check_affine_dynamic_loaded_mapped_sound; exact RUN|apply mayReturn_pure in RUN; discriminate].
Qed.

Definition check_affine_dynamic_loaded_package live pool (propose : affine_inner_pointer_proposer)
  source (region : affine_dynamic_loaded_region_package source) :=
  match propose (affine_inner_pointer_request_of (dynamic_loaded_body_cached_package (dynamic_loaded_region_body region))) with
  | Some proposal =>
    let validator_bounds := affine_proposal_validator_bounds proposal in
    let encoder_bounds := affine_proposal_encoder_bounds proposal in
    match affine_proposal_candidate proposal with
    | AffineInnerMappedProposal candidate steps =>
      check_affine_dynamic_loaded_mapped live pool region validator_bounds encoder_bounds candidate steps
    | AffineInnerTilingProposal candidate witnesses =>
      check_affine_dynamic_loaded_tiled live pool region validator_bounds encoder_bounds candidate witnesses
    | AffineInnerScheduleProposal schedules steps =>
      check_affine_dynamic_loaded_scheduled live pool region validator_bounds encoder_bounds schedules steps
    end
  | None => pure None end.
Theorem check_affine_dynamic_loaded_package_sound live pool propose source (region : affine_dynamic_loaded_region_package source) target :
  mayReturn (check_affine_dynamic_loaded_package live pool propose region) (Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  unfold check_affine_dynamic_loaded_package; destruct (propose _) as [proposal|].
  - destruct (affine_proposal_candidate proposal); intro RUN;
      [eapply check_affine_dynamic_loaded_mapped_sound|eapply check_affine_dynamic_loaded_tiled_sound|
       eapply check_affine_dynamic_loaded_scheduled_sound]; exact RUN.
  - intro RUN; apply mayReturn_pure in RUN; discriminate.
Qed.
Definition check_affine_dynamic_loaded_source live pool profile propose source :=
  match describe_affine_dynamic_loaded_source profile source with
  | Some region => check_affine_dynamic_loaded_package live pool propose region
  | None => pure None end.
Theorem check_affine_dynamic_loaded_source_sound live pool profile propose source target :
  mayReturn (check_affine_dynamic_loaded_source live pool profile propose source) (Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  unfold check_affine_dynamic_loaded_source; destruct (describe_affine_dynamic_loaded_source profile source) as [region|].
  - apply check_affine_dynamic_loaded_package_sound.
  - intro RUN; apply mayReturn_pure in RUN; discriminate.
Qed.

Print Assumptions check_affine_dynamic_loaded_certified_sound.
Print Assumptions check_affine_dynamic_loaded_mapped_sound.
Print Assumptions check_affine_dynamic_loaded_tiled_sound.
Print Assumptions check_affine_dynamic_loaded_scheduled_sound.
Print Assumptions check_affine_dynamic_loaded_package_sound.
Print Assumptions check_affine_dynamic_loaded_source_sound.
