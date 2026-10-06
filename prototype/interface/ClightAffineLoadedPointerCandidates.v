From Stdlib Require Import List Bool.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightCondition ClightPureExpr ClightPrivateRegion ClightPrivatePool ClightSyntaxEquality.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryParametricWidth
  GuardMemoryMultiPointerCompiler GuardMemoryMultiPointerBackend GuardMemoryAffineInnerPointerRegionSource GuardMemoryParametricRestore
  GuardMemoryScheduleProducer GuardMemoryParametricGuard GuardMemoryParametricChecker GuardMemoryTiledCompiler.
From GuardInterface Require Import ClightAffineLoadedPointerRewrite ClightAffinePointerGuardExamples
  ClightAffineInnerPointerCandidate ClightAffineInnerPointerCandidateGuard ClightAffineInnerPointerCandidates
  ClightAffineInnerPointerPreservation ClightSourceObservation ClightAffinePointerGuard
  ClightAffineInnerPointerSourceGuard ClightReadonlyRewrite ClightConditionComposition
  ClightObservedPointerSyntax ClightSequenceContracts.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

(** Initial installation profile: the retained-preload fixture, with checked
    sequence association and a retained quiet suffix. Its fixed identifiers
    are not a general frontend profile. Candidate proposals remain untrusted. *)
Definition checked_alp_target validator_bounds encoder_bounds width alias code :=
  Ssequence (source_load_prefix alp_loads)
    (tree_statement (decision_bind alp_preliminary
      (affine_inner_pointer_candidate_guard_tree alp_cached_package width alias validator_bounds encoder_bounds)
      (Decision false))
      (Ssequence code (memory_parametric_restore ap_i ap_n ap_j ap_k
        (affine_inner_pointer_expression alp_cached_package))) ClightAffineLoadedPointerExample.alp_source).

Definition check_alp_certified live pool validator_bounds encoder_bounds candidate
  (check : CoreAlarmed.Base.imp bool) : CoreAlarmed.Base.imp (option statement) :=
  match compile_memory_source_width (affine_inner_pointer_column_limit alp_cached_package)
    (affine_inner_pointer_row (affine_inner_pointer_shape alp_cached_package))
    (memory_affine_inner_pointer_header (affine_inner_pointer_shape alp_cached_package)
      (affine_inner_pointer_expression alp_cached_package))
    (affine_inner_pointer_header_bounds (affine_inner_pointer_row_limit alp_cached_package)
      (affine_inner_pointer_header_limits alp_cached_package))
    (affine_inner_pointer_expression alp_cached_package),
    compile_affine_inner_pointer_package_envelopes alp_cached_package, private_counter_pairs pool with
  | Some width, Some alias, Some pairs =>
    match compile_memory_multi_pointer_buffer_loop (affine_inner_pointer_pointers alp_cached_package)
      (memory_affine_inner_pointer_region_context alp_cached_package) encoder_bounds live pairs candidate with
    | Some code => BIND valid <- check -;
      pure (if valid then Some (checked_alp_target validator_bounds encoder_bounds width alias code) else None)
    | None => pure None end
  | _,_,_ => pure None end.

Theorem check_alp_certified_sound live pool validator_bounds encoder_bounds candidate check target :
  (mayReturn check true -> affine_inner_pointer_candidate_certificate alp_cached_package validator_bounds candidate) ->
  mayReturn (check_alp_certified live pool validator_bounds encoder_bounds candidate check) (Some target) ->
  PrivateRegion.projected_region_contract live alp_observed_source target.
Proof.
  intro CERTIFICATE; unfold check_alp_certified.
  destruct (compile_memory_source_width _ _ _ _ _) as [width|] eqn:WIDTH;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_affine_inner_pointer_package_envelopes alp_cached_package) as [alias|] eqn:ALIAS;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (private_counter_pairs pool) as [pairs|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_memory_multi_pointer_buffer_loop _ _ _ _ _ _) as [code|] eqn:COMPILE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN;
    destruct valid; [injection RUN as <-|discriminate].
  pose (certified := @Build_affine_inner_pointer_candidate_package ap_source alp_cached_package live
    validator_bounds encoder_bounds candidate pairs code COMPILE (CERTIFICATE VALID)).
  change (PrivateRegion.projected_region_contract live alp_observed_source
    (Ssequence (source_load_prefix alp_loads) (alp_guarded_candidate certified width alias))).
  apply alp_observed_candidate_contract; assumption.
Qed.

Definition check_alp_mapped live pool validator_bounds encoder_bounds candidate steps :=
  check_alp_certified live pool validator_bounds encoder_bounds candidate
    (check_affine_inner_pointer_model alp_cached_package validator_bounds candidate steps).
Theorem check_alp_mapped_sound live pool validator_bounds encoder_bounds candidate steps target :
  mayReturn (check_alp_mapped live pool validator_bounds encoder_bounds candidate steps) (Some target) ->
  PrivateRegion.projected_region_contract live alp_observed_source target.
Proof. apply check_alp_certified_sound, check_affine_inner_pointer_model_sound. Qed.

Definition check_alp_tiled live pool validator_bounds encoder_bounds candidate witnesses :=
  check_alp_certified live pool validator_bounds encoder_bounds candidate
    (check_affine_inner_pointer_tiling_model alp_cached_package validator_bounds candidate witnesses).
Theorem check_alp_tiled_sound live pool validator_bounds encoder_bounds candidate witnesses target :
  mayReturn (check_alp_tiled live pool validator_bounds encoder_bounds candidate witnesses) (Some target) ->
  PrivateRegion.projected_region_contract live alp_observed_source target.
Proof. apply check_alp_certified_sound, check_affine_inner_pointer_tiling_model_sound. Qed.

Definition check_alp_scheduled live pool validator_bounds encoder_bounds schedules steps :=
  let context := memory_affine_inner_pointer_region_context alp_cached_package in
  let arrays := affine_inner_pointer_pointers alp_cached_package in
  BIND generated <- memory_generate_scheduled_loop
    (memory_parametric_assumed_loop (affine_inner_pointer_candidate_base alp_cached_package)
      (affine_inner_pointer_row (affine_inner_pointer_shape alp_cached_package)) context validator_bounds
      (affine_inner_pointer_expression alp_cached_package)
      (memory_affine_inner_pointer_region_model alp_cached_package),context,
      map (fun identifier => (identifier,tt)) (context++arrays)) schedules -;
  match generated with
  | Some candidate => check_alp_mapped live pool validator_bounds encoder_bounds
      (propose_affine_inner_candidate_normalization encoder_bounds O candidate) steps
  | None => pure None end.
Theorem check_alp_scheduled_sound live pool validator_bounds encoder_bounds schedules steps target :
  mayReturn (check_alp_scheduled live pool validator_bounds encoder_bounds schedules steps) (Some target) ->
  PrivateRegion.projected_region_contract live alp_observed_source target.
Proof.
  unfold check_alp_scheduled; intro RUN; bind_imp_destruct RUN generated GENERATED.
  destruct generated as [candidate|];
    [eapply check_alp_mapped_sound; exact RUN|apply mayReturn_pure in RUN; discriminate].
Qed.

Definition check_alp_package live pool (propose : affine_inner_pointer_proposer) :=
  match propose (affine_inner_pointer_request_of alp_cached_package) with
    | Some proposal =>
      let validator_bounds := affine_proposal_validator_bounds proposal in
      let encoder_bounds := affine_proposal_encoder_bounds proposal in
      match affine_proposal_candidate proposal with
      | AffineInnerMappedProposal candidate steps =>
        check_alp_mapped live pool validator_bounds encoder_bounds candidate steps
      | AffineInnerTilingProposal candidate witnesses =>
        check_alp_tiled live pool validator_bounds encoder_bounds candidate witnesses
      | AffineInnerScheduleProposal schedules steps =>
        check_alp_scheduled live pool validator_bounds encoder_bounds schedules steps
      end
    | None => pure None end.
Theorem check_alp_package_sound live pool propose target :
  mayReturn (check_alp_package live pool propose) (Some target) ->
  PrivateRegion.projected_region_contract live alp_observed_source target.
Proof.
  unfold check_alp_package.
  destruct (propose (affine_inner_pointer_request_of alp_cached_package)) as [proposal|].
  - destruct (affine_proposal_candidate proposal); intro RUN;
      [eapply check_alp_mapped_sound|eapply check_alp_tiled_sound|eapply check_alp_scheduled_sound]; exact RUN.
  - intro RUN; apply mayReturn_pure in RUN; discriminate.
Qed.

Definition check_alp_source live pool propose source :=
  match describe_observed_pointer_source source with
  | Some observed =>
    if statement_eq (Ssequence (source_load_prefix (observed_source_loads observed))
        (observed_source_loop observed)) alp_observed_source then
      BIND candidate <- check_alp_package live pool propose -;
      pure (option_map (fun target => Ssequence target (observed_source_suffix observed)) candidate)
    else pure None
  | None => pure None end.
Theorem check_alp_source_sound live pool propose source target :
  mayReturn (check_alp_source live pool propose source) (Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  unfold check_alp_source; destruct (describe_observed_pointer_source source) as [observed|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (statement_eq _ _) as [EQ|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN candidate CANDIDATE; apply mayReturn_pure in RUN;
    destruct candidate as [candidate|]; [injection RUN as <-|discriminate].
  eapply flattened_projected_region_contract; [exact (observed_source_flat observed)|].
  apply projected_region_quiet_suffix; [exact (observed_source_suffix_quiet observed)|].
  rewrite EQ; eapply check_alp_package_sound; exact CANDIDATE.
Qed.

Print Assumptions check_alp_certified_sound.
Print Assumptions check_alp_mapped_sound.
Print Assumptions check_alp_tiled_sound.
Print Assumptions check_alp_scheduled_sound.
Print Assumptions check_alp_package_sound.
Print Assumptions check_alp_source_sound.
