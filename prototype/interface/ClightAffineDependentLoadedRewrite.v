From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightGuard ClightNoWrap ClightTempFrame
  ClightPrivateRegion ClightRegionProgress ClightLoopSyntax ClightStraightLine ClightCountedLoop
  ClightFrontendLoopProtocol CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryParametricWidth
  GuardMemoryAffinePointerLoadedDomain GuardMemoryParametricSourceClight.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ReadonlyConditionComposition
  ClightConditionComposition ClightPreloadSnapshot ClightSourceObservation ClightLoadedBoundSyntax
  ClightAffinePointerGuard ClightAffinePointerSourcePreparation ClightAffineInnerPointerSourceGuard
  ClightAffineInnerPointerCandidateGuard ClightAffineInnerPointerCandidate ClightAffineInnerPointerPreservation
  ClightAffineLoadedSourceGuard ClightAffineLoadedRewrite ClightAffineLoadedStability ClightAffineDynamicLoadedCache
  ClightAffineDependentLoadedPrefix ClightAffineDependentLoadedPreparation
  ClightAffineDependentLoadedStability ClightAffineDependentLoadedCache.
Import ListNotations.
Set Implicit Arguments.

Section REWRITE.
Variable source : statement.
Variable package : memory_affine_inner_pointer_package source.
Variables root pointer_cache : ident.
Hypothesis ROOT_FRESH : root <> affine_inner_pointer_row (affine_inner_pointer_shape package) /\
  root <> affine_inner_pointer_column (affine_inner_pointer_shape package) /\
  root <> affine_inner_pointer_inner_bound (affine_inner_pointer_shape package).
Hypothesis POINTER_FRESH : pointer_cache <> affine_inner_pointer_row (affine_inner_pointer_shape package) /\
  pointer_cache <> affine_inner_pointer_column (affine_inner_pointer_shape package) /\
  pointer_cache <> affine_inner_pointer_inner_bound (affine_inner_pointer_shape package).
Variable live : list ident.
Variable candidate : affine_inner_pointer_candidate_package package live.
Variables width alias : decision_tree.
Hypothesis WIDTH : compile_memory_source_width (affine_inner_pointer_column_limit package)
  (affine_inner_pointer_row (affine_inner_pointer_shape package))
  (memory_affine_inner_pointer_header (affine_inner_pointer_shape package) (affine_inner_pointer_expression package))
  (affine_inner_pointer_header_bounds (affine_inner_pointer_row_limit package) (affine_inner_pointer_header_limits package))
  (affine_inner_pointer_expression package) = Some width.
Hypothesis ALIAS : compile_affine_inner_pointer_package_envelopes package = Some alias.

Definition affine_dependent_loaded_guarded_candidate := tree_statement
  (decision_bind (decision_bind (affine_inner_pointer_package_preparation_tree package width)
    (affine_dependent_stability_tree package root pointer_cache (Z.to_nat (affine_inner_pointer_row_limit package)) 0%Z) (Decision false))
    (affine_inner_pointer_package_candidate_guard candidate width alias) (Decision false))
  (affine_inner_pointer_candidate_statement candidate) (affine_dependent_loaded_source package root).

Definition affine_dependent_loaded_candidate_condition fe O (observe : fragment_observation -> O -> Prop) :
  readonly_condition (readonly_clight_host fe observe)
    (fun entry => affine_dependent_loaded_completed package root pointer_cache fe entry /\
      (affine_inner_pointer_ready package entry /\ affine_dependent_writes_separated package root pointer_cache entry))
    (fun entry => (affine_inner_pointer_ready package entry /\ affine_inner_pointer_source_nonalias package entry) /\
      affine_inner_pointer_candidate_ranges package (affine_inner_candidate_validator_bounds candidate)
        (affine_inner_candidate_encoder_bounds candidate) entry)
    (affine_inner_pointer_package_candidate_guard candidate width alias).
Proof.
  eapply readonly_condition_restrict; [exact (@affine_inner_pointer_candidate_guard_condition source package fe
    O observe width alias (affine_inner_candidate_validator_bounds candidate) (affine_inner_candidate_encoder_bounds candidate)
    WIDTH ALIAS)|].
  intros entry [DOMAIN [READY APART]]; eapply (@affine_dependent_cached_domain source package root pointer_cache ROOT_FRESH POINTER_FRESH);
    eassumption.
Defined.

Definition affine_dependent_loaded_prepared_condition fe O (observe : fragment_observation -> O -> Prop) :=
  sequence_readonly_conditions (clight_readonly_check_algebra fe observe)
    (@affine_dependent_preparation_condition source package root pointer_cache fe O observe width WIDTH)
    (@affine_dependent_stability_condition source package root pointer_cache ROOT_FRESH POINTER_FRESH fe O observe).
Definition affine_dependent_loaded_complete_condition fe O (observe : fragment_observation -> O -> Prop) :=
  sequence_readonly_conditions (clight_readonly_check_algebra fe observe)
    (affine_dependent_loaded_prepared_condition fe observe) (affine_dependent_loaded_candidate_condition fe observe).

Theorem affine_dependent_loaded_guarded_candidate_execution fe ge locals temps memory after final :
  affine_dependent_loaded_completed package root pointer_cache fe (Entry ge locals temps memory) ->
  exec_stmt fe ge locals temps memory (affine_dependent_loaded_source package root) E0 after final Out_normal ->
  exists target, exec_stmt fe ge locals temps memory affine_dependent_loaded_guarded_candidate E0 target final Out_normal /\
    temp_agree live after target.
Proof.
  intros DOMAIN SOURCE.
  pose proof DOMAIN as COMPLETED.
  pose proof (@affine_dependent_loaded_complete_condition fe fragment_observation (@eq fragment_observation)) as CHECK.
  destruct (readonly_available CHECK _ COMPLETED) as [accepted [checked [RUN SAME]]]; subst checked.
  unfold affine_dependent_loaded_guarded_candidate; destruct accepted.
  - destruct (readonly_sound CHECK _ _ _ COMPLETED (conj RUN eq_refl)) as [_ SOUND].
    destruct (SOUND eq_refl) as [[PREPARED APART] [[READY NONALIAS] RANGES]].
    assert (CACHED : exec_stmt fe ge locals temps memory source E0 after final Out_normal).
    { eapply (@affine_dependent_cache_execution source package root pointer_cache ROOT_FRESH POINTER_FRESH fe (Entry ge locals temps memory));
        eassumption. }
    destruct (@affine_inner_pointer_candidate_execution source package live candidate fe ge locals temps memory after final
      READY NONALIAS RANGES CACHED) as [target [EXECUTE PUBLIC]].
    exists target; split; [|exact PUBLIC].
    eapply decision_fragment_run with (b:=true); [exact RUN|exact EXECUTE].
  - exists after; split; [|apply temp_agree_refl].
    eapply decision_fragment_run with (b:=false); [exact RUN|exact SOURCE].
Qed.

End REWRITE.

Print Assumptions affine_dependent_loaded_candidate_condition.
Print Assumptions affine_dependent_loaded_prepared_condition.
Print Assumptions affine_dependent_loaded_complete_condition.
Print Assumptions affine_dependent_loaded_guarded_candidate_execution.
