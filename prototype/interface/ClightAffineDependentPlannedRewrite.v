From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightGuard ClightPrivateRegion
  ClightLoopSyntax ClightStraightLine CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryParametricWidth GuardMemoryAffinePointerLoadedDomain.
From GuardInterface Require Import ClightCheckPlan ClightCheckPlanFrame ClightAffineLoadedCheckPlan
  ClightReadonlyRewrite ClightPreloadSnapshot ClightSourceObservation ClightAffinePointerGuard
  ClightAffineInnerPointerCandidate ClightAffineInnerPointerCandidateGuard ClightAffineLoadedRewrite
  ClightAffineInnerPointerSourceGuard ClightAffinePointerSourcePreparation ClightAffineLoadedStability
  ClightAffineInnerPointerPreservation
  ClightAffineDynamicLoadedRewrite ClightAffineDependentCheckPlan ClightAffineDependentLoadedRewrite
  ClightAffineDependentLoadedPrefix ClightDependentCaptureDomain ClightPrivateScan.
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
Let plan := affine_dependent_complete_plan package root pointer_cache width alias
  (affine_inner_candidate_validator_bounds candidate) (affine_inner_candidate_encoder_bounds candidate).
Let yes := affine_inner_pointer_candidate_statement candidate.
Let no := affine_dependent_loaded_source package root.
Variable result : ident.
Hypotheses (YES : check_plan_frameable yes = true) (NO : check_plan_frameable no = true).
Hypothesis PRIVATE : ~ In result (check_plan_reads plan++statement_temps yes++statement_temps no++live).

Definition affine_dependent_planned_guarded_candidate := check_plan_guarded_statement plan result yes no.

(** Reuse the complete original condition and candidate proof. The only new
    obligation is the language implementation and its private public frame;
    neither the semantic premise nor candidate certificate changes. *)
Theorem affine_dependent_planned_guarded_candidate_execution fe ge locals temps memory after final :
  affine_dependent_loaded_completed package root pointer_cache fe (Entry ge locals temps memory) ->
  exec_stmt fe ge locals temps memory no E0 after final Out_normal ->
  exists target, exec_stmt fe ge locals temps memory affine_dependent_planned_guarded_candidate E0 target final Out_normal /\
    temp_agree live after target.
Proof.
  intros DOMAIN SOURCE.
  destruct (@affine_dependent_loaded_guarded_candidate_execution source package root pointer_cache ROOT_FRESH POINTER_FRESH live candidate
    width alias WIDTH ALIAS fe ge locals temps memory after final DOMAIN SOURCE) as [old [RUN PUBLIC]].
  unfold affine_dependent_loaded_guarded_candidate in RUN.
  unfold affine_inner_pointer_package_candidate_guard in RUN.
  rewrite <- affine_dependent_complete_plan_tree in RUN; fold plan in RUN.
  change (clight_fragment_run fe (tree_statement (check_plan_tree plan) yes no)
    (Entry ge locals temps memory) (FragmentObservation E0 old final Out_normal)) in RUN.
  destruct (proj1 (@readonly_tree_execution_exact fe (check_plan_tree plan) yes no
    (Entry ge locals temps memory) (FragmentObservation E0 old final Out_normal)) RUN)
    as [answer [CHECK BRANCH]].
  destruct (@check_plan_guarded_normal_execution fe ge locals temps memory plan result live yes no
    answer old final CHECK YES NO PRIVATE BRANCH) as [target [EXECUTE FRAME]].
  exists target; split; [exact EXECUTE|eapply temp_agree_trans; eassumption].
Qed.

Theorem affine_dependent_planned_prefix_contract loads :
  pointer_cache <> root -> affine_inner_pointer_bound (affine_inner_pointer_shape package) <> root ->
  affine_inner_pointer_bound (affine_inner_pointer_shape package) <> pointer_cache ->
  ~ In pointer_cache (source_load_pointers loads) ->
  ~ In (affine_inner_pointer_bound (affine_inner_pointer_shape package)) (source_load_pointers loads) ->
  source_observations_check (affine_inner_pointer_pointers package) loads = true ->
  PrivateRegion.projected_region_contract live
    (Ssequence (dependent_guard_prefix loads root pointer_cache (affine_inner_pointer_bound (affine_inner_pointer_shape package))) no)
    (Ssequence (dependent_guard_prefix loads root pointer_cache (affine_inner_pointer_bound (affine_inner_pointer_shape package)))
      affine_dependent_planned_guarded_candidate).
Proof.
  intros POINTER_ROOT CACHE_ROOT DISTINCT POINTER_PRIVATE CACHE_PRIVATE OBSERVED.
  apply source_prefix_region_contract with
    (writes:=statement_temps (Ssequence (dependent_guard_prefix loads root pointer_cache
      (affine_inner_pointer_bound (affine_inner_pointer_shape package))) no))
    (domain:=fun entry => ClightRedundantSet.register_domain (affine_inner_pointer_row (affine_inner_pointer_shape package)) entry /\
      ClightDependentHeaderObservations.dependent_cached_header root pointer_cache
        (affine_inner_pointer_bound (affine_inner_pointer_shape package)) entry /\
      observed_pointer_domain (affine_inner_pointer_pointers package) entry).
  - apply dependent_guard_prefix_supported.
  - apply writes_sequence.
    + eapply writes_only_weaken; [intros id MEMBER; apply in_or_app; left; exact MEMBER|].
      exact (@private_scan_write_bound (dependent_guard_prefix loads root pointer_cache
        (affine_inner_pointer_bound (affine_inner_pointer_shape package)))
        (dependent_guard_prefix_supported loads root pointer_cache (affine_inner_pointer_bound (affine_inner_pointer_shape package)))).
    + eapply writes_only_weaken; [intros id MEMBER; apply in_or_app; right; exact MEMBER|].
      exact (@check_plan_frameable_writes no NO).
  - intros; destruct (@dependent_guard_prefix_domain source package loads root pointer_cache _ _ _ _ _ _ _ _
      POINTER_ROOT CACHE_ROOT DISTINCT POINTER_PRIVATE CACHE_PRIVATE OBSERVED ltac:(eassumption) ltac:(eassumption))
      as [ROW [CACHE [POINTERS SOURCE]]]; repeat split; assumption.
  - intros temps p locals entry memory after final SCOPE [ROW [CACHE POINTERS]] SOURCE.
    assert (DOMAIN : affine_dependent_loaded_completed package root pointer_cache (adapter_entry temps)
      (Entry (globalenv p) locals entry memory)).
    { split; [exact ROW|split; [exact CACHE|split; [exact POINTERS|exists after,final; exact SOURCE]]]. }
    destruct (@affine_dependent_planned_guarded_candidate_execution (adapter_entry temps) (globalenv p) locals entry memory
      after final DOMAIN SOURCE) as [target [EXECUTE PUBLIC]].
    exists target,final; split; [exact EXECUTE|split; [exact PUBLIC|apply memory_equivalent_refl]].
Qed.
End REWRITE.

Print Assumptions affine_dependent_planned_guarded_candidate_execution.
Print Assumptions affine_dependent_planned_prefix_contract.
