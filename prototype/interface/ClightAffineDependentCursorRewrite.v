From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightTempFrame ClightTempFootprint ClightGuard ClightPrivateRegion
  ClightLoopSyntax ClightStraightLine CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryParametricWidth GuardMemoryAffinePointerLoadedDomain.
From GuardInterface Require Import ClightCheckPlan ClightCheckPlanFrame ClightStagedCheck ClightReadonlyRewrite
  ClightAffineDependentCursorScan ClightAffineDependentCursorResources ClightPreloadSnapshot ClightSourceObservation
  ClightAffinePointerGuard ClightAffinePointerSourcePreparation ClightAffineInnerPointerSourceGuard
  ClightAffineInnerPointerCandidate ClightAffineInnerPointerCandidateGuard ClightAffineInnerPointerPreservation
  ClightAffineDependentLoadedRewrite ClightAffineDependentLoadedStability ClightAffineDependentLoadedPrefix
  ClightDependentCaptureDomain ClightDependentHeaderObservations ClightPrivateScan.
Import ListNotations.
Set Implicit Arguments.

Definition affine_dependent_cursor_guard_scope source (package : memory_affine_inner_pointer_package source)
  width alias validator_bounds encoder_bounds yes no live :=
  check_plan_reads (tree_check_plan (affine_inner_pointer_package_preparation_tree package width)) ++
  check_plan_reads (tree_check_plan (affine_inner_pointer_candidate_guard_tree package width alias validator_bounds encoder_bounds)) ++
  statement_temps yes ++ statement_temps no ++ live.

Definition affine_dependent_cursor_guarded_statement source (package : memory_affine_inner_pointer_package source)
  root pointer_cache outer inner result width alias validator_bounds encoder_bounds yes no :=
  staged_check_guarded (tree_check_plan (affine_inner_pointer_package_preparation_tree package width))
    (affine_dependent_cursor_scan package root pointer_cache outer inner result)
    (tree_check_plan (affine_inner_pointer_candidate_guard_tree package width alias validator_bounds encoder_bounds)) result yes no.

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
Let yes := affine_inner_pointer_candidate_statement candidate.
Let no := affine_dependent_loaded_source package root.
Let before := tree_check_plan (affine_inner_pointer_package_preparation_tree package width).
Let after := tree_check_plan (affine_inner_pointer_package_candidate_guard candidate width alias).
Let protected := affine_dependent_cursor_guard_scope package width alias
  (affine_inner_candidate_validator_bounds candidate) (affine_inner_candidate_encoder_bounds candidate) yes no live.
Variables outer inner result : ident.
Hypotheses (YES : check_plan_frameable yes=true) (NO : check_plan_frameable no=true).
Hypothesis RESOURCES : affine_dependent_cursor_resources package root pointer_cache outer inner result protected.

Definition affine_dependent_cursor_guarded_candidate := affine_dependent_cursor_guarded_statement package root pointer_cache
  outer inner result width alias (affine_inner_candidate_validator_bounds candidate) (affine_inner_candidate_encoder_bounds candidate) yes no.

(** The source model, complete condition and candidate certificate are the
    existing ones. The new implementation materializes their decision with
    two runtime loops and preserves the original loaded fallback. *)
Theorem affine_dependent_cursor_guarded_candidate_execution fe ge locals temps memory source_exit final :
  affine_dependent_loaded_completed package root pointer_cache fe (Entry ge locals temps memory) ->
  exec_stmt fe ge locals temps memory no E0 source_exit final Out_normal ->
  exists target,
    exec_stmt fe ge locals temps memory affine_dependent_cursor_guarded_candidate E0 target final Out_normal /\
    temp_agree live source_exit target.
Proof.
  intros DOMAIN SOURCE.
  destruct (@affine_dependent_loaded_guarded_candidate_execution source package root pointer_cache ROOT_FRESH POINTER_FRESH
    live candidate width alias WIDTH ALIAS fe ge locals temps memory source_exit final DOMAIN SOURCE) as [old [RUN PUBLIC]].
  unfold affine_dependent_loaded_guarded_candidate in RUN.
  change (clight_fragment_run fe (tree_statement
    (decision_bind (decision_bind (affine_inner_pointer_package_preparation_tree package width)
      (affine_dependent_stability_tree package root pointer_cache (Z.to_nat (affine_inner_pointer_row_limit package)) 0%Z) (Decision false))
      (affine_inner_pointer_package_candidate_guard candidate width alias) (Decision false)) yes no)
    (Entry ge locals temps memory) (FragmentObservation E0 old final Out_normal)) in RUN.
  destruct (proj1 (@readonly_tree_execution_exact fe _ yes no (Entry ge locals temps memory)
    (FragmentObservation E0 old final Out_normal)) RUN) as [answer [CHECK BRANCH]].
  assert (SPEC : decision_run (Entry ge locals temps memory)
    (staged_check_spec before (affine_dependent_stability_tree package root pointer_cache (Z.to_nat (affine_inner_pointer_row_limit package)) 0%Z) after) answer).
  { unfold staged_check_spec,before,after; rewrite !tree_check_plan_spec; exact CHECK. }
  destruct RESOURCES as [[OUTER_INNER [OUTER_RESULT INNER_RESULT]] [OUTER_PRIVATE [INNER_PRIVATE RESULT_PRIVATE]]
    [CACHE [ROOT_CURSOR POINTER_CURSOR]] BOUND OPERATIONS RESULT_FRESH OUTER_READS INNER_READS POINT_READS].
  assert (BEFORE_FRESH : ~ In result (check_plan_reads before)).
  { intro MEMBER; apply RESULT_PRIVATE; unfold protected,affine_dependent_cursor_guard_scope;
      apply in_or_app; left; exact MEMBER. }
  assert (AFTER_SCOPE : incl (check_plan_reads after) protected).
  { intros id MEMBER; unfold protected,affine_dependent_cursor_guard_scope; apply in_or_app; right; apply in_or_app; left; exact MEMBER. }
  assert (AFTER_FRESH : ~ In result (check_plan_reads after)) by (intro MEMBER; apply RESULT_PRIVATE,AFTER_SCOPE; exact MEMBER).
  assert (BRANCH_SCOPE : incl (statement_temps yes++statement_temps no++live) protected).
  { intros id MEMBER; unfold protected,affine_dependent_cursor_guard_scope; apply in_or_app; right; apply in_or_app; right; exact MEMBER. }
  assert (MIDDLE : forall current choice, temp_agree protected temps current ->
    decision_run (Entry ge locals temps memory) (affine_dependent_stability_tree package root pointer_cache
      (Z.to_nat (affine_inner_pointer_row_limit package)) 0%Z) choice ->
    exists exit, exec_stmt fe ge locals current memory (affine_dependent_cursor_scan package root pointer_cache outer inner result)
      E0 exit memory Out_normal /\ temp_agree protected current exit /\ exit ! result=Some (Vint (ClightSharedGuard.shared_guard_word choice))).
  { intros current choice FRAME POINT.
    exact (@affine_dependent_cursor_scan_execution_current source package root pointer_cache outer inner result protected
      OUTER_INNER OUTER_RESULT INNER_RESULT OUTER_PRIVATE INNER_PRIVATE RESULT_PRIVATE CACHE ROOT_CURSOR POINTER_CURSOR
      BOUND OPERATIONS RESULT_FRESH OUTER_READS INNER_READS POINT_READS fe ROOT_FRESH POINTER_FRESH
      (Entry ge locals temps memory) current choice FRAME POINT). }
  destruct (@staged_check_guarded_execution fe (Entry ge locals temps memory) before after
    (affine_dependent_cursor_scan package root pointer_cache outer inner result)
    (affine_dependent_stability_tree package root pointer_cache (Z.to_nat (affine_inner_pointer_row_limit package)) 0%Z)
    result protected RESULT_PRIVATE BEFORE_FRESH AFTER_FRESH AFTER_SCOPE MIDDLE
    live yes no answer old final YES NO BRANCH_SCOPE SPEC BRANCH) as [target [ACTUAL FRAME]].
  exists target; split; [exact ACTUAL|eapply temp_agree_trans; [exact PUBLIC|exact FRAME]].
Qed.

Theorem affine_dependent_cursor_prefix_contract loads :
  pointer_cache <> root -> affine_inner_pointer_bound (affine_inner_pointer_shape package) <> root ->
  affine_inner_pointer_bound (affine_inner_pointer_shape package) <> pointer_cache ->
  ~ In pointer_cache (source_load_pointers loads) ->
  ~ In (affine_inner_pointer_bound (affine_inner_pointer_shape package)) (source_load_pointers loads) ->
  source_observations_check (affine_inner_pointer_pointers package) loads=true ->
  PrivateRegion.projected_region_contract live
    (Ssequence (dependent_guard_prefix loads root pointer_cache (affine_inner_pointer_bound (affine_inner_pointer_shape package))) no)
    (Ssequence (dependent_guard_prefix loads root pointer_cache (affine_inner_pointer_bound (affine_inner_pointer_shape package)))
      affine_dependent_cursor_guarded_candidate).
Proof.
  intros POINTER_ROOT CACHE_ROOT DISTINCT POINTER_PRIVATE CACHE_PRIVATE OBSERVED.
  apply source_prefix_region_contract with
    (writes:=statement_temps (Ssequence (dependent_guard_prefix loads root pointer_cache
      (affine_inner_pointer_bound (affine_inner_pointer_shape package))) no))
    (domain:=fun entry => ClightRedundantSet.register_domain (affine_inner_pointer_row (affine_inner_pointer_shape package)) entry /\
      dependent_cached_header root pointer_cache (affine_inner_pointer_bound (affine_inner_pointer_shape package)) entry /\
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
  - intros temps program locals entry memory source_exit final SCOPE [ROW [CACHE POINTERS]] SOURCE.
    assert (DOMAIN : affine_dependent_loaded_completed package root pointer_cache (adapter_entry temps)
      (Entry (globalenv program) locals entry memory)).
    { split; [exact ROW|split; [exact CACHE|split; [exact POINTERS|exists source_exit,final; exact SOURCE]]]. }
    destruct (@affine_dependent_cursor_guarded_candidate_execution (adapter_entry temps) (globalenv program) locals entry memory
      source_exit final DOMAIN SOURCE) as [target [RUN PUBLIC]].
    exists target,final; split; [exact RUN|split; [exact PUBLIC|apply memory_equivalent_refl]].
Qed.
End REWRITE.

Print Assumptions affine_dependent_cursor_guarded_candidate_execution.
Print Assumptions affine_dependent_cursor_prefix_contract.
