From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightGuard ClightNoWrap ClightTempFrame
  ClightPrivateRegion ClightRegionProgress ClightLoopSyntax ClightStraightLine ClightCountedLoop
  ClightFrontendLoopProtocol CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryParametricWidth
  GuardMemoryAffinePointerLoadedDomain GuardMemoryAffinePointerLoadedCache GuardMemoryObservationExclusion
  GuardMemoryParametricSourceClight GuardMemoryPointerSequence.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyLoadedTreeSynthesis
  ReadonlyConditionComposition ClightConditionComposition ClightPreloadSnapshot ClightSourceObservation
  ClightLoadedBoundSyntax ClightStrictLoopProgress ClightAffinePointerGuard
  ClightAffinePointerSourcePreparation ClightAffineInnerPointerSourceGuard ClightAffineInnerPointerCandidateGuard ClightAffineInnerPointerCandidate
  ClightAffineInnerPointerPreservation ClightAffineLoadedSourceGuard.
Import ListNotations.
Set Implicit Arguments.

Section REWRITE.
Variable source : statement.
Variable package : memory_affine_inner_pointer_package source.
Variable pointer : ident.
Hypothesis MEMBER : In pointer (affine_inner_pointer_pointers package).
Hypothesis EXCLUDED : memory_writes_exclude_cell
  (memory_affine_inner_pointer_limits (affine_inner_pointer_row_limit package) (affine_inner_pointer_column_limit package)
    (affine_inner_pointer_header_limits package) (affine_inner_pointer_body_limits package))
  (affine_inner_pointer_extent package) pointer 0%Z (affine_inner_pointer_operations package) = true.
Variable live : list ident.
Variable candidate : affine_inner_pointer_candidate_package package live.
Variables width alias : decision_tree.
Hypothesis WIDTH : compile_memory_source_width (affine_inner_pointer_column_limit package)
  (affine_inner_pointer_row (affine_inner_pointer_shape package))
  (memory_affine_inner_pointer_header (affine_inner_pointer_shape package) (affine_inner_pointer_expression package))
  (affine_inner_pointer_header_bounds (affine_inner_pointer_row_limit package) (affine_inner_pointer_header_limits package))
  (affine_inner_pointer_expression package) = Some width.
Hypothesis ALIAS : compile_affine_inner_pointer_package_envelopes package = Some alias.

Definition affine_loaded_guarded_candidate := tree_statement
  (decision_bind (affine_inner_pointer_package_preparation_tree package width)
    (affine_inner_pointer_package_candidate_guard candidate width alias) (Decision false))
  (affine_inner_pointer_candidate_statement candidate) (memory_affine_pointer_loaded_source package pointer).

Definition affine_loaded_candidate_condition fe O (observe : fragment_observation -> O -> Prop) :
  readonly_condition (readonly_clight_host fe observe)
    (fun entry => memory_affine_pointer_loaded_completed package pointer fe entry /\ affine_inner_pointer_ready package entry)
    (fun entry => (affine_inner_pointer_ready package entry /\ affine_inner_pointer_source_nonalias package entry) /\
      affine_inner_pointer_candidate_ranges package (affine_inner_candidate_validator_bounds candidate)
        (affine_inner_candidate_encoder_bounds candidate) entry)
    (affine_inner_pointer_package_candidate_guard candidate width alias).
Proof.
  eapply readonly_condition_restrict; [exact (@affine_inner_pointer_candidate_guard_condition source package fe
    O observe width alias (affine_inner_candidate_validator_bounds candidate) (affine_inner_candidate_encoder_bounds candidate)
    WIDTH ALIAS)|].
  intros entry [DOMAIN PREPARED]; eapply affine_loaded_prepared_cached_domain;
    [exact MEMBER|exact EXCLUDED|exact DOMAIN|exact PREPARED].
Defined.
Definition affine_loaded_complete_condition fe O (observe : fragment_observation -> O -> Prop) :=
  sequence_readonly_conditions (clight_readonly_check_algebra fe observe)
    (@affine_loaded_preparation_condition source package pointer fe O observe width WIDTH)
    (affine_loaded_candidate_condition fe observe).

Theorem affine_loaded_guarded_candidate_execution fe ge locals temps memory after final :
  loaded_preload_domain (affine_inner_pointer_row (affine_inner_pointer_shape package))
    (affine_inner_pointer_bound (affine_inner_pointer_shape package)) pointer (affine_inner_pointer_pointers package)
    (Entry ge locals temps memory) ->
  exec_stmt fe ge locals temps memory (memory_affine_pointer_loaded_source package pointer) E0 after final Out_normal ->
  exists target, exec_stmt fe ge locals temps memory affine_loaded_guarded_candidate E0 target final Out_normal /\
    temp_agree live after target.
Proof.
  intros DOMAIN SOURCE.
  assert (COMPLETED : memory_affine_pointer_loaded_completed package pointer fe (Entry ge locals temps memory))
    by (split; [exact DOMAIN|exists after,final; exact SOURCE]).
  pose proof (@affine_loaded_complete_condition fe fragment_observation (@eq fragment_observation)) as CHECK.
  destruct (readonly_available CHECK _ COMPLETED) as [accepted [checked [RUN SAME]]]; subst checked.
  unfold affine_loaded_guarded_candidate; destruct accepted.
  - destruct (readonly_sound CHECK _ _ _ COMPLETED (conj RUN eq_refl)) as [_ SOUND].
    destruct (SOUND eq_refl) as [PREPARED [[READY NONALIAS] RANGES]].
    assert (CACHED : exec_stmt fe ge locals temps memory source E0 after final Out_normal).
    { eapply memory_affine_pointer_loaded_cache_under_ranges;
      [exact MEMBER|exact EXCLUDED|exact DOMAIN|exact (affine_inner_pointer_ready_header PREPARED)|
       exact (affine_inner_pointer_ready_width PREPARED)|exact (affine_inner_pointer_ready_ranges PREPARED)|
       exact (affine_inner_pointer_ready_view PREPARED)|exact SOURCE]. }
    destruct (@affine_inner_pointer_candidate_execution source package live candidate fe ge locals temps memory after final
      READY NONALIAS RANGES CACHED) as [target [EXECUTE PUBLIC]].
    exists target; split; [|exact PUBLIC].
    eapply decision_fragment_run with (b:=true); [exact RUN|exact EXECUTE].
  - exists after; split; [|apply temp_agree_refl].
    eapply decision_fragment_run with (b:=false); [exact RUN|exact SOURCE].
Qed.

Lemma affine_loaded_source_writes : writes_only
  [affine_inner_pointer_row (affine_inner_pointer_shape package);
   affine_inner_pointer_inner_bound (affine_inner_pointer_shape package);
   affine_inner_pointer_column (affine_inner_pointer_shape package)]
  (memory_affine_pointer_loaded_source package pointer).
Proof.
  assert (OUTER : writes_only
    [affine_inner_pointer_inner_bound (affine_inner_pointer_shape package);
     affine_inner_pointer_column (affine_inner_pointer_shape package)]
    (affine_inner_pointer_outer_body (affine_inner_pointer_shape package))).
  { eapply memory_parametric_outer_writes;
    [eapply memory_pointer_sequence_writes; exact (affine_inner_pointer_body_exact (affine_inner_pointer_syntax package))|
     exact (affine_inner_pointer_outer_exact (affine_inner_pointer_syntax package))]. }
  unfold memory_affine_pointer_loaded_source,loaded_bound_loop,strict_frontend_loop,counter_increment.
  apply writes_loop.
  - apply writes_sequence; [apply writes_sequence; [apply writes_skip|apply writes_if; [apply writes_skip|apply writes_break]]|].
    eapply writes_only_weaken; [|exact OUTER]; cbn; tauto.
  - apply writes_sequence; [apply writes_skip|apply writes_set; cbn; auto].
Qed.

Theorem affine_loaded_observed_candidate_contract loads :
  NoDup (source_load_targets loads) -> source_observations_check (affine_inner_pointer_pointers package) loads = true ->
  In (affine_inner_pointer_bound (affine_inner_pointer_shape package),pointer) loads ->
  PrivateRegion.projected_region_contract live
    (Ssequence (source_load_prefix loads) (memory_affine_pointer_loaded_source package pointer))
    (Ssequence (source_load_prefix loads) affine_loaded_guarded_candidate).
Proof.
  intros UNIQUE OBSERVED RECEIPT.
  apply source_prefix_region_contract with
    (writes:=source_load_targets loads++[affine_inner_pointer_row (affine_inner_pointer_shape package);
      affine_inner_pointer_inner_bound (affine_inner_pointer_shape package);affine_inner_pointer_column (affine_inner_pointer_shape package)])
    (domain:=loaded_preload_domain (affine_inner_pointer_row (affine_inner_pointer_shape package))
      (affine_inner_pointer_bound (affine_inner_pointer_shape package)) pointer (affine_inner_pointer_pointers package)).
  - apply source_load_prefix_supported.
  - apply writes_sequence.
    + eapply writes_only_weaken; [intros identifier IN; apply in_or_app; left; exact IN|apply source_load_prefix_writes].
    + eapply writes_only_weaken; [intros identifier IN; apply in_or_app; right; exact IN|exact affine_loaded_source_writes].
  - intros; eapply source_preload_loaded_domain;
      [exact UNIQUE|exact OBSERVED|exact RECEIPT|eassumption|eassumption].
  - intros temps p locals entry memory after final SCOPE DOMAIN SOURCE.
    destruct (@affine_loaded_guarded_candidate_execution (adapter_entry temps) (globalenv p) locals entry memory after final
      DOMAIN SOURCE) as [target [EXECUTE PUBLIC]].
    exists target,final; split; [exact EXECUTE|split; [exact PUBLIC|apply memory_equivalent_refl]].
Qed.
End REWRITE.

Print Assumptions affine_loaded_candidate_condition.
Print Assumptions affine_loaded_complete_condition.
Print Assumptions affine_loaded_guarded_candidate_execution.
Print Assumptions affine_loaded_source_writes.
Print Assumptions affine_loaded_observed_candidate_contract.
