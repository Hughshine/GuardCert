From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightGuard ClightRegionProgress
  ClightCountedLoop ClightFrontendLoopProtocol ClightNoWrap.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryParametricWidth
  GuardMemoryPointerSequence GuardMemoryAffineInnerPointerSourceDomain.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightQuietDeterminacy
  ClightStrictLoopProgress ClightAffineHeaderSnapshots ClightAffineSnapshotRows ClightAffineSnapshotSourceInputs
  ClightAffineSnapshotPrefix ClightAffineSnapshotTransport ClightAffineSnapshotSyntax ClightAffineSnapshotPreparation
  ClightAffineZeroSnapshotCandidateCondition ClightAffineInnerPointerSourceGuard ClightAffinePointerGuard
  ClightAffineZeroPointerCandidate ClightSourceObservation ClightAffineDomainFacts ClightAffineZeroSnapshotPrefix ClightAffineZeroSnapshotRows ClightAffineZeroSnapshotTransport ClightAffinePreparedState ClightObservedHeaderPrefix ClightAffineZeroSnapshotPreparation ClightFirstReachedWidth.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The condition's AST is independent of the execution and observation
    relations used in its proof. The installed statement uses a fixed choice;
    the execution theorem below works with every function-entry relation. *)
Theorem affine_zero_snapshot_candidate_tree_language_independent original
    (site : affine_snapshot_source_package original) fe O
    (observe : fragment_observation -> O -> Prop) other_fe Other
    (other_observe : fragment_observation -> Other -> Prop) first later alias validator encoder :
  affine_zero_snapshot_candidate_tree site fe observe first later alias validator encoder =
  affine_zero_snapshot_candidate_tree site other_fe other_observe first later alias validator encoder.
Proof.
  unfold affine_zero_snapshot_candidate_tree,affine_zero_snapshot_prepare_and_scan_tree; f_equal; f_equal.
  unfold ClightAffineZeroSnapshotScan.affine_zero_snapshot_scan_tree.
  generalize(BinInt.Z.to_nat(affine_inner_pointer_row_limit(snapshot_cached_package site)))as fuel.
  generalize BinNums.Z0 as start; intros start fuel; revert start.
  induction fuel as [|fuel IH]; intro start;
    cbn [ReadonlyPrefixScan.synthesize_prefix_scan
      ReadonlyConditionComposition.constant_check ReadonlyBranching.branch_check
      ClightConditionComposition.clight_readonly_check_algebra ClightReadonlyBranching.clight_readonly_branch_algebra
      ReadonlyPrefixScan.prefix_active_probe ReadonlyPrefixScan.prefix_point_probe ReadonlyPrefixScan.prefix_next
      ClightAffineZeroSnapshotScan.affine_zero_snapshot_scan_spec ClightObservedBodyPrefix.observed_body_prefix_spec];
    [reflexivity|f_equal; f_equal; apply IH].
Qed.

Definition affine_zero_snapshot_installed_tree original(site:affine_snapshot_source_package original)
    first later alias validator encoder :=
  affine_zero_snapshot_candidate_tree site(adapter_entry true)(@eq fragment_observation)first later alias validator encoder.

(** Transport the given original execution with its exact memory and exits.
    No completion callback or runtime source pre-execution is required. *)
Theorem affine_zero_snapshot_checked_cached_execution original(site:affine_snapshot_source_package original)
    fe ge locals temps memory after final :
  affine_snapshot_original_domain(snapshot_cached_package site)(snapshot_root site)(snapshot_child site)
    (snapshot_child_cache site)(snapshot_original_header site)fe(Entry ge locals temps memory) ->
  affine_domain_ready(snapshot_cached_package site)(Entry ge locals temps memory) ->
  affine_snapshot_point_preservation(snapshot_cached_package site)(snapshot_root site)(snapshot_child site)
    (snapshot_child_cache site)(Entry ge locals temps memory) ->
  exec_stmt fe ge locals temps memory original E0 after final Out_normal ->
  exec_stmt fe ge locals temps memory(snapshot_cached_source site)E0 after final Out_normal.
Proof.
  intros DOMAIN READY STABLE SOURCE.
  set(entry:=Entry ge locals temps memory)in *.
  set(source:=snapshot_cached_source site).
  set(package:=snapshot_cached_package site)in *.
  set(shape:=affine_inner_pointer_shape package).
  set(row:=affine_inner_pointer_row shape).
  set(cache:=affine_inner_pointer_bound shape).
  set(root:=snapshot_root site).
  set(child:=snapshot_child site).
  set(child_cache:=snapshot_child_cache site).
  set(header:=snapshot_original_header site).
  pose proof(affine_inner_pointer_source_exact(affine_inner_pointer_syntax package))as EXACT.
  change(source=memory_affine_inner_pointer_source shape)in EXACT.
  rewrite EXACT.
  pose proof(@affine_zero_snapshot_prepared_entry source package root child child_cache header
    (snapshot_root_protected site)(snapshot_child_protected site)fe entry DOMAIN READY)as PREPARED.
  destruct(@affine_snapshot_initial_words source package root child child_cache header fe entry DOMAIN)
    as [ROW CACHE].
  assert(CAP:signed_range(affine_inner_pointer_row_limit package)).
  { pose proof(affine_inner_pointer_control_limits(affine_inner_pointer_syntax package))as CAPS;
      inversion CAPS; subst; tauto. }
  destruct(@memory_affine_inner_pointer_header_sound shape(affine_inner_pointer_row_limit package)entry
    CAP ROW CACHE(affine_domain_ready_header READY))as [ZERO REST].
  assert(INV:@affine_zero_snapshot_execution_invariant source package root child child_cache entry
    (affine_prepared_count package entry)(entry_temps entry)(entry_memory entry)).
  { exists 0; split; [pose proof(affine_domain_count_range READY); lia|split; [exact ZERO|split]].
    - apply temp_agree_refl.
    - unfold affine_snapshot_observations,header_observations_match; apply Forall_app; split;
        apply cached_signed_initial_observations; [exact(proj1(proj2 PREPARED))|exact(proj2(proj2 PREPARED))]. }
  rewrite(snapshot_source_exact site)in SOURCE.
  exact(proj1(@affine_zero_snapshot_loaded_to_cached source package root child child_cache header
    (snapshot_root_protected site)(snapshot_child_protected site)(snapshot_cache_member site)
    (snapshot_header_word site)(snapshot_cached_body_exact site)fe entry PREPARED STABLE
    (entry_temps entry)(entry_memory entry)E0 after final Out_normal INV SOURCE)).
Qed.

Section EXECUTION.
Variable original : statement.
Variable site : affine_snapshot_source_package original.
Let package := snapshot_cached_package site.
Variable live : list ident.
Variable candidate : affine_zero_pointer_candidate_package package live.
Variables first later alias : decision_tree.
Hypothesis FIRST : compile_first_reached_width 0(affine_inner_pointer_column_limit package)0
  (affine_inner_pointer_row(affine_inner_pointer_shape package))
  (memory_affine_inner_pointer_header(affine_inner_pointer_shape package)(affine_inner_pointer_expression package))
  (affine_zero_snapshot_header_bounds site)(affine_inner_pointer_expression package)=Some first.
Hypothesis LATER : compile_first_reached_width 0(affine_inner_pointer_column_limit package)1
  (affine_inner_pointer_row(affine_inner_pointer_shape package))
  (memory_affine_inner_pointer_header(affine_inner_pointer_shape package)(affine_inner_pointer_expression package))
  (affine_zero_snapshot_header_bounds site)(affine_inner_pointer_expression package)=Some later.
Hypothesis ALIAS : compile_affine_inner_pointer_package_envelopes package=Some alias.
Definition affine_zero_snapshot_guarded_candidate := tree_statement
  (affine_zero_snapshot_installed_tree site first later alias
    (affine_zero_candidate_validator_bounds candidate)(affine_zero_candidate_encoder_bounds candidate))
  (affine_zero_pointer_candidate_statement candidate)original.

Theorem affine_zero_snapshot_guarded_candidate_execution fe ge locals temps memory after final :
  affine_zero_snapshot_candidate_domain site fe(Entry ge locals temps memory) ->
  exec_stmt fe ge locals temps memory original E0 after final Out_normal ->
  exists target,exec_stmt fe ge locals temps memory affine_zero_snapshot_guarded_candidate E0 target final Out_normal /\
    temp_agree live after target.
Proof.
  intros DOMAIN SOURCE.
  pose proof(@affine_zero_snapshot_candidate_condition original site fe fragment_observation(@eq fragment_observation)
    first later alias(affine_zero_candidate_validator_bounds candidate)(affine_zero_candidate_encoder_bounds candidate)
    FIRST LATER ALIAS)as CONDITION.
  destruct(readonly_available CONDITION _ DOMAIN)as [accepted [checked [RUN SAME]]]; subst checked.
  unfold affine_zero_snapshot_guarded_candidate,affine_zero_snapshot_installed_tree.
  rewrite(@affine_zero_snapshot_candidate_tree_language_independent original site(adapter_entry true)
    fragment_observation(@eq fragment_observation)fe fragment_observation(@eq fragment_observation)
    first later alias(affine_zero_candidate_validator_bounds candidate)(affine_zero_candidate_encoder_bounds candidate)).
  destruct accepted.
  - destruct(readonly_sound CONDITION _ _ _ DOMAIN(conj RUN eq_refl))as [_ SOUND].
    destruct(SOUND eq_refl)as [READY [STABLE [NONALIAS RANGES]]].
    assert(CACHED:exec_stmt fe ge locals temps memory(snapshot_cached_source site)E0 after final Out_normal).
    { apply affine_zero_snapshot_checked_cached_execution; [exact(proj1 DOMAIN)|exact READY|exact STABLE|exact SOURCE]. }
    destruct(@affine_zero_pointer_candidate_execution(snapshot_cached_source site)package live candidate
      fe ge locals temps memory after final READY NONALIAS RANGES CACHED)as [target [EXECUTE PUBLIC]].
    exists target; split; [eapply decision_fragment_run with(b:=true); [exact RUN|exact EXECUTE]|exact PUBLIC].
  - exists after; split; [eapply decision_fragment_run with(b:=false); [exact RUN|exact SOURCE]|apply temp_agree_refl].
Qed.
End EXECUTION.

Print Assumptions affine_zero_snapshot_candidate_tree_language_independent.

Print Assumptions affine_zero_snapshot_checked_cached_execution.
Print Assumptions affine_zero_snapshot_guarded_candidate_execution.
