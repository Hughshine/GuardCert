From Stdlib Require Import List Bool.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightGuard ClightRegionProgress
  ClightCountedLoop ClightFrontendLoopProtocol.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryParametricWidth
  GuardMemoryPointerSequence.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightQuietDeterminacy
  ClightStrictLoopProgress ClightAffineHeaderSnapshots ClightAffineSnapshotRows ClightAffineSnapshotSourceInputs
  ClightAffineSnapshotPrefix ClightAffineSnapshotTransport ClightAffineSnapshotSyntax
  ClightAffineSnapshotCandidateCondition ClightAffineInnerPointerSourceGuard ClightAffinePointerGuard
  ClightAffineInnerPointerCandidate ClightSourceObservation.
Set Implicit Arguments.

(** The condition's AST is independent of the execution and observation
    relations used in its proof. The installed statement uses a fixed choice;
    the execution theorem below works with every function-entry relation. *)
Theorem affine_snapshot_candidate_tree_language_independent original
    (site : affine_snapshot_source_package original) fe O
    (observe : fragment_observation -> O -> Prop) other_fe Other
    (other_observe : fragment_observation -> Other -> Prop) width alias validator encoder :
  affine_snapshot_candidate_tree site fe observe width alias validator encoder =
  affine_snapshot_candidate_tree site other_fe other_observe width alias validator encoder.
Proof.
  unfold affine_snapshot_candidate_tree,affine_snapshot_prepare_and_scan_tree; f_equal; f_equal.
  unfold ClightAffineSnapshotScan.affine_snapshot_scan_tree.
  generalize(BinInt.Z.to_nat(affine_inner_pointer_row_limit(snapshot_cached_package site)))as fuel.
  generalize BinNums.Z0 as start; intros start fuel; revert start.
  induction fuel as [|fuel IH]; intro start;
    cbn [ReadonlyPrefixScan.synthesize_prefix_scan
      ReadonlyConditionComposition.constant_check ReadonlyBranching.branch_check
      ClightConditionComposition.clight_readonly_check_algebra ClightReadonlyBranching.clight_readonly_branch_algebra
      ReadonlyPrefixScan.prefix_active_probe ReadonlyPrefixScan.prefix_point_probe ReadonlyPrefixScan.prefix_next
      ClightAffineSnapshotScan.affine_snapshot_scan_spec ClightObservedBodyPrefix.observed_body_prefix_spec];
    [reflexivity|f_equal; f_equal; apply IH].
Qed.

Definition affine_snapshot_installed_tree original(site:affine_snapshot_source_package original)
    width alias validator encoder :=
  affine_snapshot_candidate_tree site(adapter_entry true)(@eq fragment_observation)width alias validator encoder.

Theorem affine_snapshot_checked_source_quiet original(site:affine_snapshot_source_package original) :
  quiet_statement original=true.
Proof.
  rewrite(snapshot_source_exact site).
  unfold affine_snapshot_source,strict_frontend_loop.
  cbn [quiet_statement counter_increment]; rewrite andb_true_r.
  apply affine_setup_child_quiet.
  exact(@memory_pointer_sequence_quiet _ _
    (affine_inner_pointer_body_exact(affine_inner_pointer_syntax(snapshot_cached_package site)))).
Qed.

(** Transport a specific original execution, including its actual exit.
    Quiet determinacy aligns it with the completion used to license the guard;
    cached-source completion is produced here, rather than supplied by users. *)
Theorem affine_snapshot_checked_cached_execution original(site:affine_snapshot_source_package original)
    fe ge locals temps memory after final :
  affine_snapshot_original_domain(snapshot_cached_package site)(snapshot_root site)(snapshot_child site)
    (snapshot_child_cache site)(snapshot_original_header site)fe(Entry ge locals temps memory) ->
  affine_inner_pointer_ready(snapshot_cached_package site)(Entry ge locals temps memory) ->
  affine_snapshot_point_preservation(snapshot_cached_package site)(snapshot_root site)(snapshot_child site)
    (snapshot_child_cache site)(Entry ge locals temps memory) ->
  exec_stmt fe ge locals temps memory original E0 after final Out_normal ->
  exec_stmt fe ge locals temps memory(snapshot_cached_source site)E0 after final Out_normal.
Proof.
  intros DOMAIN READY STABLE SOURCE.
  destruct(@affine_snapshot_original_cached_completion(snapshot_cached_source site)(snapshot_cached_package site)
    (snapshot_root site)(snapshot_child site)(snapshot_child_cache site)(snapshot_original_header site)
    (snapshot_root_protected site)(snapshot_child_protected site)(snapshot_cache_member site)
    (snapshot_header_word site)(snapshot_cached_body_exact site)fe(Entry ge locals temps memory)
    (@affine_snapshot_prepared_entry(snapshot_cached_source site)(snapshot_cached_package site)
      (snapshot_root site)(snapshot_child site)(snapshot_child_cache site)(snapshot_original_header site)
      (snapshot_root_protected site)(snapshot_child_protected site)fe(Entry ge locals temps memory)DOMAIN READY)
    STABLE DOMAIN)as [other_after [other_final [ORIGINAL CACHED]]].
  rewrite <-snapshot_source_exact in ORIGINAL.
  destruct(@quiet_execution_determinate fe ge locals temps memory original E0 other_after other_final Out_normal
    ORIGINAL(affine_snapshot_checked_source_quiet site)E0 after final Out_normal SOURCE)
    as [_ [TEMPS [MEMORY OUTCOME]]]; subst other_after other_final.
  rewrite(affine_inner_pointer_source_exact(affine_inner_pointer_syntax(snapshot_cached_package site))).
  exact CACHED.
Qed.

Section EXECUTION.
Variable original : statement.
Variable site : affine_snapshot_source_package original.
Let package := snapshot_cached_package site.
Variable live : list ident.
Variable candidate : affine_inner_pointer_candidate_package package live.
Variables width alias : decision_tree.
Hypothesis WIDTH : compile_memory_source_width(affine_inner_pointer_column_limit package)
  (affine_inner_pointer_row(affine_inner_pointer_shape package))
  (memory_affine_inner_pointer_header(affine_inner_pointer_shape package)(affine_inner_pointer_expression package))
  (affine_inner_pointer_header_bounds(affine_inner_pointer_row_limit package)(affine_inner_pointer_header_limits package))
  (affine_inner_pointer_expression package)=Some width.
Hypothesis ALIAS : compile_affine_inner_pointer_package_envelopes package=Some alias.
Definition affine_snapshot_guarded_candidate := tree_statement
  (affine_snapshot_installed_tree site width alias
    (affine_inner_candidate_validator_bounds candidate)(affine_inner_candidate_encoder_bounds candidate))
  (affine_inner_pointer_candidate_statement candidate)original.

Theorem affine_snapshot_guarded_candidate_execution fe ge locals temps memory after final :
  affine_snapshot_candidate_domain site fe(Entry ge locals temps memory) ->
  exec_stmt fe ge locals temps memory original E0 after final Out_normal ->
  exists target,exec_stmt fe ge locals temps memory affine_snapshot_guarded_candidate E0 target final Out_normal /\
    temp_agree live after target.
Proof.
  intros DOMAIN SOURCE.
  pose proof(@affine_snapshot_candidate_condition original site fe fragment_observation(@eq fragment_observation)
    width alias(affine_inner_candidate_validator_bounds candidate)(affine_inner_candidate_encoder_bounds candidate)
    WIDTH ALIAS)as CONDITION.
  destruct(readonly_available CONDITION _ DOMAIN)as [accepted [checked [RUN SAME]]]; subst checked.
  unfold affine_snapshot_guarded_candidate,affine_snapshot_installed_tree.
  rewrite(@affine_snapshot_candidate_tree_language_independent original site(adapter_entry true)
    fragment_observation(@eq fragment_observation)fe fragment_observation(@eq fragment_observation)
    width alias(affine_inner_candidate_validator_bounds candidate)(affine_inner_candidate_encoder_bounds candidate)).
  destruct accepted.
  - destruct(readonly_sound CONDITION _ _ _ DOMAIN(conj RUN eq_refl))as [_ SOUND].
    destruct(SOUND eq_refl)as [READY [STABLE [NONALIAS RANGES]]].
    assert(CACHED:exec_stmt fe ge locals temps memory(snapshot_cached_source site)E0 after final Out_normal).
    { apply affine_snapshot_checked_cached_execution; [exact(proj1 DOMAIN)|exact READY|exact STABLE|exact SOURCE]. }
    destruct(@affine_inner_pointer_candidate_execution(snapshot_cached_source site)package live candidate
      fe ge locals temps memory after final READY NONALIAS RANGES CACHED)as [target [EXECUTE PUBLIC]].
    exists target; split; [eapply decision_fragment_run with(b:=true); [exact RUN|exact EXECUTE]|exact PUBLIC].
  - exists after; split; [eapply decision_fragment_run with(b:=false); [exact RUN|exact SOURCE]|apply temp_agree_refl].
Qed.
End EXECUTION.

Print Assumptions affine_snapshot_candidate_tree_language_independent.
Print Assumptions affine_snapshot_checked_source_quiet.
Print Assumptions affine_snapshot_checked_cached_execution.
Print Assumptions affine_snapshot_guarded_candidate_execution.
