From Stdlib Require Import List Bool.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineInnerPointerSourceDomain
  GuardMemoryAffineInnerPointerRegionSource GuardMemoryParametricWidth GuardMemoryArrayBackend GuardMemoryPointerBackend.
From GuardInterface Require Import GuardInterface GuardedRewrite ReadonlyConditionComposition
  ClightReadonlyRewrite ClightConditionComposition ClightAffineSnapshotSyntax ClightAffineSnapshotSourceInputs
  ClightAffineSnapshotPreparation ClightAffineSnapshotPrefix ClightAffineSnapshotRows
  ClightAffineSnapshotScan ClightAffineSnapshotTransport ClightAffineInnerPointerSourceGuard
  ClightAffineInnerPointerCandidateGuard ClightSourceObservation ClightAffinePointerSourcePreparation ClightAffinePointerGuard.
Set Implicit Arguments.

(** The checked source adapter supplies static obligations. Original-source
    facts license preparation and stability; their accepted facts produce the
    cached completion required by the existing alias/candidate-range service. *)
Section CONDITION.
Variable original : statement.
Variable site : affine_snapshot_source_package original.
Let source := snapshot_cached_source site.
Let package := snapshot_cached_package site.
Let root := snapshot_root site.
Let child := snapshot_child site.
Let child_cache := snapshot_child_cache site.
Let header := snapshot_original_header site.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable O : Type.
Variable observe : fragment_observation -> O -> Prop.
Variables width alias : decision_tree.
Variable validator_bounds : list MemoryNested.A.interval.
Variable encoder_bounds : list MemoryFramedNested.N.A.interval.
Hypothesis WIDTH : compile_memory_source_width(affine_inner_pointer_column_limit package)
  (affine_inner_pointer_row(affine_inner_pointer_shape package))
  (memory_affine_inner_pointer_header(affine_inner_pointer_shape package)(affine_inner_pointer_expression package))
  (affine_inner_pointer_header_bounds(affine_inner_pointer_row_limit package)(affine_inner_pointer_header_limits package))
  (affine_inner_pointer_expression package)=Some width.
Hypothesis ALIAS : compile_affine_inner_pointer_package_envelopes package=Some alias.
Let H := readonly_clight_host fe observe.
Definition affine_snapshot_candidate_domain entry :=
  affine_snapshot_original_domain package root child child_cache header fe entry /\
  observed_pointer_domain(affine_inner_pointer_pointers package)entry.
Let READY := affine_inner_pointer_ready package.
Let STABLE := affine_snapshot_point_preservation package root child child_cache.
Let LEGACY entry := (READY entry /\ affine_inner_pointer_source_nonalias package entry) /\
  affine_inner_pointer_candidate_ranges package validator_bounds encoder_bounds entry.
Let prepare := affine_inner_pointer_package_preparation_tree package width.
Let scan := @affine_snapshot_scan_tree source package root child child_cache header
  (snapshot_root_protected site)(snapshot_child_protected site)(snapshot_cache_member site)
  (snapshot_header_word site)(snapshot_cached_body_exact site)fe O observe.
Let legacy := affine_inner_pointer_candidate_guard_tree package width alias validator_bounds encoder_bounds.
Definition affine_snapshot_prepare_and_scan_tree := decision_bind prepare scan(Decision false).
Definition affine_snapshot_candidate_tree := decision_bind affine_snapshot_prepare_and_scan_tree legacy(Decision false).
Definition affine_snapshot_candidate_facts entry := READY entry /\ STABLE entry /\
  affine_inner_pointer_source_nonalias package entry /\
  affine_inner_pointer_candidate_ranges package validator_bounds encoder_bounds entry.

Definition affine_snapshot_candidate_preparation_condition : readonly_condition H
  affine_snapshot_candidate_domain READY prepare.
Proof.
  eapply readonly_condition_restrict.
  - exact(@affine_snapshot_preparation_condition source package root child child_cache header
      (snapshot_header_word site)(snapshot_cached_body_exact site)fe O observe width WIDTH).
  - intros entry [DOMAIN OBSERVED]; exact DOMAIN.
Defined.

Definition affine_snapshot_candidate_scan_condition : readonly_condition H
  (fun entry=>affine_snapshot_candidate_domain entry /\ READY entry)STABLE scan.
Proof.
  eapply readonly_condition_restrict.
  - exact(@affine_snapshot_scan_condition source package root child child_cache header
      (snapshot_root_protected site)(snapshot_child_protected site)(snapshot_cache_member site)
      (snapshot_header_word site)(snapshot_cached_body_exact site)fe O observe).
  - intros entry [[DOMAIN OBSERVED]READY_FACT]; split; assumption.
Defined.

Definition affine_snapshot_prepare_and_scan_condition : readonly_condition H
  affine_snapshot_candidate_domain(fun entry=>READY entry /\ STABLE entry)affine_snapshot_prepare_and_scan_tree.
Proof.
  exact(@sequence_readonly_conditions clight_entry H(clight_readonly_check_algebra fe observe)
    affine_snapshot_candidate_domain READY STABLE prepare scan
    affine_snapshot_candidate_preparation_condition affine_snapshot_candidate_scan_condition).
Defined.

Theorem affine_snapshot_prepared_observed_cached_completion entry :
  affine_snapshot_candidate_domain entry -> READY entry -> STABLE entry ->
  affine_inner_pointer_observed_completed package fe entry.
Proof.
  intros [DOMAIN OBSERVED]READY_FACT STABILITY.
  destruct(@affine_snapshot_original_cached_completion source package root child child_cache header
    (snapshot_root_protected site)(snapshot_child_protected site)(snapshot_cache_member site)
    (snapshot_header_word site)(snapshot_cached_body_exact site)fe entry
    (@affine_snapshot_prepared_entry source package root child child_cache header
      (snapshot_root_protected site)(snapshot_child_protected site)fe entry DOMAIN READY_FACT)
    STABILITY DOMAIN)as [after [final [ORIGINAL CACHED]]].
  split; [exists after,final; exact CACHED|exact OBSERVED].
Qed.

Definition affine_snapshot_legacy_candidate_condition : readonly_condition H
  (fun entry=>affine_snapshot_candidate_domain entry /\(READY entry /\ STABLE entry))LEGACY legacy.
Proof.
  eapply readonly_condition_restrict.
  - exact(@affine_inner_pointer_candidate_guard_condition source package fe O observe
      width alias validator_bounds encoder_bounds WIDTH ALIAS).
  - intros entry [DOMAIN [READY_FACT STABILITY]]; apply affine_snapshot_prepared_observed_cached_completion; assumption.
Defined.

Definition affine_snapshot_candidate_condition : readonly_condition H
  affine_snapshot_candidate_domain affine_snapshot_candidate_facts affine_snapshot_candidate_tree.
Proof.
  eapply readonly_condition_entails.
  - exact(@sequence_readonly_conditions clight_entry H(clight_readonly_check_algebra fe observe)
      affine_snapshot_candidate_domain(fun entry=>READY entry /\ STABLE entry)LEGACY
      affine_snapshot_prepare_and_scan_tree legacy
      affine_snapshot_prepare_and_scan_condition affine_snapshot_legacy_candidate_condition).
  - intros entry DOMAIN [[READY_FACT STABILITY][[SECOND NONALIAS]RANGES]];
      split; [exact READY_FACT|split; [exact STABILITY|split; assumption]].
Defined.
End CONDITION.

Print Assumptions affine_snapshot_candidate_preparation_condition.
Print Assumptions affine_snapshot_candidate_scan_condition.
Print Assumptions affine_snapshot_prepared_observed_cached_completion.
Print Assumptions affine_snapshot_legacy_candidate_condition.
Print Assumptions affine_snapshot_candidate_condition.
