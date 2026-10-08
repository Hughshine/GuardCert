From Stdlib Require Import List Bool ZArith.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightPureExpr.
From GuardMemory Require Import GuardMemoryArrayBackend GuardMemoryPointerBackend GuardMemoryParametricGuard
  GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineInnerPointerSourceDomain
  GuardMemoryAffineInnerPointerRegionSource.
From GuardInterface Require Import GuardedRewrite ReadonlyConditionComposition
  ClightConditionComposition ClightReadonlyRewrite ClightReadonlyCompletedCondition
  ClightAffineDomainFacts ClightAffineInnerPointerSourceGuard ClightAffineInnerPointerCandidateGuard
  ClightAffinePointerGuard ClightSourceObservation ClightAffineSnapshotSyntax
  ClightAffineSnapshotSourceInputs ClightAffineSnapshotTransport ClightAffineZeroSnapshotScan
  ClightAffineZeroSnapshotPreparation ClightFirstReachedWidth ClightAffineZeroPointerGuard.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section CONDITION.
Variable original : statement.
Variable site : affine_snapshot_source_package original.
Let package:=snapshot_cached_package site.
Let shape:=affine_inner_pointer_shape package.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable O : Type.
Variable observe : fragment_observation -> O -> Prop.
Variables first later alias : decision_tree.
Variable validator_bounds : list MemoryNested.A.interval.
Variable encoder_bounds : list MemoryFramedNested.N.A.interval.
Hypothesis FIRST : compile_first_reached_width 0(affine_inner_pointer_column_limit package)0
  (affine_inner_pointer_row shape)(memory_affine_inner_pointer_header shape(affine_inner_pointer_expression package))
  (affine_zero_snapshot_header_bounds site)(affine_inner_pointer_expression package)=Some first.
Hypothesis LATER : compile_first_reached_width 0(affine_inner_pointer_column_limit package)1
  (affine_inner_pointer_row shape)(memory_affine_inner_pointer_header shape(affine_inner_pointer_expression package))
  (affine_zero_snapshot_header_bounds site)(affine_inner_pointer_expression package)=Some later.
Hypothesis ALIAS : compile_affine_inner_pointer_package_envelopes package=Some alias.
Let H:=readonly_clight_host fe observe.
Definition affine_zero_snapshot_candidate_domain entry:=
  affine_snapshot_original_domain package(snapshot_root site)(snapshot_child site)
    (snapshot_child_cache site)(snapshot_original_header site)fe entry /\
  observed_pointer_domain(affine_inner_pointer_pointers package)entry.
Let D:=affine_zero_snapshot_candidate_domain.
Let READY:=affine_domain_ready package.
Let STABLE:=affine_snapshot_point_preservation package(snapshot_root site)(snapshot_child site)(snapshot_child_cache site).
Let NONALIAS:=affine_inner_pointer_source_nonalias package.
Let RANGES:=affine_inner_pointer_candidate_ranges package validator_bounds encoder_bounds.
Let ready_stable entry:=READY entry /\ STABLE entry.
Let prepare:=affine_zero_snapshot_preparation_tree site first later.
Let scan:=@affine_zero_snapshot_scan_tree(snapshot_cached_source site)package(snapshot_root site)
  (snapshot_child site)(snapshot_child_cache site)(snapshot_original_header site)
  (snapshot_root_protected site)(snapshot_child_protected site)(snapshot_cache_member site)
  (snapshot_header_word site)(snapshot_cached_body_exact site)fe O observe.
Definition affine_zero_snapshot_prepare_and_scan_tree:=decision_bind prepare scan(Decision false).
Definition affine_zero_snapshot_candidate_tree:=decision_bind affine_zero_snapshot_prepare_and_scan_tree
  (decision_bind alias(affine_inner_pointer_candidate_ranges_tree package validator_bounds encoder_bounds)(Decision false))
  (Decision false).
Definition affine_zero_snapshot_candidate_facts entry:=
  READY entry /\ STABLE entry /\ NONALIAS entry /\ RANGES entry.

Definition affine_zero_snapshot_candidate_preparation_condition : readonly_condition H D READY prepare.
Proof.
  eapply readonly_condition_restrict.
  - exact(@affine_zero_snapshot_preparation_condition original site first later FIRST LATER fe O observe).
  - intros entry[DOMAIN POINTERS]; exact DOMAIN.
Defined.
Definition affine_zero_snapshot_candidate_scan_condition : readonly_condition H
  (fun entry=>D entry /\ READY entry)STABLE scan.
Proof.
  eapply readonly_condition_restrict.
  - exact(@affine_zero_snapshot_scan_condition(snapshot_cached_source site)package(snapshot_root site)
      (snapshot_child site)(snapshot_child_cache site)(snapshot_original_header site)
      (snapshot_root_protected site)(snapshot_child_protected site)(snapshot_cache_member site)
      (snapshot_header_word site)(snapshot_cached_body_exact site)fe O observe).
  - intros entry[[DOMAIN POINTERS]READY_FACT]; exact(conj DOMAIN READY_FACT).
Defined.
Definition affine_zero_snapshot_prepare_and_scan_condition : readonly_condition H D ready_stable
  affine_zero_snapshot_prepare_and_scan_tree.
Proof.
  exact(@sequence_readonly_conditions clight_entry H(clight_readonly_check_algebra fe observe)
    D READY STABLE prepare scan affine_zero_snapshot_candidate_preparation_condition
    affine_zero_snapshot_candidate_scan_condition).
Defined.
Let prepared_domain entry:=D entry /\ ready_stable entry.
Definition affine_zero_snapshot_candidate_alias_condition : readonly_condition H prepared_domain NONALIAS alias.
Proof.
  eapply readonly_condition_restrict.
  - exact(@affine_zero_pointer_alias_condition(snapshot_cached_source site)package fe O observe alias ALIAS).
  - intros entry[[DOMAIN POINTERS][READY_FACT STABILITY]]; exact(conj POINTERS READY_FACT).
Defined.
Definition affine_zero_snapshot_candidate_validator_condition : readonly_condition H
  (fun entry=>prepared_domain entry /\ NONALIAS entry)
  (fun entry=>MemoryNested.A.env_within validator_bounds
    (memory_source_parameter_values(memory_affine_inner_pointer_region_context package)entry))
  (MemorySourceRanges.range_guard(memory_affine_inner_pointer_region_context package)validator_bounds).
Proof.
  apply readonly_completed_tree_condition.
  - intros entry[[DOMAIN[READY_FACT STABILITY]]SEPARATED]; eapply MemorySourceRanges.range_guard_total;
      exact(affine_domain_ready_view READY_FACT).
  - intros entry[[DOMAIN[READY_FACT STABILITY]]SEPARATED]RUN; eapply MemorySourceRanges.range_guard_sound;
      [exact(affine_domain_ready_view READY_FACT)|exact RUN].
Defined.
Definition affine_zero_snapshot_candidate_encoder_condition : readonly_condition H
  (fun entry=>(prepared_domain entry /\ NONALIAS entry) /\
    MemoryNested.A.env_within validator_bounds(memory_source_parameter_values(memory_affine_inner_pointer_region_context package)entry))
  (fun entry=>MemoryFramedNested.N.A.env_within encoder_bounds
    (memory_source_parameter_values(memory_affine_inner_pointer_region_context package)entry))
  (MemoryFramedNested.N.G.range_guard(memory_affine_inner_pointer_region_context package)encoder_bounds).
Proof.
  apply readonly_completed_tree_condition.
  - intros entry[[[DOMAIN[READY_FACT STABILITY]]SEPARATED]WITHIN]; eapply MemoryFramedNested.N.G.range_guard_total;
      exact(affine_domain_ready_view READY_FACT).
  - intros entry[[[DOMAIN[READY_FACT STABILITY]]SEPARATED]WITHIN]RUN; eapply MemoryFramedNested.N.G.range_guard_sound;
      [exact(affine_domain_ready_view READY_FACT)|exact RUN].
Defined.
Definition affine_zero_snapshot_candidate_ranges_condition : readonly_condition H
  (fun entry=>prepared_domain entry /\ NONALIAS entry)RANGES
  (affine_inner_pointer_candidate_ranges_tree package validator_bounds encoder_bounds).
Proof.
  exact(@sequence_readonly_conditions clight_entry H(clight_readonly_check_algebra fe observe)
    (fun entry=>prepared_domain entry /\ NONALIAS entry)_ _ _ _
    affine_zero_snapshot_candidate_validator_condition affine_zero_snapshot_candidate_encoder_condition).
Defined.
Definition affine_zero_snapshot_candidate_condition : readonly_condition H D
  affine_zero_snapshot_candidate_facts affine_zero_snapshot_candidate_tree.
Proof.
  eapply readonly_condition_entails.
  - exact(@sequence_readonly_conditions clight_entry H(clight_readonly_check_algebra fe observe)
      D ready_stable(fun entry=>NONALIAS entry /\ RANGES entry)_ _
      affine_zero_snapshot_prepare_and_scan_condition
      (@sequence_readonly_conditions clight_entry H(clight_readonly_check_algebra fe observe)
        prepared_domain NONALIAS RANGES _ _ affine_zero_snapshot_candidate_alias_condition
        affine_zero_snapshot_candidate_ranges_condition)).
  - intros entry DOMAIN[[READY_FACT STABILITY][SEPARATED WITHIN]];
      exact(conj READY_FACT(conj STABILITY(conj SEPARATED WITHIN))).
Defined.
End CONDITION.

Print Assumptions affine_zero_snapshot_candidate_preparation_condition.
Print Assumptions affine_zero_snapshot_candidate_scan_condition.
Print Assumptions affine_zero_snapshot_candidate_alias_condition.
Print Assumptions affine_zero_snapshot_candidate_ranges_condition.
Print Assumptions affine_zero_snapshot_candidate_condition.
