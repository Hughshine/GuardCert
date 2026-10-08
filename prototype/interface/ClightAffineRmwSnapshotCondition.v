From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightRedundantSet ClightGuard ClightPureExpr.
From GuardMemory Require Import GuardMemoryArrayBackend GuardMemoryPointerBackend
  GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineInnerPointerSourceDomain
  GuardMemoryAffineInnerPointerRegionSource GuardMemoryParametricGuard.
From GuardInterface Require Import GuardedRewrite ReadonlyConditionComposition ReadonlyBranching
  ClightConditionComposition ClightReadonlyBranching ClightReadonlyRewrite ClightReadonlyCompletedCondition
  ClightAffineSnapshotSyntax ClightAffineSnapshotRows ClightAffineSnapshotSourceInputs ClightAffineSnapshotTransport
  ClightAffineSnapshotRowObservation ClightAffineZeroSnapshotPrefix ClightAffineZeroSnapshotPreparation
  ClightAffineZeroSnapshotCandidateCondition ClightAffineZeroSnapshotScan ClightAffineSnapshotCheckPlan
  ClightAffineInnerPointerCandidateGuard ClightAffineInnerPointerSourceGuard ClightAffineZeroPointerGuard
  ClightAffineDomainFacts ClightFirstReachedWidth ClightSourceObservation ClightCheckPlan ClightZeroRmwCondition.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The fixed scan plan defines ordinary code, independent of proof semantics.
    Both branches establish the same actual-row observation guarantee. *)
Definition affine_rmw_snapshot_scan_tree original(site:affine_snapshot_source_package original) :=
  let package:=snapshot_cached_package site in
  check_plan_tree(affine_snapshot_check_scan_plan package(snapshot_root site)(snapshot_child site)
    (Z.to_nat(affine_inner_pointer_row_limit package))0).
Definition affine_rmw_snapshot_stability_tree original(site:affine_snapshot_source_package original)
    (rmw:affine_snapshot_rmw_site site) :=
  decision_bind(zero_rmw_condition(affine_snapshot_rmw_alpha rmw))(Decision true)
    (affine_rmw_snapshot_scan_tree site).

Lemma affine_rmw_snapshot_scan_tree_exact original(site:affine_snapshot_source_package original)
    fe O(observe:fragment_observation->O->Prop) :
  affine_rmw_snapshot_scan_tree site=
  @affine_zero_snapshot_scan_tree(snapshot_cached_source site)(snapshot_cached_package site)
    (snapshot_root site)(snapshot_child site)(snapshot_child_cache site)(snapshot_original_header site)
    (snapshot_root_protected site)(snapshot_child_protected site)(snapshot_cache_member site)
    (snapshot_header_word site)(snapshot_cached_body_exact site)fe O observe.
Proof.
  unfold affine_rmw_snapshot_scan_tree.
  rewrite(affine_snapshot_check_scan_plan_tree site fe observe).
  rewrite(@affine_zero_snapshot_scan_tree_reuses_original(snapshot_cached_source site)(snapshot_cached_package site)
    (snapshot_root site)(snapshot_child site)(snapshot_child_cache site)(snapshot_original_header site)
    (snapshot_root_protected site)(snapshot_child_protected site)(snapshot_cache_member site)
    (snapshot_header_word site)(snapshot_cached_body_exact site)fe O observe).
  reflexivity.
Qed.

Section CONDITION.
Variable original : statement.
Variable site : affine_snapshot_source_package original.
Variable rmw : affine_snapshot_rmw_site site.
Let package:=snapshot_cached_package site.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable O : Type.
Variable observe : fragment_observation -> O -> Prop.
Variables first later alias : decision_tree.
Variable validator_bounds : list MemoryNested.A.interval.
Variable encoder_bounds : list MemoryFramedNested.N.A.interval.
Hypothesis FIRST : compile_first_reached_width 0(affine_inner_pointer_column_limit package)0
  (affine_inner_pointer_row(affine_inner_pointer_shape package))
  (memory_affine_inner_pointer_header(affine_inner_pointer_shape package)(affine_inner_pointer_expression package))
  (affine_zero_snapshot_header_bounds site)(affine_inner_pointer_expression package)=Some first.
Hypothesis LATER : compile_first_reached_width 0(affine_inner_pointer_column_limit package)1
  (affine_inner_pointer_row(affine_inner_pointer_shape package))
  (memory_affine_inner_pointer_header(affine_inner_pointer_shape package)(affine_inner_pointer_expression package))
  (affine_zero_snapshot_header_bounds site)(affine_inner_pointer_expression package)=Some later.
Hypothesis ALIAS : compile_affine_inner_pointer_package_envelopes package=Some alias.
Let H:=readonly_clight_host fe observe.
Let D:=affine_zero_snapshot_candidate_domain site fe.
Let READY:=affine_domain_ready package.
Let ROWS:=affine_snapshot_row_observation_preservation package(snapshot_root site)(snapshot_child site)
  (snapshot_child_cache site)(snapshot_original_header site)fe.
Let NONALIAS:=affine_inner_pointer_source_nonalias package.
Let RANGES:=affine_inner_pointer_candidate_ranges package validator_bounds encoder_bounds.
Let ready_rows entry:=READY entry /\ ROWS entry.
Let prepare:=affine_zero_snapshot_preparation_tree site first later.
Definition affine_rmw_snapshot_prepare_and_stability_tree:=decision_bind prepare
  (affine_rmw_snapshot_stability_tree rmw)(Decision false).
Definition affine_rmw_snapshot_candidate_tree:=decision_bind affine_rmw_snapshot_prepare_and_stability_tree
  (decision_bind alias(affine_inner_pointer_candidate_ranges_tree package validator_bounds encoder_bounds)(Decision false))
  (Decision false).
Definition affine_rmw_snapshot_candidate_facts entry:=
  READY entry /\ ROWS entry /\ NONALIAS entry /\ RANGES entry.

Definition affine_rmw_snapshot_alpha_condition : readonly_condition H
  (fun entry=>D entry /\ READY entry)
  (fun entry=>(entry_temps entry)!(affine_snapshot_rmw_alpha rmw)=Some(Vint Int.zero))
  (zero_rmw_condition(affine_snapshot_rmw_alpha rmw)).
Proof.
  apply readonly_completed_tree_condition.
  - intros entry[DOMAIN READY_FACT]; apply zero_rmw_condition_available.
    eexists; exact(@affine_domain_words(snapshot_cached_source site)package entry READY_FACT
      (affine_snapshot_rmw_alpha rmw)(affine_snapshot_rmw_context rmw)).
  - intros entry[DOMAIN READY_FACT]RUN; eapply zero_rmw_condition_accept; [|exact RUN].
    eexists; exact(@affine_domain_words(snapshot_cached_source site)package entry READY_FACT
      (affine_snapshot_rmw_alpha rmw)(affine_snapshot_rmw_context rmw)).
Defined.

Definition affine_rmw_snapshot_scan_condition : readonly_condition H
  (fun entry=>D entry /\ READY entry)ROWS(affine_rmw_snapshot_scan_tree site).
Proof.
  eapply readonly_condition_entails.
  - rewrite(affine_rmw_snapshot_scan_tree_exact site fe observe).
    exact(@affine_zero_snapshot_candidate_scan_condition original site fe O observe).
  - intros entry[[DOMAIN POINTERS]READY_FACT]PRESERVES.
    apply affine_snapshot_separated_row_preservation; [|exact PRESERVES].
    exact(@affine_zero_snapshot_prepared_entry(snapshot_cached_source site)package(snapshot_root site)
      (snapshot_child site)(snapshot_child_cache site)(snapshot_original_header site)
      (snapshot_root_protected site)(snapshot_child_protected site)fe entry DOMAIN READY_FACT).
Defined.

Definition affine_rmw_snapshot_stability_condition : readonly_condition H
  (fun entry=>D entry /\ READY entry)ROWS(affine_rmw_snapshot_stability_tree rmw).
Proof.
  apply(@branch_readonly_conditions clight_entry H(clight_readonly_branch_algebra fe observe)
    (fun entry=>D entry /\ READY entry)
    (fun entry=>(entry_temps entry)!(affine_snapshot_rmw_alpha rmw)=Some(Vint Int.zero))
    (fun _=>True)ROWS).
  - apply condition_classifier; exact affine_rmw_snapshot_alpha_condition.
  - apply(@readonly_true_condition clight_entry H(clight_readonly_check_algebra fe observe)).
    intros entry[DOMAIN ZERO]; exact(@affine_snapshot_zero_rmw_row_preservation original site rmw fe entry ZERO).
  - eapply readonly_condition_restrict; [exact affine_rmw_snapshot_scan_condition|].
    intros entry[DOMAIN UNUSED]; exact DOMAIN.
Defined.

Definition affine_rmw_snapshot_prepare_and_stability_condition : readonly_condition H D ready_rows
  affine_rmw_snapshot_prepare_and_stability_tree.
Proof.
  exact(@sequence_readonly_conditions clight_entry H(clight_readonly_check_algebra fe observe)
    D READY ROWS prepare(affine_rmw_snapshot_stability_tree rmw)
    (@affine_zero_snapshot_candidate_preparation_condition original site fe O observe first later FIRST LATER)
    affine_rmw_snapshot_stability_condition).
Defined.
Let prepared_domain entry:=D entry /\ ready_rows entry.
Definition affine_rmw_snapshot_alias_condition : readonly_condition H prepared_domain NONALIAS alias.
Proof.
  eapply readonly_condition_restrict.
  - exact(@affine_zero_pointer_alias_condition(snapshot_cached_source site)package fe O observe alias ALIAS).
  - intros entry[[DOMAIN POINTERS][READY_FACT ROWS_FACT]]; exact(conj POINTERS READY_FACT).
Defined.
Definition affine_rmw_snapshot_validator_condition : readonly_condition H
  (fun entry=>prepared_domain entry /\ NONALIAS entry)
  (fun entry=>MemoryNested.A.env_within validator_bounds
    (memory_source_parameter_values(memory_affine_inner_pointer_region_context package)entry))
  (MemorySourceRanges.range_guard(memory_affine_inner_pointer_region_context package)validator_bounds).
Proof.
  apply readonly_completed_tree_condition.
  - intros entry[[DOMAIN[READY_FACT ROWS_FACT]]SEPARATED]; eapply MemorySourceRanges.range_guard_total;
      exact(affine_domain_ready_view READY_FACT).
  - intros entry[[DOMAIN[READY_FACT ROWS_FACT]]SEPARATED]RUN; eapply MemorySourceRanges.range_guard_sound;
      [exact(affine_domain_ready_view READY_FACT)|exact RUN].
Defined.
Definition affine_rmw_snapshot_encoder_condition : readonly_condition H
  (fun entry=>(prepared_domain entry /\ NONALIAS entry) /\
    MemoryNested.A.env_within validator_bounds(memory_source_parameter_values(memory_affine_inner_pointer_region_context package)entry))
  (fun entry=>MemoryFramedNested.N.A.env_within encoder_bounds
    (memory_source_parameter_values(memory_affine_inner_pointer_region_context package)entry))
  (MemoryFramedNested.N.G.range_guard(memory_affine_inner_pointer_region_context package)encoder_bounds).
Proof.
  apply readonly_completed_tree_condition.
  - intros entry[[[DOMAIN[READY_FACT ROWS_FACT]]SEPARATED]WITHIN]; eapply MemoryFramedNested.N.G.range_guard_total;
      exact(affine_domain_ready_view READY_FACT).
  - intros entry[[[DOMAIN[READY_FACT ROWS_FACT]]SEPARATED]WITHIN]RUN; eapply MemoryFramedNested.N.G.range_guard_sound;
      [exact(affine_domain_ready_view READY_FACT)|exact RUN].
Defined.
Definition affine_rmw_snapshot_ranges_condition : readonly_condition H
  (fun entry=>prepared_domain entry /\ NONALIAS entry)RANGES
  (affine_inner_pointer_candidate_ranges_tree package validator_bounds encoder_bounds).
Proof.
  exact(@sequence_readonly_conditions clight_entry H(clight_readonly_check_algebra fe observe)
    (fun entry=>prepared_domain entry /\ NONALIAS entry)_ _ _ _
    affine_rmw_snapshot_validator_condition affine_rmw_snapshot_encoder_condition).
Defined.
Definition affine_rmw_snapshot_candidate_condition : readonly_condition H D
  affine_rmw_snapshot_candidate_facts affine_rmw_snapshot_candidate_tree.
Proof.
  eapply readonly_condition_entails.
  - exact(@sequence_readonly_conditions clight_entry H(clight_readonly_check_algebra fe observe)
      D ready_rows(fun entry=>NONALIAS entry /\ RANGES entry)_ _
      affine_rmw_snapshot_prepare_and_stability_condition
      (@sequence_readonly_conditions clight_entry H(clight_readonly_check_algebra fe observe)
        prepared_domain NONALIAS RANGES _ _ affine_rmw_snapshot_alias_condition affine_rmw_snapshot_ranges_condition)).
  - intros entry DOMAIN[[READY_FACT ROWS_FACT][SEPARATED WITHIN]];
      exact(conj READY_FACT(conj ROWS_FACT(conj SEPARATED WITHIN))).
Defined.
End CONDITION.

Print Assumptions affine_rmw_snapshot_alpha_condition.
Print Assumptions affine_rmw_snapshot_scan_tree_exact.
Print Assumptions affine_rmw_snapshot_scan_condition.
Print Assumptions affine_rmw_snapshot_stability_condition.
Print Assumptions affine_rmw_snapshot_candidate_condition.
