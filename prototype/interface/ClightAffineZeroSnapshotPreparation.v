From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightPureExpr ClightGuard ClightNoWrap.
From GuardMemory Require Import GuardMemoryArrayBackend GuardMemoryParametricGuard
  GuardMemoryParametricSourceDomain GuardMemoryAffineInnerPointerSyntax
  GuardMemoryAffineInnerPointerSourceDomain GuardMemoryAffineInnerPointerRegionSource.
From GuardInterface Require Import GuardedRewrite ReadonlyConditionComposition ReadonlyBranching
  ClightConditionComposition ClightReadonlyBranching ClightReadonlyRewrite ClightReadonlyCompletedCondition
  ClightReadonlyLoadedTreeSynthesis
  ClightAffinePreparationEvidence ClightAffineDomainFacts ClightAffineSnapshotSyntax
  ClightAffineSnapshotSourceInputs ClightAffineSnapshotPreparation ClightAffineSnapshotReachedCondition
  ClightFirstReachedWidth ClightAffineZeroSnapshotReady ClightAffinePointerGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Original entry receipts license header checks. Two sufficient first-reached
    conditions produce the same ready fact; refusal of the first supplies no
    negation. Both alternatives are safe in the same checked header domain. *)
Section PREPARATION.
Variable original : statement.
Variable site : affine_snapshot_source_package original.
Let package:=snapshot_cached_package site.
Let shape:=affine_inner_pointer_shape package.
Let row:=affine_inner_pointer_row shape.
Let header:=memory_affine_inner_pointer_header shape(affine_inner_pointer_expression package).
Definition affine_zero_snapshot_header_bounds:=affine_inner_pointer_header_bounds
  (affine_inner_pointer_row_limit package)(affine_inner_pointer_header_limits package).
Variables first later : decision_tree.
Hypothesis FIRST : compile_first_reached_width 0(affine_inner_pointer_column_limit package)0 row
  header affine_zero_snapshot_header_bounds(affine_inner_pointer_expression package)=Some first.
Hypothesis LATER : compile_first_reached_width 0(affine_inner_pointer_column_limit package)1 row
  header affine_zero_snapshot_header_bounds(affine_inner_pointer_expression package)=Some later.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable O : Type.
Variable observe : fragment_observation -> O -> Prop.
Let H:=readonly_clight_host fe observe.
Let D:=affine_snapshot_original_domain package(snapshot_root site)(snapshot_child site)
  (snapshot_child_cache site)(snapshot_original_header site)fe.
Let EVIDENCE:=@affine_snapshot_preparation_evidence(snapshot_cached_source site)package
  (snapshot_root site)(snapshot_child site)(snapshot_child_cache site)(snapshot_original_header site)
  (snapshot_header_word site)(snapshot_cached_body_exact site)fe.
Let HEAD entry:=memory_affine_inner_pointer_header_accept shape(affine_inner_pointer_row_limit package)entry=true.
Let RANGE entry:=MemoryNested.A.env_within affine_zero_snapshot_header_bounds
  (memory_source_parameter_values header entry).
Let READY:=affine_domain_ready package.
Definition affine_zero_snapshot_header_tree:=decision_bind
  (affine_inner_pointer_header_tree shape(affine_inner_pointer_row_limit package))
  (MemorySourceRanges.range_guard header affine_zero_snapshot_header_bounds)(Decision false).
Definition affine_zero_snapshot_alternative_tree:=decision_bind(affine_zero_preparation_tree site first)
  (Decision true)(affine_zero_preparation_tree site later).
Definition affine_zero_snapshot_preparation_tree:=decision_bind affine_zero_snapshot_header_tree
  affine_zero_snapshot_alternative_tree(Decision false).

Definition affine_zero_snapshot_head_condition : readonly_condition H D HEAD
  (affine_inner_pointer_header_tree shape(affine_inner_pointer_row_limit package)).
Proof.
  apply readonly_completed_tree_condition.
  - intros entry DOMAIN; eexists; eapply affine_evidence_header_tree_run; [exact EVIDENCE|exact DOMAIN].
  - intros entry DOMAIN RUN; unfold HEAD.
    eapply readonly_decision_determinate; [eapply affine_evidence_header_tree_run; [exact EVIDENCE|exact DOMAIN]|exact RUN].
Defined.
Lemma affine_zero_snapshot_head_view entry : D entry -> HEAD entry ->
  MemoryNested.A.typed_view header(memory_source_parameter_values header entry)(entry_temps entry).
Proof.
  intros DOMAIN ACCEPT; eapply preparation_header_view; [exact EVIDENCE| |exact DOMAIN|exact ACCEPT].
  pose proof(affine_inner_pointer_control_limits(affine_inner_pointer_syntax package))as CAPS;
    inversion CAPS; subst; tauto.
Qed.
Definition affine_zero_snapshot_head_range_condition : readonly_condition H
  (fun entry=>D entry /\ HEAD entry)RANGE(MemorySourceRanges.range_guard header affine_zero_snapshot_header_bounds).
Proof.
  apply readonly_completed_tree_condition.
  - intros entry[DOMAIN ACCEPT]; eapply MemorySourceRanges.range_guard_total; apply affine_zero_snapshot_head_view; assumption.
  - intros entry[DOMAIN ACCEPT]RUN; eapply MemorySourceRanges.range_guard_sound;
      [apply affine_zero_snapshot_head_view; assumption|exact RUN].
Defined.
Definition affine_zero_snapshot_header_condition : readonly_condition H D
  (fun entry=>HEAD entry /\ RANGE entry)affine_zero_snapshot_header_tree.
Proof.
  exact(@sequence_readonly_conditions clight_entry H(clight_readonly_check_algebra fe observe)
    D HEAD RANGE _ _ affine_zero_snapshot_head_condition affine_zero_snapshot_head_range_condition).
Defined.
Definition affine_zero_snapshot_alternative_condition : readonly_condition H
  (fun entry=>D entry /\(HEAD entry /\ RANGE entry))READY affine_zero_snapshot_alternative_tree.
Proof.
  apply(@branch_readonly_conditions clight_entry H(clight_readonly_branch_algebra fe observe)
    (fun entry=>D entry /\(HEAD entry /\ RANGE entry))READY(fun _=>True)READY).
  - apply condition_classifier.
    exact(@affine_zero_preparation_condition original site 0 affine_zero_snapshot_header_bounds first FIRST fe O observe).
  - apply(@readonly_true_condition clight_entry H(clight_readonly_check_algebra fe observe));
      intros entry[DOMAIN READY_FACT]; exact READY_FACT.
  - eapply readonly_condition_restrict.
    + exact(@affine_zero_preparation_condition original site 1 affine_zero_snapshot_header_bounds later LATER fe O observe).
    + intros entry[DOMAIN UNUSED]; exact DOMAIN.
Defined.
Definition affine_zero_snapshot_preparation_condition : readonly_condition H D READY affine_zero_snapshot_preparation_tree.
Proof.
  eapply readonly_condition_entails.
  - exact(@sequence_readonly_conditions clight_entry H(clight_readonly_check_algebra fe observe)
      D(fun entry=>HEAD entry /\ RANGE entry)READY _ _
      affine_zero_snapshot_header_condition affine_zero_snapshot_alternative_condition).
  - intros entry DOMAIN[HEADER READY_FACT]; exact READY_FACT.
Defined.
End PREPARATION.

Print Assumptions affine_zero_snapshot_header_condition.
Print Assumptions affine_zero_snapshot_alternative_condition.
Print Assumptions affine_zero_snapshot_preparation_condition.
