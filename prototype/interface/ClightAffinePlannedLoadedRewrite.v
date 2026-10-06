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
  ClightAffineDynamicLoadedRewrite.
Import ListNotations.
Set Implicit Arguments.

Section REWRITE.
Variable source : statement.
Variable package : memory_affine_inner_pointer_package source.
Variable pointer : ident.
Hypothesis FRESH : pointer <> affine_inner_pointer_row (affine_inner_pointer_shape package) /\
  pointer <> affine_inner_pointer_column (affine_inner_pointer_shape package) /\
  pointer <> affine_inner_pointer_inner_bound (affine_inner_pointer_shape package).
Variable live : list ident.
Variable candidate : affine_inner_pointer_candidate_package package live.
Variables width alias : decision_tree.
Hypothesis WIDTH : compile_memory_source_width (affine_inner_pointer_column_limit package)
  (affine_inner_pointer_row (affine_inner_pointer_shape package))
  (memory_affine_inner_pointer_header (affine_inner_pointer_shape package) (affine_inner_pointer_expression package))
  (affine_inner_pointer_header_bounds (affine_inner_pointer_row_limit package) (affine_inner_pointer_header_limits package))
  (affine_inner_pointer_expression package) = Some width.
Hypothesis ALIAS : compile_affine_inner_pointer_package_envelopes package = Some alias.
Let plan := affine_loaded_complete_plan package pointer width alias
  (affine_inner_candidate_validator_bounds candidate) (affine_inner_candidate_encoder_bounds candidate).
Let yes := affine_inner_pointer_candidate_statement candidate.
Let no := memory_affine_pointer_loaded_source package pointer.
Variable result : ident.
Hypotheses (YES : check_plan_frameable yes = true) (NO : check_plan_frameable no = true).
Hypothesis PRIVATE : ~ In result (check_plan_reads plan++statement_temps yes++statement_temps no++live).

Definition affine_planned_loaded_guarded_candidate := check_plan_guarded_statement plan result yes no.

(** Reuse the complete original condition and candidate proof. The only new
    obligation is the language implementation and its private public frame;
    neither the semantic premise nor candidate certificate changes. *)
Theorem affine_planned_loaded_guarded_candidate_execution fe ge locals temps memory after final :
  loaded_preload_domain (affine_inner_pointer_row (affine_inner_pointer_shape package))
    (affine_inner_pointer_bound (affine_inner_pointer_shape package)) pointer (affine_inner_pointer_pointers package)
    (Entry ge locals temps memory) ->
  exec_stmt fe ge locals temps memory no E0 after final Out_normal ->
  exists target, exec_stmt fe ge locals temps memory affine_planned_loaded_guarded_candidate E0 target final Out_normal /\
    temp_agree live after target.
Proof.
  intros DOMAIN SOURCE.
  destruct (@affine_dynamic_loaded_guarded_candidate_execution source package pointer FRESH live candidate
    width alias WIDTH ALIAS fe ge locals temps memory after final DOMAIN SOURCE) as [old [RUN PUBLIC]].
  unfold affine_dynamic_loaded_guarded_candidate in RUN.
  unfold affine_inner_pointer_package_candidate_guard in RUN.
  rewrite <- affine_loaded_complete_plan_tree in RUN; fold plan in RUN.
  change (clight_fragment_run fe (tree_statement (check_plan_tree plan) yes no)
    (Entry ge locals temps memory) (FragmentObservation E0 old final Out_normal)) in RUN.
  destruct (proj1 (@readonly_tree_execution_exact fe (check_plan_tree plan) yes no
    (Entry ge locals temps memory) (FragmentObservation E0 old final Out_normal)) RUN)
    as [answer [CHECK BRANCH]].
  destruct (@check_plan_guarded_normal_execution fe ge locals temps memory plan result live yes no
    answer old final CHECK YES NO PRIVATE BRANCH) as [target [EXECUTE FRAME]].
  exists target; split; [exact EXECUTE|eapply temp_agree_trans; eassumption].
Qed.

Theorem affine_planned_loaded_observed_candidate_contract loads :
  NoDup (source_load_targets loads) -> source_observations_check (affine_inner_pointer_pointers package) loads = true ->
  In (affine_inner_pointer_bound (affine_inner_pointer_shape package),pointer) loads ->
  PrivateRegion.projected_region_contract live
    (Ssequence (source_load_prefix loads) no)
    (Ssequence (source_load_prefix loads) affine_planned_loaded_guarded_candidate).
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
    + eapply writes_only_weaken; [intros identifier IN; apply in_or_app; right; exact IN|apply affine_loaded_source_writes].
  - intros; eapply source_preload_loaded_domain;
      [exact UNIQUE|exact OBSERVED|exact RECEIPT|eassumption|eassumption].
  - intros temps p locals entry memory after final SCOPE DOMAIN SOURCE.
    destruct (@affine_planned_loaded_guarded_candidate_execution (adapter_entry temps) (globalenv p) locals entry memory after final
      DOMAIN SOURCE) as [target [EXECUTE PUBLIC]].
    exists target,final; split; [exact EXECUTE|split; [exact PUBLIC|apply memory_equivalent_refl]].
Qed.
End REWRITE.

Print Assumptions affine_planned_loaded_guarded_candidate_execution.
Print Assumptions affine_planned_loaded_observed_candidate_contract.
