From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightGuard ClightNoWrap ClightRedundantSet.
From GuardMemory Require Import GuardMemoryArrayBackend GuardMemoryAffineInnerPointerSyntax
  GuardMemoryAffineInnerPointerSourceDomain GuardMemoryParametricWidth GuardMemoryAffinePointerLoadedDomain
  GuardMemoryAffinePointerLoadedCache GuardMemoryObservationExclusion.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyCompletedCondition
  ReadonlyConditionComposition ClightConditionComposition ClightAffinePreparationEvidence
  ClightAffinePointerGuard ClightAffinePointerSourcePreparation ClightAffineInnerPointerSourceGuard
  ClightReadonlyLoadedTreeSynthesis ClightPreloadSnapshot.
Import ListNotations.
Set Implicit Arguments.

Definition affine_loaded_preparation_evidence source (package : memory_affine_inner_pointer_package source) pointer fe :
  affine_preparation_evidence (affine_inner_pointer_shape package) (affine_inner_pointer_expression package)
    (affine_inner_pointer_row_limit package) (affine_inner_pointer_column_limit package)
    (affine_inner_pointer_body_parameters package) (affine_inner_pointer_scalars package)
    (memory_affine_pointer_loaded_completed package pointer fe).
Proof.
  constructor.
  - exact (@memory_affine_pointer_loaded_header_words source package pointer fe).
  - exact (@memory_affine_pointer_loaded_body_words source package pointer fe).
Defined.

Section CONDITION.
Variable source : statement.
Variable package : memory_affine_inner_pointer_package source.
Variable pointer : ident.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable O : Type.
Variable observe : fragment_observation -> O -> Prop.
Variable width_tree : decision_tree.
Hypothesis WIDTH : compile_memory_source_width (affine_inner_pointer_column_limit package)
  (affine_inner_pointer_row (affine_inner_pointer_shape package))
  (memory_affine_inner_pointer_header (affine_inner_pointer_shape package) (affine_inner_pointer_expression package))
  (affine_inner_pointer_header_bounds (affine_inner_pointer_row_limit package) (affine_inner_pointer_header_limits package))
  (affine_inner_pointer_expression package) = Some width_tree.
Let D := memory_affine_pointer_loaded_completed package pointer fe.
Let E := affine_loaded_preparation_evidence package pointer fe.

Definition affine_loaded_preparation_condition :
  readonly_condition (readonly_clight_host fe observe) D (affine_inner_pointer_ready package)
    (affine_inner_pointer_package_preparation_tree package width_tree).
Proof.
  pose proof (@affine_evidence_preparation_condition source (affine_inner_pointer_shape package)
    (affine_inner_pointer_expression package) (affine_inner_pointer_encoded package)
    (affine_inner_pointer_row_limit package) (affine_inner_pointer_column_limit package)
    (affine_inner_pointer_header_limits package) (affine_inner_pointer_body_limits package)
    (affine_inner_pointer_body_parameters package) (affine_inner_pointer_pointers package)
    (affine_inner_pointer_scalars package) (affine_inner_pointer_extent package) (affine_inner_pointer_operations package)
    (affine_inner_pointer_syntax package) fe O observe D E width_tree WIDTH) as PREP.
  apply readonly_completed_tree_condition.
  - intros entry DOMAIN; destruct (readonly_available PREP entry DOMAIN) as [answer [checked [RUN SAME]]].
    exists answer; exact RUN.
  - intros entry DOMAIN RUN.
    destruct (@affine_evidence_preparation_ranges source (affine_inner_pointer_shape package)
      (affine_inner_pointer_expression package) (affine_inner_pointer_encoded package)
      (affine_inner_pointer_row_limit package) (affine_inner_pointer_column_limit package)
      (affine_inner_pointer_header_limits package) (affine_inner_pointer_body_limits package)
      (affine_inner_pointer_body_parameters package) (affine_inner_pointer_pointers package)
      (affine_inner_pointer_scalars package) (affine_inner_pointer_extent package) (affine_inner_pointer_operations package)
      (affine_inner_pointer_syntax package) fe O observe D E width_tree WIDTH entry DOMAIN RUN)
      as [HEADER [LIMIT [RANGES VIEW]]].
    constructor; assumption.
Defined.
End CONDITION.

Theorem affine_loaded_prepared_cached_domain source (package : memory_affine_inner_pointer_package source)
  pointer fe entry :
  In pointer (affine_inner_pointer_pointers package) ->
  memory_writes_exclude_cell
    (memory_affine_inner_pointer_limits (affine_inner_pointer_row_limit package) (affine_inner_pointer_column_limit package)
      (affine_inner_pointer_header_limits package) (affine_inner_pointer_body_limits package))
    (affine_inner_pointer_extent package) pointer 0%Z (affine_inner_pointer_operations package) = true ->
  memory_affine_pointer_loaded_completed package pointer fe entry -> affine_inner_pointer_ready package entry ->
  affine_inner_pointer_observed_completed package fe entry.
Proof.
  intros MEMBER EXCLUDED [DOMAIN [after [final SOURCE]]] READY.
  destruct entry as [ge locals temps memory].
  split.
  - exists after,final; rewrite <- (affine_inner_pointer_source_exact (affine_inner_pointer_syntax package)).
    eapply memory_affine_pointer_loaded_cache_under_ranges;
      [exact MEMBER|exact EXCLUDED|exact DOMAIN|exact (affine_inner_pointer_ready_header READY)|
       exact (affine_inner_pointer_ready_width READY)|exact (affine_inner_pointer_ready_ranges READY)|
       exact (affine_inner_pointer_ready_view READY)|exact SOURCE].
  - exact (proj2 (proj2 DOMAIN)).
Qed.

Print Assumptions affine_loaded_preparation_evidence.
Print Assumptions affine_loaded_preparation_condition.
Print Assumptions affine_loaded_prepared_cached_domain.
