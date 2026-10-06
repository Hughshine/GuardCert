From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightPureExpr ClightNoWrap ClightCountedLoop ClightRectangularStore.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryArrayBackend GuardMemoryPointerBackend
  GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation GuardMemoryAffineSourceContext
  GuardMemoryAffineSourceLoop GuardMemoryAffineSourceEndpoints GuardMemoryAffineSourceEndpointEncoding
  GuardMemoryParametricGuard GuardMemoryParametricWidth GuardMemoryParametricChecker GuardMemoryParametricSourceDomain
  GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineInnerPointerSourceDomain GuardMemoryAffineInnerPointerRegionSource.
From GuardInterface Require Import GuardedRewrite ReadonlyConditionComposition ClightConditionComposition
  ClightReadonlyRewrite ClightReadonlyCompletedCondition ClightAffinePointerGuard
  ClightAffineInnerPointerSourceGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The legacy candidate checker uses only this stride as the permitted
    affine inner width. This metadata does not change the actual source Loop
    into a rectangle. *)
Definition affine_inner_pointer_candidate_base source (package : memory_affine_inner_pointer_package source) :=
  RectangleShape (affine_inner_pointer_extent package) (affine_inner_pointer_column_limit package) 0 0.

Theorem affine_inner_pointer_ready_width_model source (package : memory_affine_inner_pointer_package source) fe entry :
  memory_affine_inner_pointer_completed fe (affine_inner_pointer_shape package) entry ->
  affine_inner_pointer_ready package entry ->
  memory_source_width_model (affine_inner_pointer_column_limit package)
    (affine_inner_pointer_row (affine_inner_pointer_shape package)) (memory_affine_inner_pointer_region_context package)
    (affine_inner_pointer_expression package)
    (memory_source_parameter_values (memory_affine_inner_pointer_region_context package) entry) = true.
Proof.
  intros DOMAIN READY.
  set (shape := affine_inner_pointer_shape package).
  set (expression := affine_inner_pointer_expression package).
  set (context := memory_affine_inner_pointer_region_context package).
  set (valuation := fun id => Int.signed (temp_word id (entry_temps entry))).
  set (N := valuation (affine_inner_pointer_bound shape)).
  destruct (@memory_affine_inner_pointer_source_header_words source shape expression (affine_inner_pointer_encoded package)
    (affine_inner_pointer_row_limit package) (affine_inner_pointer_column_limit package)
    (affine_inner_pointer_header_limits package) (affine_inner_pointer_body_limits package)
    (affine_inner_pointer_body_parameters package) (affine_inner_pointer_pointers package)
    (affine_inner_pointer_scalars package) (affine_inner_pointer_extent package) (affine_inner_pointer_operations package)
    (affine_inner_pointer_syntax package) fe entry DOMAIN) as [ROW [BOUND WORDS]].
  assert (CAP : signed_range (affine_inner_pointer_row_limit package)).
  { pose proof (affine_inner_pointer_control_limits (affine_inner_pointer_syntax package)) as CAPS;
    inversion CAPS; subst; tauto. }
  pose proof (@memory_affine_inner_pointer_header_sound shape _ entry CAP ROW BOUND
    (affine_inner_pointer_ready_header READY)) as [_ [_ POSITIVE]].
  assert (POS : 0 < N) by exact (proj1 POSITIVE).
  assert (MATH : 0 < memory_source_affine_math (memory_source_set_valuation valuation (affine_inner_pointer_row shape) 0) expression /\
    forall i, 0 <= i < N -> 0 <= memory_source_affine_math (memory_source_set_valuation valuation (affine_inner_pointer_row shape) i) expression <=
      affine_inner_pointer_column_limit package).
  { pose proof (affine_inner_pointer_ready_width READY) as WIDTH.
    unfold memory_affine_inner_pointer_width_property in WIDTH; split.
    - unfold valuation; rewrite <-memory_affine_inner_pointer_word_math; exact (proj1 WIDTH).
    - intros i RANGE; unfold valuation; rewrite <-memory_affine_inner_pointer_word_math.
      apply (proj2 WIDTH); rewrite memory_source_word_temp; exact RANGE. }
  destruct (@memory_source_loop_endpoint_encoding expression (affine_inner_pointer_row shape) context
    (affine_inner_pointer_encoded package) (affine_inner_pointer_full_encoding (affine_inner_pointer_syntax package)) (L.Constant 0))
    as [first FIRST].
  destruct (@memory_source_loop_endpoint_encoding expression (affine_inner_pointer_row shape) context
    (affine_inner_pointer_encoded package) (affine_inner_pointer_full_encoding (affine_inner_pointer_syntax package))
    (L.Sum (L.Var O) (L.Constant (-1)))) as [last LAST].
  change (memory_source_width_model (affine_inner_pointer_column_limit package) (affine_inner_pointer_row shape)
    context expression (map valuation context) = true).
  unfold memory_source_width_model,memory_source_endpoints; rewrite FIRST,LAST.
  unfold memory_source_endpoint_test; cbn [L.eval_test L.eval_expr].
  pose proof (@memory_source_endpoint_value expression (affine_inner_pointer_row shape) context (L.Constant 0) first valuation FIRST) as FIRST_VALUE.
  pose proof (@memory_source_endpoint_value expression (affine_inner_pointer_row shape) context
    (L.Sum (L.Var O) (L.Constant (-1))) last valuation LAST) as LAST_VALUE.
  cbn [L.eval_expr] in FIRST_VALUE,LAST_VALUE.
  change (L.eval_expr (@map positive Z valuation context) last = memory_source_affine_math
    (memory_source_set_valuation valuation (affine_inner_pointer_row shape) (N + -1)) expression) in LAST_VALUE.
  replace (N + -1) with (N-1) in LAST_VALUE by lia.
  change ((1 <=? L.eval_expr (@map positive Z valuation context) first) &&
    ((L.eval_expr (@map positive Z valuation context) first <=? affine_inner_pointer_column_limit package) &&
      ((0 <=? L.eval_expr (@map positive Z valuation context) last) &&
        (L.eval_expr (@map positive Z valuation context) last <=? affine_inner_pointer_column_limit package))) = true).
  rewrite FIRST_VALUE,LAST_VALUE.
  pose proof (proj2 MATH 0 ltac:(lia)) as START.
  pose proof (proj2 MATH (N-1) ltac:(lia)) as END.
  rewrite !andb_true_iff,!Z.leb_le; repeat split; lia.
Qed.

Definition affine_inner_pointer_candidate_ranges_tree source (package : memory_affine_inner_pointer_package source)
  validator_bounds encoder_bounds :=
  decision_bind (MemorySourceRanges.range_guard (memory_affine_inner_pointer_region_context package) validator_bounds)
    (MemoryFramedNested.N.G.range_guard (memory_affine_inner_pointer_region_context package) encoder_bounds) (Decision false).
Definition affine_inner_pointer_candidate_guard_tree source (package : memory_affine_inner_pointer_package source)
  width_tree alias_tree validator_bounds encoder_bounds :=
  decision_bind (affine_inner_pointer_source_guard_tree package width_tree alias_tree)
    (affine_inner_pointer_candidate_ranges_tree package validator_bounds encoder_bounds) (Decision false).
Definition affine_inner_pointer_candidate_ranges source (package : memory_affine_inner_pointer_package source)
  validator_bounds encoder_bounds entry :=
  MemoryNested.A.env_within validator_bounds
    (memory_source_parameter_values (memory_affine_inner_pointer_region_context package) entry) /\
  MemoryFramedNested.N.A.env_within encoder_bounds
    (memory_source_parameter_values (memory_affine_inner_pointer_region_context package) entry).

Section CONDITION.
Variable source : statement.
Variable package : memory_affine_inner_pointer_package source.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable O : Type.
Variable observe : fragment_observation -> O -> Prop.
Variable width_tree alias_tree : decision_tree.
Variable validator_bounds : list MemoryNested.A.interval.
Variable encoder_bounds : list MemoryFramedNested.N.A.interval.
Hypothesis WIDTH : compile_memory_source_width (affine_inner_pointer_column_limit package)
  (affine_inner_pointer_row (affine_inner_pointer_shape package))
  (memory_affine_inner_pointer_header (affine_inner_pointer_shape package) (affine_inner_pointer_expression package))
  (affine_inner_pointer_header_bounds (affine_inner_pointer_row_limit package) (affine_inner_pointer_header_limits package))
  (affine_inner_pointer_expression package) = Some width_tree.
Hypothesis ALIAS : compile_affine_inner_pointer_package_envelopes package = Some alias_tree.
Let H := readonly_clight_host fe observe.
Let D := affine_inner_pointer_observed_completed package fe.
Let P := fun entry => affine_inner_pointer_ready package entry /\ affine_inner_pointer_source_nonalias package entry.

Definition affine_inner_pointer_candidate_validator_condition :
  readonly_condition H (fun entry => D entry /\ P entry)
    (fun entry => MemoryNested.A.env_within validator_bounds
      (memory_source_parameter_values (memory_affine_inner_pointer_region_context package) entry))
    (MemorySourceRanges.range_guard (memory_affine_inner_pointer_region_context package) validator_bounds).
Proof.
  apply readonly_completed_tree_condition.
  - intros entry [DOMAIN [READY NONALIAS]]; eapply MemorySourceRanges.range_guard_total;
      exact (affine_inner_pointer_ready_view READY).
  - intros entry [DOMAIN [READY NONALIAS]] RUN; eapply MemorySourceRanges.range_guard_sound;
      [exact (affine_inner_pointer_ready_view READY)|exact RUN].
Defined.
Definition affine_inner_pointer_candidate_encoder_condition :
  readonly_condition H
    (fun entry => (D entry /\ P entry) /\ MemoryNested.A.env_within validator_bounds
      (memory_source_parameter_values (memory_affine_inner_pointer_region_context package) entry))
    (fun entry => MemoryFramedNested.N.A.env_within encoder_bounds
      (memory_source_parameter_values (memory_affine_inner_pointer_region_context package) entry))
    (MemoryFramedNested.N.G.range_guard (memory_affine_inner_pointer_region_context package) encoder_bounds).
Proof.
  apply readonly_completed_tree_condition.
  - intros entry [[DOMAIN [READY NONALIAS]] VALIDATOR]; eapply MemoryFramedNested.N.G.range_guard_total;
      exact (affine_inner_pointer_ready_view READY).
  - intros entry [[DOMAIN [READY NONALIAS]] VALIDATOR] RUN; eapply MemoryFramedNested.N.G.range_guard_sound;
      [exact (affine_inner_pointer_ready_view READY)|exact RUN].
Defined.
Definition affine_inner_pointer_candidate_ranges_condition :
  readonly_condition H (fun entry => D entry /\ P entry)
    (affine_inner_pointer_candidate_ranges package validator_bounds encoder_bounds)
    (affine_inner_pointer_candidate_ranges_tree package validator_bounds encoder_bounds).
Proof.
  exact (@sequence_readonly_conditions _ H (clight_readonly_check_algebra fe observe) (fun entry => D entry /\ P entry)
    _ _ _ _ affine_inner_pointer_candidate_validator_condition affine_inner_pointer_candidate_encoder_condition).
Defined.
Definition affine_inner_pointer_candidate_guard_condition :
  readonly_condition H D
    (fun entry => P entry /\ affine_inner_pointer_candidate_ranges package validator_bounds encoder_bounds entry)
    (affine_inner_pointer_candidate_guard_tree package width_tree alias_tree validator_bounds encoder_bounds).
Proof.
  exact (@sequence_readonly_conditions _ H (clight_readonly_check_algebra fe observe) D P
    (affine_inner_pointer_candidate_ranges package validator_bounds encoder_bounds) _ _
    (@affine_inner_pointer_source_guard_condition source package fe O observe width_tree alias_tree WIDTH ALIAS)
    affine_inner_pointer_candidate_ranges_condition).
Defined.
End CONDITION.

Print Assumptions affine_inner_pointer_ready_width_model.
Print Assumptions affine_inner_pointer_candidate_validator_condition.
Print Assumptions affine_inner_pointer_candidate_encoder_condition.
Print Assumptions affine_inner_pointer_candidate_ranges_condition.
Print Assumptions affine_inner_pointer_candidate_guard_condition.
