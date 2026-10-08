From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightGuard ClightNoWrap.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryNaryCompute GuardMemoryNaryRanges GuardMemoryNaryAffineAccess GuardMemoryMultiPointerCells
  GuardMemoryMultiPointerIdentifiers GuardMemoryAffinePointerPairs GuardMemoryLinearPointerSyntax
  GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation GuardMemoryAffineSourceContext GuardMemoryAffineSourceLoop
  GuardMemoryParametricGuard GuardMemoryParametricWidth GuardMemoryParametricSourceDomain GuardMemoryParametricSourceClight
  GuardMemoryFiniteFootprint GuardMemoryFootprintRestriction
  GuardMemoryAffineParameterPointerFootprint GuardMemoryAffineInnerPointerSyntax
  GuardMemoryAffineInnerPointerSourceDomain GuardMemoryAffineInnerPointerRegionSource.
From GuardInterface Require Import GuardedRewrite ReadonlyConditionComposition ClightConditionComposition
  ClightReadonlyRewrite ClightReadonlyCompletedCondition ClightAffineEnvelope ClightParametricEnvelope
  ClightSourceObservation ClightAffineParameterPointerEnvelope ClightAffinePointerGuard
  ClightAffinePointerSourcePreparation ClightAffineInnerPointerEnvelope ClightAffineDomainFacts ClightAffineInnerPointerSourceGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The existing envelope algorithm needs nonnegative bounded widths and
    typed geometry, not a positive first row. Pointer receipts come from the
    retained original loads; they remain separate from source completion. *)
Lemma affine_zero_pointer_encoded_width source (package : memory_affine_inner_pointer_package source) entry :
  affine_domain_ready package entry -> forall i,
    0 <= i < Int.signed (temp_word (affine_inner_pointer_bound (affine_inner_pointer_shape package)) (entry_temps entry)) ->
    L.eval_expr (i::memory_source_parameter_values (memory_affine_inner_pointer_region_context package) entry)
      (affine_inner_pointer_encoded package) <= affine_inner_pointer_column_limit package.
Proof.
  intros READY i RANGE.
  change (L.eval_expr (i::map (fun id => Int.signed (temp_word id (entry_temps entry)))
    (memory_affine_inner_pointer_parameters (affine_inner_pointer_shape package) (affine_inner_pointer_expression package)
      (affine_inner_pointer_body_parameters package)++affine_inner_pointer_scalars package))
    (affine_inner_pointer_encoded package) <= affine_inner_pointer_column_limit package).
  pose proof (@memory_source_loop_expression_value (affine_inner_pointer_expression package)
    (affine_inner_pointer_row (affine_inner_pointer_shape package))
    (memory_affine_inner_pointer_parameters (affine_inner_pointer_shape package) (affine_inner_pointer_expression package)
      (affine_inner_pointer_body_parameters package)++affine_inner_pointer_scalars package)
    (affine_inner_pointer_encoded package) (fun id => Int.signed (temp_word id (entry_temps entry))) i
    (affine_inner_pointer_full_encoding (affine_inner_pointer_syntax package))) as VALUE.
  assert (BOUND : memory_source_affine_math
    (memory_source_set_valuation (fun id => Int.signed (temp_word id (entry_temps entry)))
      (affine_inner_pointer_row (affine_inner_pointer_shape package)) i)
    (affine_inner_pointer_expression package) <= affine_inner_pointer_column_limit package).
  { rewrite <-memory_affine_inner_pointer_word_math.
    apply (proj2 ((affine_domain_ready_width READY) i ltac:(rewrite memory_source_word_temp; exact RANGE))). }
  exact (eq_ind_r (fun value => value <= affine_inner_pointer_column_limit package) BOUND VALUE).
Qed.

Section CONDITION.
Variable source : statement.
Variable package : memory_affine_inner_pointer_package source.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable O : Type.
Variable observe : fragment_observation -> O -> Prop.
Variable alias_tree : decision_tree.
Hypothesis ALIAS : compile_affine_inner_pointer_package_envelopes package=Some alias_tree.
Let H:=readonly_clight_host fe observe.
Let D:=observed_pointer_domain(affine_inner_pointer_pointers package).
Lemma affine_zero_pointer_alias_complete_sound entry :
  D entry -> affine_domain_ready package entry ->
  (exists answer, decision_run entry alias_tree answer) /\
  (decision_run entry alias_tree true -> affine_inner_pointer_source_nonalias package entry).
Proof.
  intros OBSERVED READY.
  set (parameters := memory_source_parameter_values (affine_inner_pointer_geometry package) entry).
  set (scalars := memory_source_parameter_values (affine_inner_pointer_scalars package) entry).
  set (rows := Int.signed (temp_word (affine_inner_pointer_bound (affine_inner_pointer_shape package)) (entry_temps entry))).
  assert (HEAD : exists rest, parameters = rows::rest).
  { unfold parameters,affine_inner_pointer_geometry,memory_affine_inner_pointer_parameters,
      memory_affine_inner_pointer_header,memory_source_context,memory_source_parameter_values,rows; cbn; eexists; reflexivity. }
  assert (GEOMETRY_VIEW : affine_registers_view (affine_inner_pointer_geometry package) parameters (entry_temps entry)).
  { pose proof (affine_domain_ready_view READY) as FULL.
    unfold memory_affine_inner_pointer_region_context,memory_source_parameter_values in FULL; rewrite map_app in FULL.
    apply envelope_typed_view; [unfold parameters,memory_source_parameter_values; symmetry; apply length_map|].
    intros n identifier POSITION.
    change (@List.nth_error positive (affine_inner_pointer_geometry package) n = Some identifier) in POSITION.
    assert (INDEX : (n < length (affine_inner_pointer_geometry package))%nat).
    { apply nth_error_Some; congruence. }
    destruct (FULL n identifier ltac:(rewrite nth_error_app1; [exact POSITION|exact INDEX]))
      as [word [LOOK SIGNED]].
    exists word; split; [exact LOOK|].
    rewrite app_nth1 in SIGNED by (rewrite length_map; exact INDEX); exact SIGNED. }
  assert (VIEW : affine_registers_view
    (affine_inner_pointer_bound (affine_inner_pointer_shape package)::affine_inner_pointer_geometry package)
    (rows::parameters) (entry_temps entry)).
  { constructor; [|exact GEOMETRY_VIEW].
    destruct HEAD as [rest HEAD]; rewrite HEAD in GEOMETRY_VIEW.
    unfold affine_inner_pointer_geometry,memory_affine_inner_pointer_parameters,
      memory_affine_inner_pointer_header,memory_source_context in GEOMETRY_VIEW.
    inversion GEOMETRY_VIEW; assumption. }
  assert (RANGES : Forall2 (fun value limit => 0 <= value < limit) (rows::parameters)
    ((affine_inner_pointer_row_limit package+1)::affine_inner_pointer_geometry_caps package)).
  { constructor.
    2: { pose proof (affine_domain_ready_ranges READY) as GEOM.
      unfold parameters; clear -GEOM.
      induction GEOM; constructor; assumption. }
    pose proof (affine_domain_ready_ranges READY) as GEOM.
    change (memory_nary_ranges (affine_inner_pointer_geometry_caps package) parameters) in GEOM.
    destruct HEAD as [rest HEAD]; rewrite HEAD in GEOM; inversion GEOM; assumption. }
  assert (PAIR_OBS : forall pair, In pair
    (memory_affine_access_pairs (memory_linear_pointer_accesses (affine_inner_pointer_operations package))) ->
    observed_pointer_domain [memory_nary_access_array (fst pair);memory_nary_access_array (snd pair)] entry).
  { intros [first second] MEMBER identifier IN.
    apply memory_affine_access_pair_member in MEMBER as [FIRST [SECOND DISTINCT]].
    pose proof (affine_inner_pointer_package_accesses_covered package) as COVER.
    cbn [fst snd] in IN; destruct IN as [<-|[<-|[]]]; apply OBSERVED.
    - apply Forall_forall with (x:=first) in COVER; assumption.
    - apply Forall_forall with (x:=second) in COVER; assumption. }
  destruct entry as [ge locals temps memory].
  destruct (@compiled_fixed_column_pointer_pairs_sound (affine_inner_pointer_column_limit package) _ _ _ alias_tree
    ge locals temps memory rows parameters ALIAS VIEW RANGES PAIR_OBS) as [SAFE SOUND].
  split; [exact SAFE|intro ACCEPT].
  unfold affine_inner_pointer_source_nonalias,memory_affine_inner_pointer_region_context,memory_source_parameter_values;
    rewrite map_app.
  eapply affine_parameter_pointer_envelopes_nonalias with (parameters:=parameters) (scalars:=scalars)
    (column_cap:=affine_inner_pointer_column_limit package).
  - exact (affine_inner_pointer_operations_valid (affine_inner_pointer_syntax package)).
  - unfold parameters,memory_source_parameter_values,affine_inner_pointer_geometry,
      memory_affine_inner_pointer_layout; rewrite length_app,length_map; cbn; lia.
  - exact (proj2 (proj2 (affine_inner_pointer_window (affine_inner_pointer_syntax package)))).
  - intros i RANGE.
    change (L.eval_expr (i::map (fun id => Int.signed (temp_word id temps))
      (affine_inner_pointer_geometry package)++map (fun id => Int.signed (temp_word id temps))
      (affine_inner_pointer_scalars package)) (affine_inner_pointer_encoded package) <= affine_inner_pointer_column_limit package).
    rewrite <-map_app.
    apply (@affine_zero_pointer_encoded_width source package (Entry ge locals temps memory) READY i).
    destruct HEAD as [rest HEAD]; rewrite HEAD in RANGE; exact RANGE.
  - destruct HEAD as [rest HEAD]; replace (L.eval_expr (parameters++scalars) (L.Var 0)) with rows
      by (rewrite HEAD; reflexivity).
    apply SOUND; exact ACCEPT.
Qed.

Definition affine_zero_pointer_alias_condition :
  readonly_condition H (fun entry => D entry /\ affine_domain_ready package entry)
    (affine_inner_pointer_source_nonalias package) alias_tree.
Proof.
  apply readonly_completed_tree_condition.
  - intros entry [DOMAIN READY]; apply (proj1 (affine_zero_pointer_alias_complete_sound DOMAIN READY)).
  - intros entry [DOMAIN READY] RUN; apply (proj2 (affine_zero_pointer_alias_complete_sound DOMAIN READY)); exact RUN.
Defined.

End CONDITION.

Print Assumptions affine_zero_pointer_encoded_width.
Print Assumptions affine_zero_pointer_alias_complete_sound.
Print Assumptions affine_zero_pointer_alias_condition.
