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
  ClightAffinePointerSourcePreparation ClightAffineInnerPointerEnvelope.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition affine_inner_pointer_geometry source (package : memory_affine_inner_pointer_package source) :=
  memory_affine_inner_pointer_parameters (affine_inner_pointer_shape package) (affine_inner_pointer_expression package)
    (affine_inner_pointer_body_parameters package).
Definition affine_inner_pointer_geometry_caps source (package : memory_affine_inner_pointer_package source) :=
  (affine_inner_pointer_row_limit package+1)::
    affine_inner_pointer_header_limits package++affine_inner_pointer_body_limits package.
Definition compile_affine_inner_pointer_package_envelopes source (package : memory_affine_inner_pointer_package source) :=
  compile_affine_inner_pointer_envelopes (affine_inner_pointer_column_limit package)
    (affine_inner_pointer_bound (affine_inner_pointer_shape package)::affine_inner_pointer_geometry package)
    ((affine_inner_pointer_row_limit package+1)::affine_inner_pointer_geometry_caps package)
    (affine_inner_pointer_operations package).
Definition affine_inner_pointer_source_guard_tree source (package : memory_affine_inner_pointer_package source) width_tree alias_tree :=
  decision_bind (affine_inner_pointer_package_preparation_tree package width_tree) alias_tree (Decision false).

(** Receipt capabilities may be established by a retained source prefix.
    Neither this domain nor the preparation facts assert non-alias. *)
Definition affine_inner_pointer_observed_completed source (package : memory_affine_inner_pointer_package source) fe entry :=
  memory_affine_inner_pointer_completed fe (affine_inner_pointer_shape package) entry /\
  observed_pointer_domain (affine_inner_pointer_pointers package) entry.
Record affine_inner_pointer_ready source (package : memory_affine_inner_pointer_package source) entry : Prop := {
  affine_inner_pointer_ready_header :
    memory_affine_inner_pointer_header_accept (affine_inner_pointer_shape package)
      (affine_inner_pointer_row_limit package) entry = true;
  affine_inner_pointer_ready_width :
    memory_affine_inner_pointer_width_property (affine_inner_pointer_shape package)
      (affine_inner_pointer_expression package) (affine_inner_pointer_column_limit package) entry;
  affine_inner_pointer_ready_ranges : memory_nary_ranges (affine_inner_pointer_geometry_caps package)
    (memory_source_parameter_values (affine_inner_pointer_geometry package) entry);
  affine_inner_pointer_ready_view : MemoryNested.A.typed_view (memory_affine_inner_pointer_region_context package)
    (memory_source_parameter_values (memory_affine_inner_pointer_region_context package) entry) (entry_temps entry)
}.
Definition affine_inner_pointer_source_nonalias source (package : memory_affine_inner_pointer_package source) entry :=
  locations_nonalias (memory_restrict_locations (memory_footprint_allowed
    (memory_affine_parameter_pointer_footprint (affine_inner_pointer_encoded package)
      (length (affine_inner_pointer_scalars package)) (affine_inner_pointer_operations package)
      (memory_source_parameter_values (memory_affine_inner_pointer_region_context package) entry)))
    (memory_multi_pointer_locations (entry_temps entry) (affine_inner_pointer_extent package))).

Lemma affine_inner_pointer_package_accesses_covered source (package : memory_affine_inner_pointer_package source) :
  Forall (fun access => In (memory_nary_access_array access) (affine_inner_pointer_pointers package))
    (memory_linear_pointer_accesses (affine_inner_pointer_operations package)).
Proof.
  pose proof (affine_inner_pointer_operations_covered (affine_inner_pointer_syntax package)) as OPS.
  induction OPS as [|operation operations [WRITE READS] REST IH]; cbn [memory_linear_pointer_accesses flat_map].
  - constructor.
  - apply Forall_app; split; [constructor; assumption|exact IH].
Qed.

Lemma affine_inner_pointer_ready_encoded_width source (package : memory_affine_inner_pointer_package source) entry :
  affine_inner_pointer_ready package entry -> forall i,
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
    apply (proj2 (proj2 (affine_inner_pointer_ready_width READY) i ltac:(rewrite memory_source_word_temp; exact RANGE))). }
  exact (eq_ind_r (fun value => value <= affine_inner_pointer_column_limit package) BOUND VALUE).
Qed.

Section CONDITION.
Variable source : statement.
Variable package : memory_affine_inner_pointer_package source.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable O : Type.
Variable observe : fragment_observation -> O -> Prop.
Variable width_tree alias_tree : decision_tree.
Hypothesis WIDTH : compile_memory_source_width (affine_inner_pointer_column_limit package)
  (affine_inner_pointer_row (affine_inner_pointer_shape package))
  (memory_affine_inner_pointer_header (affine_inner_pointer_shape package) (affine_inner_pointer_expression package))
  (affine_inner_pointer_header_bounds (affine_inner_pointer_row_limit package) (affine_inner_pointer_header_limits package))
  (affine_inner_pointer_expression package) = Some width_tree.
Hypothesis ALIAS : compile_affine_inner_pointer_package_envelopes package = Some alias_tree.
Let H := readonly_clight_host fe observe.
Let D := affine_inner_pointer_observed_completed package fe.

Definition affine_inner_pointer_source_preparation_condition :
  readonly_condition H D (affine_inner_pointer_ready package)
    (affine_inner_pointer_package_preparation_tree package width_tree).
Proof.
  pose proof (@affine_inner_pointer_preparation_condition source
    (affine_inner_pointer_shape package) (affine_inner_pointer_expression package) (affine_inner_pointer_encoded package)
    (affine_inner_pointer_row_limit package) (affine_inner_pointer_column_limit package)
    (affine_inner_pointer_header_limits package) (affine_inner_pointer_body_limits package)
    (affine_inner_pointer_body_parameters package) (affine_inner_pointer_pointers package)
    (affine_inner_pointer_scalars package) (affine_inner_pointer_extent package)
    (affine_inner_pointer_operations package) (affine_inner_pointer_syntax package) fe O observe width_tree WIDTH) as PREP.
  apply readonly_completed_tree_condition.
  - intros entry [DOMAIN OBSERVED]; destruct (readonly_available PREP entry DOMAIN) as [answer [checked [RUN SAME]]].
    exists answer; exact RUN.
  - intros entry [DOMAIN OBSERVED] RUN.
    destruct (@affine_inner_pointer_preparation_ranges source
      (affine_inner_pointer_shape package) (affine_inner_pointer_expression package) (affine_inner_pointer_encoded package)
      (affine_inner_pointer_row_limit package) (affine_inner_pointer_column_limit package)
      (affine_inner_pointer_header_limits package) (affine_inner_pointer_body_limits package)
      (affine_inner_pointer_body_parameters package) (affine_inner_pointer_pointers package)
      (affine_inner_pointer_scalars package) (affine_inner_pointer_extent package)
      (affine_inner_pointer_operations package) (affine_inner_pointer_syntax package) fe O observe width_tree WIDTH
      entry DOMAIN RUN) as [HEADER [LIMIT [RANGES VIEW]]].
    constructor; assumption.
Defined.

Lemma affine_inner_pointer_alias_complete_sound entry :
  D entry -> affine_inner_pointer_ready package entry ->
  (exists answer, decision_run entry alias_tree answer) /\
  (decision_run entry alias_tree true -> affine_inner_pointer_source_nonalias package entry).
Proof.
  intros [DOMAIN OBSERVED] READY.
  set (parameters := memory_source_parameter_values (affine_inner_pointer_geometry package) entry).
  set (scalars := memory_source_parameter_values (affine_inner_pointer_scalars package) entry).
  set (rows := Int.signed (temp_word (affine_inner_pointer_bound (affine_inner_pointer_shape package)) (entry_temps entry))).
  assert (HEAD : exists rest, parameters = rows::rest).
  { unfold parameters,affine_inner_pointer_geometry,memory_affine_inner_pointer_parameters,
      memory_affine_inner_pointer_header,memory_source_context,memory_source_parameter_values,rows; cbn; eexists; reflexivity. }
  assert (GEOMETRY_VIEW : affine_registers_view (affine_inner_pointer_geometry package) parameters (entry_temps entry)).
  { pose proof (affine_inner_pointer_ready_view READY) as FULL.
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
    2: { pose proof (affine_inner_pointer_ready_ranges READY) as GEOM.
      unfold parameters; clear -GEOM.
      induction GEOM; constructor; assumption. }
    pose proof (affine_inner_pointer_ready_ranges READY) as GEOM.
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
    apply (@affine_inner_pointer_ready_encoded_width source package (Entry ge locals temps memory) READY i).
    destruct HEAD as [rest HEAD]; rewrite HEAD in RANGE; exact RANGE.
  - destruct HEAD as [rest HEAD]; replace (L.eval_expr (parameters++scalars) (L.Var 0)) with rows
      by (rewrite HEAD; reflexivity).
    apply SOUND; exact ACCEPT.
Qed.

Definition affine_inner_pointer_source_alias_condition :
  readonly_condition H (fun entry => D entry /\ affine_inner_pointer_ready package entry)
    (affine_inner_pointer_source_nonalias package) alias_tree.
Proof.
  apply readonly_completed_tree_condition.
  - intros entry [DOMAIN READY]; apply (proj1 (affine_inner_pointer_alias_complete_sound DOMAIN READY)).
  - intros entry [DOMAIN READY] RUN; apply (proj2 (affine_inner_pointer_alias_complete_sound DOMAIN READY)); exact RUN.
Defined.

(** The framework sequences the two certificates. The optimizer still owes
    C_opt; no candidate statement or semantic equivalence is inferred here. *)
Definition affine_inner_pointer_source_guard_condition :
  readonly_condition H D
    (fun entry => affine_inner_pointer_ready package entry /\ affine_inner_pointer_source_nonalias package entry)
    (affine_inner_pointer_source_guard_tree package width_tree alias_tree).
Proof.
  exact (@sequence_readonly_conditions _ H (clight_readonly_check_algebra fe observe) D
    (affine_inner_pointer_ready package) (affine_inner_pointer_source_nonalias package) _ _
    affine_inner_pointer_source_preparation_condition affine_inner_pointer_source_alias_condition).
Defined.
End CONDITION.

(** C_host domain producer: an actual retained source prefix and the actual
    source loop establish D at the loop entry. There is no inserted load. *)
Theorem affine_inner_pointer_source_prefix_domain source (package : memory_affine_inner_pointer_package source)
  loads fe ge locals temps memory middle after final :
  source_observations_check (affine_inner_pointer_pointers package) loads = true ->
  exec_stmt fe ge locals temps memory (source_load_prefix loads) E0 middle memory Out_normal ->
  exec_stmt fe ge locals middle memory source E0 after final Out_normal ->
  affine_inner_pointer_observed_completed package fe (Entry ge locals middle memory).
Proof.
  intros CHECK PREFIX SOURCE;
    destruct (@source_observations_check_sound (affine_inner_pointer_pointers package) loads CHECK) as [COVER FRESH]; split.
  - exists after,final; rewrite <- (affine_inner_pointer_source_exact (affine_inner_pointer_syntax package)); exact SOURCE.
  - destruct (@source_load_prefix_observations loads fe ge locals temps memory E0 middle memory Out_normal FRESH PREFIX)
      as [_ [_ [_ OBSERVED]]].
    intros identifier MEMBER; apply OBSERVED,COVER; exact MEMBER.
Qed.

Theorem affine_inner_pointer_source_guard_execution source (package : memory_affine_inner_pointer_package source)
  width_tree alias_tree fe ge locals temps memory after final :
  let shape := affine_inner_pointer_shape package in
  let values := memory_source_parameter_values (memory_affine_inner_pointer_region_context package) (Entry ge locals temps memory) in
  compile_memory_source_width (affine_inner_pointer_column_limit package) (affine_inner_pointer_row shape)
    (memory_affine_inner_pointer_header shape (affine_inner_pointer_expression package))
    (affine_inner_pointer_header_bounds (affine_inner_pointer_row_limit package) (affine_inner_pointer_header_limits package))
    (affine_inner_pointer_expression package) = Some width_tree ->
  compile_affine_inner_pointer_package_envelopes package = Some alias_tree ->
  observed_pointer_domain (affine_inner_pointer_pointers package) (Entry ge locals temps memory) ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  decision_run (Entry ge locals temps memory) (affine_inner_pointer_source_guard_tree package width_tree alias_tree) true ->
  affine_inner_pointer_ready package (Entry ge locals temps memory) /\
  affine_inner_pointer_source_nonalias package (Entry ge locals temps memory) /\
  L.loop_semantics (memory_affine_inner_pointer_region_model package) values
    (RuntimeState (memory_multi_pointer_locations temps (affine_inner_pointer_extent package)) memory)
    (RuntimeState (memory_multi_pointer_locations temps (affine_inner_pointer_extent package)) final) /\
  after = PTree.set (affine_inner_pointer_row shape)
    (Vint (Int.repr (Int.signed (temp_word (affine_inner_pointer_bound shape) temps))))
    (memory_parametric_settle (affine_inner_pointer_column shape) (affine_inner_pointer_inner_bound shape)
      (fun i => L.eval_expr (i::values) (affine_inner_pointer_encoded package))
      (Int.signed (temp_word (affine_inner_pointer_bound shape) temps)-1) temps).
Proof.
  cbn zeta; intros WIDTH ALIAS OBSERVED SOURCE ACCEPT.
  assert (DOMAIN : affine_inner_pointer_observed_completed package fe (Entry ge locals temps memory)).
  { split; [exists after,final; rewrite <- (affine_inner_pointer_source_exact (affine_inner_pointer_syntax package)); exact SOURCE|exact OBSERVED]. }
  pose proof (@affine_inner_pointer_source_guard_condition source package fe fragment_observation
    (@eq fragment_observation) width_tree alias_tree WIDTH ALIAS) as CHECK.
  destruct (readonly_sound CHECK _ _ _ DOMAIN (conj ACCEPT eq_refl)) as [_ SOUND].
  destruct (SOUND eq_refl) as [READY NONALIAS].
  split; [exact READY|split; [exact NONALIAS|]].
  eapply memory_affine_inner_pointer_region_source_under_ranges;
    [exact (affine_inner_pointer_ready_header READY)|exact (affine_inner_pointer_ready_width READY)|
     exact (affine_inner_pointer_ready_ranges READY)|exact SOURCE].
Qed.

Theorem affine_inner_pointer_source_prefix_guard_available source (package : memory_affine_inner_pointer_package source)
  loads width_tree alias_tree fe ge locals temps memory middle after final :
  compile_memory_source_width (affine_inner_pointer_column_limit package)
    (affine_inner_pointer_row (affine_inner_pointer_shape package))
    (memory_affine_inner_pointer_header (affine_inner_pointer_shape package) (affine_inner_pointer_expression package))
    (affine_inner_pointer_header_bounds (affine_inner_pointer_row_limit package) (affine_inner_pointer_header_limits package))
    (affine_inner_pointer_expression package) = Some width_tree ->
  compile_affine_inner_pointer_package_envelopes package = Some alias_tree ->
  source_observations_check (affine_inner_pointer_pointers package) loads = true ->
  exec_stmt fe ge locals temps memory (source_load_prefix loads) E0 middle memory Out_normal ->
  exec_stmt fe ge locals middle memory source E0 after final Out_normal ->
  exists answer, decision_run (Entry ge locals middle memory)
    (affine_inner_pointer_source_guard_tree package width_tree alias_tree) answer.
Proof.
  intros WIDTH ALIAS CHECK PREFIX SOURCE.
  pose proof (@affine_inner_pointer_source_prefix_domain source package loads fe ge locals temps memory middle after final
    CHECK PREFIX SOURCE) as DOMAIN.
  destruct (readonly_available (@affine_inner_pointer_source_guard_condition source package fe fragment_observation
    (@eq fragment_observation) width_tree alias_tree WIDTH ALIAS) _ DOMAIN)
    as [answer [checked [RUN SAME]]].
  exists answer; exact RUN.
Qed.

Print Assumptions affine_inner_pointer_package_accesses_covered.
Print Assumptions affine_inner_pointer_ready_encoded_width.
Print Assumptions affine_inner_pointer_source_preparation_condition.
Print Assumptions affine_inner_pointer_alias_complete_sound.
Print Assumptions affine_inner_pointer_source_alias_condition.
Print Assumptions affine_inner_pointer_source_guard_condition.
Print Assumptions affine_inner_pointer_source_prefix_domain.
Print Assumptions affine_inner_pointer_source_guard_execution.
Print Assumptions affine_inner_pointer_source_prefix_guard_available.
