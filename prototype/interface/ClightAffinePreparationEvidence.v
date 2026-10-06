From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightPureExpr ClightGuard ClightNoWrap
  ClightRedundantSet ClightMatrixGuard ClightRectangularGuard ClightCountedLoop.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryArrayBackend GuardMemoryNaryCompute
  GuardMemoryNaryRanges GuardMemoryParameterRanges GuardMemoryAffineSourceExpressions
  GuardMemoryAffineSourceValuation GuardMemoryAffineSourceContext GuardMemoryAffineSourceEndpoints
  GuardMemoryParametricWidth GuardMemoryParametricGuard GuardMemoryParametricSourceDomain
  GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineInnerPointerSourceDomain.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyCompletedCondition
  ReadonlyConditionComposition ClightConditionComposition ClightReadonlyLoadedTreeSynthesis ClightAffinePointerGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Guard generation consumes source-supported word evidence. Cached and
    loaded source adapters may produce this evidence through different real
    paths; the arithmetic checks and their sequencing have one implementation. *)
Record affine_preparation_evidence shape expression row_limit column_limit body_parameters scalars D := {
  preparation_entry_words : forall entry, D entry ->
    register_domain (affine_inner_pointer_row shape) entry /\
    register_domain (affine_inner_pointer_bound shape) entry /\
    ((entry_temps entry) ! (affine_inner_pointer_row shape) = Some (Vint Int.zero) ->
      0 < Int.signed (temp_word (affine_inner_pointer_bound shape) (entry_temps entry)) ->
      forall identifier, In identifier (memory_source_affine_reads expression) ->
        exists word, (entry_temps entry) ! identifier = Some (Vint word));
  preparation_body_words : forall entry, D entry ->
    memory_affine_inner_pointer_header_accept shape row_limit entry = true ->
    memory_affine_inner_pointer_width_property shape expression column_limit entry ->
    forall identifier, In identifier (body_parameters++scalars) ->
      exists word, (entry_temps entry) ! identifier = Some (Vint word)
}.
Lemma preparation_header_view shape expression row_limit column_limit body_parameters scalars D
  (EVIDENCE : affine_preparation_evidence shape expression row_limit column_limit body_parameters scalars D) entry :
  signed_range row_limit -> D entry -> memory_affine_inner_pointer_header_accept shape row_limit entry = true ->
  MemoryNested.A.typed_view (memory_affine_inner_pointer_header shape expression)
    (memory_source_parameter_values (memory_affine_inner_pointer_header shape expression) entry) (entry_temps entry).
Proof.
  intros CAP DOMAIN ACCEPT; destruct (preparation_entry_words EVIDENCE entry DOMAIN) as [ROW [BOUND WORDS]].
  destruct (@memory_affine_inner_pointer_header_sound shape row_limit entry CAP ROW BOUND ACCEPT) as [ZERO [_ RANGE]].
  apply memory_source_parameter_view; intros identifier MEMBER.
  apply memory_source_context_member in MEMBER as [->|MEMBER]; [exact BOUND|].
  apply WORDS; [exact ZERO|exact (proj1 RANGE)|exact MEMBER].
Qed.
Lemma preparation_context_view shape expression row_limit column_limit body_parameters scalars D
  (EVIDENCE : affine_preparation_evidence shape expression row_limit column_limit body_parameters scalars D) entry :
  signed_range row_limit -> D entry -> memory_affine_inner_pointer_header_accept shape row_limit entry = true ->
  memory_affine_inner_pointer_width_property shape expression column_limit entry ->
  MemoryNested.A.typed_view (memory_affine_inner_pointer_parameters shape expression body_parameters++scalars)
    (memory_source_parameter_values (memory_affine_inner_pointer_parameters shape expression body_parameters++scalars) entry)
    (entry_temps entry).
Proof.
  intros CAP DOMAIN HEADER WIDTH; apply memory_source_parameter_view; intros identifier MEMBER.
  unfold memory_affine_inner_pointer_parameters in MEMBER; rewrite <-app_assoc in MEMBER.
  apply in_app_or in MEMBER as [HEAD|BODY].
  - eapply memory_source_typed_word; [eapply preparation_header_view; eassumption|exact HEAD].
  - eapply preparation_body_words; eassumption.
Qed.

Section GUARD.
Variable source : statement.
Variable shape : memory_affine_inner_pointer_shape.
Variable expression : memory_source_affine.
Variable encoded : L.expr.
Variable row_limit column_limit : Z.
Variable header_limits body_limits : list Z.
Variable body_parameters pointers scalars : list ident.
Variable extent : Z.
Variable operations : list memory_nary_compute.
Variable CERT : memory_affine_inner_pointer_certificate source shape expression encoded row_limit column_limit
  header_limits body_parameters body_limits pointers extent scalars operations.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable O : Type.
Variable observe : fragment_observation -> O -> Prop.
Let H := readonly_clight_host fe observe.
Variable D : clight_entry -> Prop.
Variable EVIDENCE : affine_preparation_evidence shape expression row_limit column_limit body_parameters scalars D.
Let header := memory_affine_inner_pointer_header shape expression.
Let bounds := affine_inner_pointer_header_bounds row_limit header_limits.
Let full_context := memory_affine_inner_pointer_parameters shape expression body_parameters++scalars.
Let head_property := fun entry => memory_affine_inner_pointer_header_accept shape row_limit entry = true.
Let range_property := fun entry => MemoryNested.A.env_within bounds (memory_source_parameter_values header entry).
Let width_property := memory_affine_inner_pointer_width_property shape expression column_limit.
Let body_property := fun entry =>
  memory_nary_ranges body_limits (memory_source_parameter_values body_parameters entry) /\
  MemoryNested.A.typed_view full_context (memory_source_parameter_values full_context entry) (entry_temps entry).

Lemma affine_evidence_header_tree_run entry : D entry ->
  decision_run entry (affine_inner_pointer_header_tree shape row_limit)
    (memory_affine_inner_pointer_header_accept shape row_limit entry).
Proof.
  intro DOMAIN.
  destruct (preparation_entry_words EVIDENCE entry DOMAIN)
    as [ROW [BOUND _]].
  unfold affine_inner_pointer_header_tree,memory_affine_inner_pointer_header_accept.
  eapply run_test; [apply register_expression_test; exact ROW|].
  destruct (register_flag (affine_inner_pointer_row shape) Int.zero entry); cbn; [|constructor].
  apply register_range_tree_run; exact BOUND.
Qed.
Definition affine_evidence_header_condition :
  readonly_condition H D head_property (affine_inner_pointer_header_tree shape row_limit).
Proof.
  apply readonly_completed_tree_condition.
  - intros entry DOMAIN; eexists; apply affine_evidence_header_tree_run; exact DOMAIN.
  - intros entry DOMAIN RUN; unfold head_property.
    eapply readonly_decision_determinate; [apply affine_evidence_header_tree_run; exact DOMAIN|exact RUN].
Defined.

Definition affine_evidence_header_range_condition :
  readonly_condition H (fun entry => D entry /\ head_property entry) range_property
    (MemorySourceRanges.range_guard header bounds).
Proof.
  apply readonly_completed_tree_condition.
  - intros entry [DOMAIN HEAD]; eapply MemorySourceRanges.range_guard_total.
    eapply preparation_header_view; [exact EVIDENCE|
        pose proof (affine_inner_pointer_control_limits CERT) as CAPS; inversion CAPS; subst; tauto|exact DOMAIN|exact HEAD].
  - intros entry [DOMAIN HEAD] RUN; eapply MemorySourceRanges.range_guard_sound;
      [eapply preparation_header_view; [exact EVIDENCE|
        pose proof (affine_inner_pointer_control_limits CERT) as CAPS; inversion CAPS; subst; tauto|exact DOMAIN|exact HEAD]|exact RUN].
Defined.

Variable width_tree : decision_tree.
Hypothesis LOWER : compile_memory_source_width column_limit (affine_inner_pointer_row shape) header bounds expression = Some width_tree.
Lemma affine_evidence_width_complete entry :
  D entry -> head_property entry -> range_property entry -> exists answer, decision_run entry width_tree answer.
Proof.
  intros DOMAIN HEAD RANGE.
  pose proof (@preparation_header_view shape expression row_limit column_limit body_parameters scalars D EVIDENCE entry
    ltac:(pose proof (affine_inner_pointer_control_limits CERT) as CAPS; inversion CAPS; subst; tauto) DOMAIN HEAD) as VIEW.
  unfold compile_memory_source_width in LOWER.
  destruct (memory_source_endpoints (affine_inner_pointer_row shape) header expression) as [[first last]|] eqn:ENDPOINTS; [|discriminate].
  destruct entry as [ge locals temps memory]; eexists.
  eapply MemoryNested.A.lower_test_correct; [exact LOWER|exact RANGE|exact VIEW].
Qed.
Lemma affine_evidence_width_sound entry :
  D entry -> head_property entry -> range_property entry -> decision_run entry width_tree true -> width_property entry.
Proof.
  intros DOMAIN HEAD RANGE RUN.
  destruct (preparation_entry_words EVIDENCE entry DOMAIN)
    as [ROW [BOUND _]].
  assert (CAP : signed_range row_limit).
  { pose proof (affine_inner_pointer_control_limits CERT) as CAPS; inversion CAPS; subst; tauto. }
  destruct (@memory_affine_inner_pointer_header_sound shape row_limit entry CAP ROW BOUND HEAD) as [_ [_ POSITIVE]].
  pose proof (@preparation_header_view shape expression row_limit column_limit body_parameters scalars D EVIDENCE entry
    ltac:(pose proof (affine_inner_pointer_control_limits CERT) as CAPS; inversion CAPS; subst; tauto) DOMAIN HEAD) as VIEW.
  assert (VALUES : memory_source_parameter_values header entry = map (memory_source_word_valuation (entry_temps entry)) header).
  { unfold memory_source_parameter_values; apply map_ext; intros identifier; symmetry; apply memory_source_word_temp. }
  change (MemoryNested.A.typed_view header (memory_source_parameter_values header entry) (entry_temps entry)) in VIEW.
  change (MemoryNested.A.env_within bounds (memory_source_parameter_values header entry)) in RANGE.
  rewrite VALUES in VIEW,RANGE.
  unfold width_property,memory_affine_inner_pointer_width_property.
  destruct entry as [ge locals temps memory].
  eapply compile_memory_source_width_sound;
    [rewrite memory_source_word_temp; exact (proj1 POSITIVE)|exact LOWER|exact VIEW|exact RANGE|exact RUN].
Qed.
Definition affine_evidence_width_condition :
  readonly_condition H (fun entry => D entry /\ (head_property entry /\ range_property entry)) width_property width_tree.
Proof.
  apply readonly_completed_tree_condition.
  - intros entry [DOMAIN [HEAD RANGE]]; apply affine_evidence_width_complete; assumption.
  - intros entry [DOMAIN [HEAD RANGE]] RUN; apply affine_evidence_width_sound; assumption.
Defined.

Definition affine_evidence_body_range_condition :
  readonly_condition H (fun entry => D entry /\ ((head_property entry /\ range_property entry) /\ width_property entry))
    body_property (memory_parameter_ranges_tree body_limits body_parameters (Decision true)).
Proof.
  assert (EXACT : forall entry, D entry -> head_property entry -> width_property entry -> forall flag,
    decision_run entry (memory_parameter_ranges_tree body_limits body_parameters (Decision true)) flag <->
      flag = memory_parameter_ranges_accept body_limits body_parameters entry).
  { intros entry DOMAIN HEAD WIDTH flag; rewrite <- (andb_true_r (memory_parameter_ranges_accept body_limits body_parameters entry)).
    apply memory_parameter_ranges_exact.
    - apply Forall_forall; intros identifier MEMBER; eapply preparation_body_words; [exact EVIDENCE|exact DOMAIN|exact HEAD|exact WIDTH|apply in_or_app; left; exact MEMBER].
    - intros _ answer; split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst answer; constructor]. }
  apply readonly_completed_tree_condition.
  - intros entry [DOMAIN [[HEAD RANGE] WIDTH]]; eexists; apply (proj2 (EXACT entry DOMAIN HEAD WIDTH _)); reflexivity.
  - intros entry [DOMAIN [[HEAD RANGE] WIDTH]] RUN; split.
    + apply memory_parameter_ranges_sound.
      * pose proof (affine_inner_pointer_parameter_limits CERT) as CAPS; apply Forall_app in CAPS; tauto.
      * symmetry; apply (proj1 (EXACT entry DOMAIN HEAD WIDTH true)); exact RUN.
    + eapply preparation_context_view; [exact EVIDENCE|
        pose proof (affine_inner_pointer_control_limits CERT) as CAPS; inversion CAPS; subst; tauto|exact DOMAIN|exact HEAD|exact WIDTH].
Defined.

(** C_guard: the existing language-independent sequencing combinator supplies
    safety/dispatch composition. Source-derived word evidence permits each
    later stage; the final condition is still readonly and refusal falls back.
    Pointer observations and non-alias are a subsequent, separately certified
    stage, not assumptions smuggled into this source domain. *)
Definition affine_evidence_preparation_condition :
  readonly_condition H D
    (fun entry => ((head_property entry /\ range_property entry) /\ width_property entry) /\ body_property entry)
    (affine_inner_pointer_preparation_tree shape expression row_limit header_limits body_parameters body_limits width_tree).
Proof.
  exact (@sequence_readonly_conditions _ H (clight_readonly_check_algebra fe observe) D
    (fun entry => (head_property entry /\ range_property entry) /\ width_property entry) body_property _ _
    (@sequence_readonly_conditions _ H (clight_readonly_check_algebra fe observe) D
      (fun entry => head_property entry /\ range_property entry) width_property _ _
      (@sequence_readonly_conditions _ H (clight_readonly_check_algebra fe observe) D
        head_property range_property _ _ affine_evidence_header_condition affine_evidence_header_range_condition)
      affine_evidence_width_condition) affine_evidence_body_range_condition).
Defined.

Theorem affine_evidence_preparation_ranges entry :
  D entry ->
  decision_run entry (affine_inner_pointer_preparation_tree shape expression row_limit header_limits body_parameters body_limits width_tree) true ->
  memory_affine_inner_pointer_header_accept shape row_limit entry = true /\
  width_property entry /\
  memory_nary_ranges ((row_limit+1)::header_limits++body_limits)
    (memory_source_parameter_values (memory_affine_inner_pointer_parameters shape expression body_parameters) entry) /\
  MemoryNested.A.typed_view full_context (memory_source_parameter_values full_context entry) (entry_temps entry).
Proof.
  intros DOMAIN RUN.
  destruct (readonly_sound affine_evidence_preparation_condition entry true entry DOMAIN (conj RUN eq_refl))
    as [_ ACCEPT]; specialize (ACCEPT eq_refl).
  destruct ACCEPT as [[[HEAD RANGE] WIDTH] [BODY VIEW]].
  split; [exact HEAD|]; split; [exact WIDTH|]; split; [|exact VIEW].
  unfold memory_affine_inner_pointer_parameters,memory_source_parameter_values; rewrite map_app.
  eapply (@Forall2_app Z Z _ ((row_limit+1)::header_limits) body_limits); [|exact BODY].
  apply affine_inner_pointer_caps_within_ranges.
  - unfold header,memory_affine_inner_pointer_header,memory_source_context; rewrite length_map; cbn.
    f_equal; exact (affine_inner_pointer_header_limits_length CERT).
  - change (MemoryNested.A.env_within bounds (memory_source_parameter_values header entry)) in RANGE.
    unfold bounds,affine_inner_pointer_header_bounds in RANGE.
    cbn [map]; replace (row_limit+1-1) with row_limit by lia; exact RANGE.
Qed.
End GUARD.

Print Assumptions preparation_header_view.
Print Assumptions preparation_context_view.
Print Assumptions affine_evidence_header_condition.
Print Assumptions affine_evidence_header_range_condition.
Print Assumptions affine_evidence_width_condition.
Print Assumptions affine_evidence_body_range_condition.
Print Assumptions affine_evidence_preparation_condition.
Print Assumptions affine_evidence_preparation_ranges.
