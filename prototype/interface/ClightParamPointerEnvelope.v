From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightGuard ClightNoWrap ClightRectangularGuard ClightCountedLoop ClightPureExpr.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryRecursiveSource GuardMemoryRecursiveDomain
  GuardMemoryMultiPointerCells GuardMemoryNaryAffineAccess GuardMemoryNaryAffineExpressions
  GuardMemoryLinearPointerSyntax GuardMemoryAffinePointerPairs GuardMemoryFiniteFootprint
  GuardMemoryFootprintRestriction GuardMemoryCrossPointerSeparation GuardMemoryParamPointerSyntax
  GuardMemoryParamPointerProjectedCandidate GuardMemoryParamPointerHeader GuardMemoryParamAxisFootprint
  GuardMemoryParamAxisPairs GuardMemoryParamAxisGuard GuardMemoryNaryRanges GuardMemoryScalarPointerBody.
From GuardInterface Require Import AffineBoxEnvelope ClightAffineEnvelope ClightAffinePointerEnvelope
  ClightSourceObservation ClightParametricEnvelope ClightReadonlyLoadedTreeSynthesis
  ClightReadonlyRewrite GuardedRewrite ClightConditionComposition.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint compile_pointer_envelope_pairs dimensions registers limits pairs : option decision_tree :=
  match pairs with
  | [] => Some (Decision true)
  | (first,second)::rest =>
    match compile_observed_affine_separation dimensions registers limits
      (memory_nary_access_array first) (memory_nary_access_array second)
      (memory_nary_access_index first) (memory_nary_access_index second),
      compile_pointer_envelope_pairs dimensions registers limits rest with
    | Some first,Some rest => Some (decision_bind first rest (Decision false))
    | _,_ => None end
  end.

Definition pointer_envelope_pair_separated temps counts parameters (pair : memory_nary_access * memory_nary_access) :=
  exists block base,
    temps ! (memory_nary_access_array (fst pair)) = Some (Vptr block base) /\
    temps ! (memory_nary_access_array (snd pair)) = Some (Vptr block base) /\
    forall left right,
      Forall2 (fun coordinate count => 0 <= coordinate < count) left counts ->
      Forall2 (fun coordinate count => 0 <= coordinate < count) right counts ->
      memory_nary_index_value (memory_nary_access_index (fst pair)) (left++parameters) <>
        memory_nary_index_value (memory_nary_access_index (snd pair)) (right++parameters).

Theorem compiled_pointer_envelope_pairs_sound dimensions registers limits pairs tree
  ge locals temps memory counts parameters :
  compile_pointer_envelope_pairs dimensions registers limits pairs = Some tree ->
  length counts = dimensions ->
  affine_registers_view registers (counts++parameters) temps ->
  Forall2 (fun value limit => 0 <= value < limit) (counts++parameters) limits ->
  (forall pair, In pair pairs -> observed_pointer_domain
    [memory_nary_access_array (fst pair);memory_nary_access_array (snd pair)] (Entry ge locals temps memory)) ->
  (exists answer, decision_run (Entry ge locals temps memory) tree answer) /\
  (decision_run (Entry ge locals temps memory) tree true ->
    Forall (pointer_envelope_pair_separated temps counts parameters) pairs).
Proof.
  revert tree; induction pairs as [|[first second] rest IH]; intros tree ENCODE DIMENSIONS WORDS RANGES OBSERVED.
  - injection ENCODE as <-; split; [exists true; constructor|intros; constructor].
  - cbn [compile_pointer_envelope_pairs] in ENCODE.
    destruct (compile_observed_affine_separation dimensions registers limits
      (memory_nary_access_array first) (memory_nary_access_array second)
      (memory_nary_access_index first) (memory_nary_access_index second)) as [head|] eqn:HEAD; [|discriminate].
    destruct (compile_pointer_envelope_pairs dimensions registers limits rest) as [tail|] eqn:TAIL; [|discriminate].
    injection ENCODE as <-.
    destruct (@compiled_observed_affine_separation_sound dimensions registers limits
      (memory_nary_access_array first) (memory_nary_access_array second)
      (memory_nary_access_index first) (memory_nary_access_index second) head
      ge locals temps memory counts parameters HEAD (OBSERVED (first,second) ltac:(left; reflexivity))
      DIMENSIONS WORDS RANGES) as [[choice RUN] SOUND].
    destruct (IH tail eq_refl DIMENSIONS WORDS RANGES
      ltac:(intros pair MEMBER; apply OBSERVED; right; exact MEMBER)) as [[last LAST] REST].
    split.
    + destruct choice; [exists last|exists false]; eapply decision_bind_run;
        [exact RUN|exact LAST|exact RUN|constructor].
    + intro ACCEPT; apply decision_bind_inv in ACCEPT as [[|] [FIRST SECOND]]; [|inversion SECOND].
      constructor; [|apply REST; exact SECOND].
      destruct (SOUND FIRST) as [block [base [P1 [P2 DIFFERENT]]]].
      exists block,base; split; [exact P1|split; [exact P2|]].
      intros left right LEFT RIGHT; rewrite <- !affine_value_source; apply DIFFERENT; assumption.
Qed.

(** Coverage comes from the actual source footprint theorem. The envelopes
    discharge only physical separation; dependence legality remains in C_opt. *)
Theorem param_pointer_envelopes_nonalias source (package : memory_param_pointer_region_package source)
  temps counts :
  memory_nest_bindings (memory_nest_bounds (param_pointer_region_nest package)) counts temps ->
  Forall signed_range counts ->
  Forall (pointer_envelope_pair_separated temps counts
    (memory_recursive_parameters (param_pointer_region_parameters package) temps))
    (memory_affine_access_pairs (memory_linear_pointer_accesses (param_pointer_region_code package))) ->
  locations_nonalias (memory_restrict_locations
    (memory_footprint_allowed (memory_param_pointer_runtime_footprint package temps))
    (memory_multi_pointer_locations temps (param_pointer_region_window package))).
Proof.
  intros WORDS RANGES PAIRS.
  apply memory_cross_pointer_separation_suffices.
  - exact (proj2 (proj2 (param_pointer_region_extent (param_pointer_region_syntax package)))).
  - intros first second left right FIRST_MEMBER SECOND_MEMBER DISTINCT FIRST SECOND.
    apply memory_footprint_allowed_exact in FIRST_MEMBER,SECOND_MEMBER.
    apply (proj1 (@memory_param_axis_pointer_footprint_member source package temps counts first WORDS RANGES))
      in FIRST_MEMBER as [first_access [first_coordinates [FIRST_ACCESS [FIRST_RANGE ->]]]].
    apply (proj1 (@memory_param_axis_pointer_footprint_member source package temps counts second WORDS RANGES))
      in SECOND_MEMBER as [second_access [second_coordinates [SECOND_ACCESS [SECOND_RANGE ->]]]].
    apply Forall_forall with (x:=(first_access,second_access)) in PAIRS.
    2: { apply memory_affine_access_pair_member; repeat split; assumption. }
    destruct PAIRS as [block [base [P1 [P2 DIFFERENT]]]].
    destruct (@memory_multi_pointer_location_inverse temps (param_pointer_region_window package) _ left FIRST)
      as [b1 [o1 [i1 [PTR1 [IDX1 [RANGE1 LOC1]]]]]].
    destruct (@memory_multi_pointer_location_inverse temps (param_pointer_region_window package) _ right SECOND)
      as [b2 [o2 [i2 [PTR2 [IDX2 [RANGE2 LOC2]]]]]].
    cbn [memory_param_axis_pointer_access_cell point_cell arr_id arr_index] in PTR1,PTR2,IDX1,IDX2.
    injection IDX1 as <-; injection IDX2 as <-.
    eapply common_base_envelope_cell_separation;
      [exact (proj2 (proj2 (param_pointer_region_extent (param_pointer_region_syntax package))))|
       exact P1|exact P2|exact RANGE1|exact RANGE2|apply DIFFERENT; assumption|exact FIRST|exact SECOND].
Qed.

Definition param_pointer_envelope_registers source (package : memory_param_pointer_region_package source) :=
  memory_nest_bounds (param_pointer_region_nest package)++param_pointer_region_parameters package.
Definition param_pointer_envelope_limits source (package : memory_param_pointer_region_package source) :=
  map (fun cap => cap+1) (param_pointer_region_limits package)++param_pointer_region_parameter_limits package.
Definition compile_param_pointer_envelopes source (package : memory_param_pointer_region_package source) :=
  compile_pointer_envelope_pairs (length (memory_nest_iterators (param_pointer_region_nest package)))
    (param_pointer_envelope_registers package) (param_pointer_envelope_limits package)
    (memory_affine_access_pairs (memory_linear_pointer_accesses (param_pointer_region_code package))).
Definition param_pointer_envelope_tree source (package : memory_param_pointer_region_package source) :=
  match compile_param_pointer_envelopes package with
  | Some tree => decision_bind (memory_param_pointer_header_tree package) tree (Decision false)
  | None => Decision false end.

Lemma param_pointer_envelope_header_values source (package : memory_param_pointer_region_package source) entry :
  memory_param_pointer_header_domain package entry -> memory_param_pointer_header_accept package entry = true ->
  exists counts,
    memory_nest_bindings (memory_nest_bounds (param_pointer_region_nest package)) counts (entry_temps entry) /\
    Forall signed_range counts /\ length counts = length (memory_nest_iterators (param_pointer_region_nest package)) /\
    affine_registers_view (param_pointer_envelope_registers package)
      (counts++memory_recursive_parameters (param_pointer_region_parameters package) (entry_temps entry)) (entry_temps entry) /\
    Forall2 (fun value limit => 0 <= value < limit)
      (counts++memory_recursive_parameters (param_pointer_region_parameters package) (entry_temps entry))
      (param_pointer_envelope_limits package).
Proof.
  intros DOMAIN ACCEPT.
  destruct (@memory_param_pointer_header_sound source package entry DOMAIN ACCEPT) as [INITIAL [RANGES PARAMETERS]].
  destruct entry as [ge locals temps memory].
  destruct (@memory_param_axis_pointer_bound_values (param_pointer_region_limits package)
    (memory_nest_bounds (param_pointer_region_nest package)) ge locals temps memory RANGES) as [counts [WORDS SIGNED]].
  assert (COUNT_RANGES : Forall2 (fun value limit => 0 <= value < limit) counts
    (map (fun cap => cap+1) (param_pointer_region_limits package))).
  { revert counts WORDS SIGNED; induction RANGES; intros counts WORDS SIGNED;
      inversion WORDS; subst; inversion SIGNED; subst; constructor; [|apply IHRANGES; assumption].
    destruct H as [[word BINDING] RANGE]; cbn [entry_temps] in BINDING.
    match goal with COUNT : temps ! _ = Some (Vint (Int.repr ?value)) |- _ =>
      assert (WORD : word = Int.repr value) by congruence; subst word end.
    unfold temp_word in RANGE; cbn [entry_temps] in RANGE; rewrite BINDING in RANGE.
    rewrite Int.signed_repr in RANGE by tauto; lia. }
  assert (PARAM_WORDS : memory_nest_bindings (param_pointer_region_parameters package)
    (memory_recursive_parameters (param_pointer_region_parameters package) temps) temps).
  { apply memory_scalar_register_bindings; intros identifier MEMBER.
    destruct DOMAIN as [VECTOR TYPES]; apply andb_true_iff in ACCEPT as [VECTOR_ACCEPT PARAM_ACCEPT].
    pose proof (TYPES VECTOR_ACCEPT) as TYPED; apply Forall_forall with (x:=identifier) in TYPED; assumption. }
  exists counts; split; [exact WORDS|split].
  - eapply Forall_impl; [|exact SIGNED]; intros count [_ RANGE]; exact RANGE.
  - split.
    + unfold memory_nest_bindings in WORDS; pose proof (Forall2_length WORDS) as LENGTH.
      rewrite memory_nest_lengths; exact (eq_sym LENGTH).
    + split; [apply Forall2_app; assumption|].
      apply Forall2_app; [exact COUNT_RANGES|].
      induction PARAMETERS; constructor; auto.
Qed.

Theorem param_pointer_envelope_condition fe O (observe : fragment_observation -> O -> Prop)
  source (package : memory_param_pointer_region_package source) :
  readonly_condition (readonly_clight_host fe observe)
    (fun entry => memory_param_pointer_runtime_domain package entry /\
      observed_pointer_domain (param_pointer_region_pointers package) entry)
    (memory_param_pointer_runtime_presumption package) (param_pointer_envelope_tree package).
Proof.
  assert (CORRECT : forall entry,
    memory_param_pointer_runtime_domain package entry ->
    observed_pointer_domain (param_pointer_region_pointers package) entry ->
    (exists answer, decision_run entry (param_pointer_envelope_tree package) answer) /\
    (decision_run entry (param_pointer_envelope_tree package) true -> memory_param_pointer_runtime_presumption package entry)).
  { intros entry [DOMAIN CAPABLE] OBSERVED; unfold param_pointer_envelope_tree.
    destruct (compile_param_pointer_envelopes package) as [tree|] eqn:COMPILE.
    2: split; [exists false; constructor|intro RUN; inversion RUN].
    pose proof (@memory_param_pointer_header_exact source package entry DOMAIN) as HEADER.
    pose proof (proj2 (HEADER (memory_param_pointer_header_accept package entry)) eq_refl) as HEADER_RUN.
    destruct (memory_param_pointer_header_accept package entry) eqn:HEADER_ACCEPT.
    2: split; [exists false; eapply decision_bind_run; [exact HEADER_RUN|constructor]|];
      intro RUN; apply decision_bind_inv in RUN as [choice [HEAD LEAF]];
      assert (FALSE : choice = false) by (apply (proj1 (HEADER choice)); exact HEAD);
      subst choice; inversion LEAF.
    destruct (param_pointer_envelope_header_values DOMAIN HEADER_ACCEPT)
      as [counts [WORDS [SIGNED [DIMENSIONS [VIEW RANGES]]]]].
    destruct entry as [ge locals temps memory].
    destruct (@compiled_pointer_envelope_pairs_sound
      (length (memory_nest_iterators (param_pointer_region_nest package)))
      (param_pointer_envelope_registers package) (param_pointer_envelope_limits package)
      (memory_affine_access_pairs (memory_linear_pointer_accesses (param_pointer_region_code package))) tree
      ge locals temps memory counts (memory_recursive_parameters (param_pointer_region_parameters package) temps)
      COMPILE DIMENSIONS VIEW RANGES) as [[answer RUN] SOUND].
    - intros [first second] MEMBER identifier IN.
      apply memory_affine_access_pair_member in MEMBER as [FIRST [SECOND DISTINCT]].
      pose proof (memory_param_axis_pointer_accesses_covered package) as COVER.
      cbn [fst snd] in IN; destruct IN as [<-|[<-|[]]]; apply OBSERVED.
      + apply Forall_forall with (x:=first) in COVER; assumption.
      + apply Forall_forall with (x:=second) in COVER; assumption.
    - split.
      + exists answer; eapply decision_bind_run; [exact HEADER_RUN|exact RUN].
      + intro ACCEPT; apply decision_bind_inv in ACCEPT as [[|] [HEAD LEAF]]; [|inversion LEAF].
        split; [exact HEADER_ACCEPT|].
        eapply param_pointer_envelopes_nonalias; [exact WORDS|exact SIGNED|apply SOUND; exact LEAF]. }
  constructor.
  - intros entry [DOMAIN OBSERVED]; destruct (proj1 (CORRECT entry DOMAIN OBSERVED)) as [answer RUN].
    eapply readonly_decision_run_safe; exact RUN.
  - intros entry [DOMAIN OBSERVED]; destruct (proj1 (CORRECT entry DOMAIN OBSERVED)) as [answer RUN].
    exists answer,entry; split; [exact RUN|reflexivity].
  - intros entry answer checked [DOMAIN OBSERVED] [RUN SAME]; split; [exact SAME|intro ACCEPT; subst answer].
    apply (proj2 (CORRECT entry DOMAIN OBSERVED)); exact RUN.
Qed.

Print Assumptions compiled_pointer_envelope_pairs_sound.
Print Assumptions param_pointer_envelopes_nonalias.
Print Assumptions param_pointer_envelope_condition.
