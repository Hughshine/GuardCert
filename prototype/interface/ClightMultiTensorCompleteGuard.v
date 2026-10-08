From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightNoWrap ClightRectangularGuard
  ClightCountedLoop ClightStraightLine ClightGuard ClightRedundantSet.
From GuardMemory Require Import GuardMemoryArrayBackend GuardMemoryRecursiveSource GuardMemoryRecursiveDomain
  GuardMemorySourceParameters GuardMemoryTensorSource GuardMemoryMultiTensorSource GuardMemoryMultiTensorSequence
  GuardMemoryMultiTensorSourceCapabilities GuardMemoryMultiTensorSourceRegion GuardMemoryTripleGuard
  GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorBackend GuardMemoryScalarChecker GuardMemoryScalarPointerBounds
  GuardMemoryIntervalBox GuardMemoryTensorBoxExpressions GuardMemoryTensorSourceRegion.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyTreeFacts
  ClightTensorVolumeGuard ClightTensorBackendGuard ClightTensorSourceGuard ClightTensorBoxGuard
  ClightTensorCompleteGuard ClightTensorCompleteCandidates ClightMultiTensorSourceGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition multi_tensor_body_accesses dimensions layout
    (items : list (multi_tensor_source_statement dimensions layout)) :=
  flat_map (fun item => map (fun access => tensor_source_terms (snd access))
    (mts_write (mt_operation item) :: mts_reads (mt_operation item))) items.

Section SOURCE.
Variables dimensions : list tensor_dimension_source.
Variable nest : memory_source_nest.
Variable scalars : list ident.
Variable items : list (multi_tensor_source_statement dimensions (memory_nest_iterators nest ++ scalars)).
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable cap : Z.
Hypothesis CAP : signed_range cap.
Hypotheses (BODY : flatten_region (memory_nest_leaf nest) = map mt_statement items)
  (NONEMPTY : items <> []) (SHAPES : memory_nest_shapes nest) (FRESH : memory_nest_fresh nest).
Hypothesis PROTECTED : forall identifier, In identifier (memory_nest_iterators nest) ->
  ~ In identifier (multi_tensor_body_pointers items ++ tensor_dimension_registers (tl dimensions) ++ scalars).
Hypothesis USED : multi_tensor_scalar_use_check scalars items = true.
Hypothesis DIMENSION_READS : forall identifier, In identifier (tensor_dimension_registers dimensions) ->
  In identifier (memory_nest_bounds nest) \/ In identifier (tensor_dimension_registers (tl dimensions)).
Let layout := tensor_coordinate_layout dimensions nest scalars.
Let accesses := multi_tensor_body_accesses items.
Variable profile : list (Z*Z).
Variable tree : decision_tree.
Hypothesis COMPILE : compile_tensor_box_guard layout profile (memory_nest_bounds nest) scalars dimensions accesses = Some tree.

Lemma multi_tensor_complete_prefix_words entry : tensor_original_defined nest fe entry ->
  decision_run entry (tensor_source_layout_guard dimensions nest cap) true ->
  Forall (fun identifier => register_domain identifier entry) layout /\
  Forall (fun identifier => 0 < tensor_box_word_valuation (entry_temps entry) identifier) (memory_nest_bounds nest).
Proof.
  destruct entry as [ge locals temps memory]; pose (entry := Entry ge locals temps memory).
  intros DEFINED RUN.
  destruct (@multi_tensor_source_layout_guard_sound dimensions nest scalars items fe cap CAP BODY NONEMPTY
    SHAPES FRESH PROTECTED USED DIMENSION_READS entry DEFINED RUN) as [INITIAL [RANGES _]].
  destruct DEFINED as [after [final SOURCE]].
  assert (POSITIVE : Forall (fun bound => 0 < Int.signed (temp_word bound temps)) (memory_nest_bounds nest)).
  { eapply Forall_impl; [|exact RANGES]; intros identifier [_ RANGE]; exact (proj1 RANGE). }
  destruct (@multi_tensor_source_region_first_capabilities dimensions nest scalars items fe ge locals temps memory
    after final BODY NONEMPTY SHAPES FRESH PROTECTED USED POSITIVE INITIAL SOURCE) as [_ WORDS].
  split; [|exact POSITIVE].
  apply Forall_forall; intros identifier MEMBER; unfold layout,tensor_coordinate_layout in MEMBER.
  apply in_app_or in MEMBER as [BOUND|REST].
  - apply Forall_forall with (x:=identifier) in RANGES; [exact (proj1 RANGES)|exact BOUND].
  - apply in_app_or in REST as [SCALAR|DIMENSION].
    + apply WORDS; apply in_or_app; right; exact SCALAR.
    + destruct (DIMENSION_READS identifier DIMENSION) as [BOUND|READ].
      * apply Forall_forall with (x:=identifier) in RANGES; [exact (proj1 RANGES)|exact BOUND].
      * apply WORDS; apply in_or_app; left; exact READ.
Qed.

Theorem multi_tensor_complete_guard_exact entry : tensor_original_defined nest fe entry ->
  forall accepted, decision_run entry (tensor_complete_tree dimensions nest scalars cap profile tree) accepted <->
    accepted = tensor_complete_flag dimensions nest scalars cap profile accesses entry.
Proof.
  intro DEFINED; unfold tensor_complete_tree,tensor_complete_flag; apply memory_guard_gate_exact.
  - exact (@multi_tensor_source_layout_guard_exact dimensions nest scalars items fe cap CAP BODY NONEMPTY
      SHAPES FRESH PROTECTED USED DIMENSION_READS entry DEFINED).
  - intro ACCEPT.
    assert (RUN : decision_run entry (tensor_source_layout_guard dimensions nest cap) true).
    { apply (@multi_tensor_source_layout_guard_exact dimensions nest scalars items fe cap CAP BODY NONEMPTY
        SHAPES FRESH PROTECTED USED DIMENSION_READS entry DEFINED); symmetry; exact ACCEPT. }
    destruct (multi_tensor_complete_prefix_words DEFINED RUN) as [WORDS POSITIVE].
    exact (@tensor_box_checked_exact layout profile (memory_nest_bounds nest) scalars dimensions accesses tree entry
      COMPILE WORDS POSITIVE).
Qed.

Theorem multi_tensor_complete_guard_pure : pure_tree (tensor_complete_tree dimensions nest scalars cap profile tree).
Proof.
  unfold tensor_complete_tree; apply pure_decision_bind;
    [apply multi_tensor_source_layout_guard_pure| |constructor].
  apply tensor_profile_tree_pure; eapply compile_tensor_box_guard_pure; exact COMPILE.
Qed.

Definition multi_tensor_complete_condition O (observe : fragment_observation -> O -> Prop) :
  readonly_condition (readonly_clight_host fe observe) (tensor_original_defined nest fe)
    (fun entry => tensor_complete_flag dimensions nest scalars cap profile accesses entry = true)
    (tensor_complete_tree dimensions nest scalars cap profile tree).
Proof.
  constructor.
  - intros entry DEFINED; eapply pure_decision_run_safe; [exact multi_tensor_complete_guard_pure|].
    apply multi_tensor_complete_guard_exact; [exact DEFINED|reflexivity].
  - intros entry DEFINED; exists (tensor_complete_flag dimensions nest scalars cap profile accesses entry),entry;
      split; [apply multi_tensor_complete_guard_exact; [exact DEFINED|reflexivity]|reflexivity].
  - intros entry flag checked DEFINED [RUN SAME]; split; [exact SAME|].
    intro ACCEPT; subst flag; symmetry; apply multi_tensor_complete_guard_exact; assumption.
Defined.

Theorem multi_tensor_complete_guard_sound entry : tensor_original_defined nest fe entry ->
  decision_run entry (tensor_complete_tree dimensions nest scalars cap profile tree) true ->
  memory_nest_initial nest (entry_temps entry) /\
  Forall (fun bound => register_range bound cap entry) (memory_nest_bounds nest) /\
  exists sizes, tensor_observe_dimensions dimensions (entry_temps entry) = Some sizes /\
    tensor_layout_flag sizes = true /\
    multi_tensor_body_box items (memory_recursive_counts (memory_nest_bounds nest) (entry_temps entry))
      (memory_recursive_parameters scalars (entry_temps entry)) sizes = true.
Proof.
  destruct entry as [ge locals temps memory]; pose (entry := Entry ge locals temps memory).
  intros DEFINED RUN; unfold tensor_complete_tree in RUN; apply decision_bind_inv in RUN as [flag [FIRST NEXT]].
  destruct flag; cbn in NEXT; [|inversion NEXT].
  destruct (@multi_tensor_source_layout_guard_sound dimensions nest scalars items fe cap CAP BODY NONEMPTY
    SHAPES FRESH PROTECTED USED DIMENSION_READS entry DEFINED FIRST) as [INITIAL [RANGES [sizes [OBSERVE LAYOUT]]]].
  destruct (multi_tensor_complete_prefix_words DEFINED FIRST) as [WORDS POSITIVE].
  pose proof (proj1 (@tensor_box_checked_exact layout profile (memory_nest_bounds nest) scalars dimensions accesses tree
    entry COMPILE WORDS POSITIVE true) NEXT) as ACCEPT; symmetry in ACCEPT.
  unfold tensor_box_checked_flag in ACCEPT; apply andb_true_iff in ACCEPT as [_ BOX].
  split; [exact INITIAL|]; split; [exact RANGES|exists sizes; split; [exact OBSERVE|split; [exact LAYOUT|]]].
  destruct (@memory_recursive_parameter_data cap (memory_nest_bounds nest) ge locals temps memory RANGES) as [_ [VALUES _]].
  destruct (@tensor_observe_dimensions_sound dimensions temps sizes OBSERVE) as [DIMENSIONS SIGNED].
  unfold tensor_box_entry_flag in BOX.
  change (forallb (fun terms => tensor_coordinate_box_check
    (tensor_box_ranges (memory_nest_bounds nest) scalars (tensor_box_word_valuation temps))
    (map (tensor_box_dimension_value (tensor_box_word_valuation temps)) dimensions) terms) accesses = true) in BOX.
  rewrite (@tensor_box_ranges_counts (memory_nest_bounds nest) scalars temps
    (memory_recursive_counts (memory_nest_bounds nest) temps) VALUES),
    (@tensor_box_dimension_view dimensions sizes temps DIMENSIONS SIGNED) in BOX.
  unfold multi_tensor_body_box; apply forallb_forall; intros item MEMBER.
  unfold multi_tensor_source_operation_box; apply forallb_forall; intros access ACCESS.
  apply forallb_forall with (x:=tensor_source_terms (snd access)) in BOX; [exact BOX|].
  unfold accesses,multi_tensor_body_accesses; apply in_flat_map; exists item; split; [exact MEMBER|].
  apply in_map_iff; exists access; split; [reflexivity|exact ACCESS].
Qed.

Theorem multi_tensor_complete_source_setup ge locals temps memory : tensor_original_defined nest fe (Entry ge locals temps memory) ->
  decision_run (Entry ge locals temps memory) (tensor_complete_tree dimensions nest scalars cap profile tree) true ->
  let counts := memory_recursive_counts (memory_nest_bounds nest) temps in
  let values := memory_recursive_parameters scalars temps in
  exists sizes,
    length counts = length (memory_nest_iterators nest) /\
    Forall (fun count => count <> O /\ signed_range (Z.of_nat count)) counts /\
    memory_nest_bindings (memory_nest_bounds nest) (map Z.of_nat counts) temps /\ memory_nest_initial nest temps /\
    memory_nest_bindings scalars values temps /\ Forall signed_range values /\
    tensor_observe_dimensions dimensions temps = Some sizes /\
    decision_run (Entry ge locals temps memory) (tensor_backend_guard dimensions) true /\
    multi_tensor_body_box items counts values sizes = true /\
    MemoryNested.A.env_within (memory_scalar_static_bounds (length counts) cap (length values)) (map Z.of_nat counts ++ values).
Proof.
  intros DEFINED GUARD counts values.
  destruct (multi_tensor_complete_guard_sound DEFINED GUARD) as [INITIAL [RANGES [sizes [OBSERVE [LAYOUT BOX]]]]].
  destruct (@memory_recursive_parameter_data cap (memory_nest_bounds nest) ge locals temps memory RANGES)
    as [BOUNDS [VALUES [COUNTS _]]].
  destruct (@multi_tensor_complete_prefix_words (Entry ge locals temps memory) DEFINED) as [WORDS POSITIVE].
  { unfold tensor_complete_tree in GUARD; apply decision_bind_inv in GUARD as [flag [FIRST NEXT]].
    destruct flag; [exact FIRST|inversion NEXT]. }
  assert (SCALARS : memory_nest_bindings scalars values temps).
  { apply tensor_word_parameter_bindings with (entry:=Entry ge locals temps memory).
    apply Forall_forall; intros identifier MEMBER.
    apply Forall_forall with (x:=identifier) in WORDS; [exact WORDS|].
    unfold layout,tensor_coordinate_layout; apply in_or_app; right; apply in_or_app; left; exact MEMBER. }
  assert (LENGTH : length counts = length (memory_nest_iterators nest)).
  { unfold counts,memory_recursive_counts,memory_recursive_parameters; rewrite !length_map,memory_nest_lengths; reflexivity. }
  assert (SIGNED : Forall signed_range values) by apply memory_recursive_scalar_values_range.
  exists sizes; split; [exact LENGTH|]; split; [exact COUNTS|]; split; [exact BOUNDS|];
    split; [exact INITIAL|]; split; [exact SCALARS|]; split; [exact SIGNED|];
    split; [exact OBSERVE|]; split.
  - pose proof (@tensor_backend_guard_run (Entry ge locals temps memory) dimensions sizes OBSERVE) as RUN.
    rewrite (proj2 (tensor_volume_check_layout sizes) LAYOUT) in RUN; exact RUN.
  - split; [exact BOX|].
    unfold counts; rewrite VALUES; unfold memory_recursive_counts,memory_recursive_parameters at 1;
      rewrite !length_map; eapply memory_scalar_validator_count_scalar_ranges; [exact RANGES|exact SIGNED].
Qed.
End SOURCE.

Print Assumptions multi_tensor_complete_prefix_words.
Print Assumptions multi_tensor_complete_guard_exact.
Print Assumptions multi_tensor_complete_guard_pure.
Print Assumptions multi_tensor_complete_condition.
Print Assumptions multi_tensor_complete_guard_sound.
Print Assumptions multi_tensor_complete_source_setup.
