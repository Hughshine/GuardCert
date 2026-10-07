From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightNoWrap ClightRedundantSet ClightCountedLoop ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryRecursiveDomain GuardMemoryTripleGuard
  GuardMemorySourceParameters GuardMemoryTensorSource GuardMemoryTensorSourceRegion GuardMemoryDynamicTensorBackend
  GuardMemoryTensorBoxExpressions GuardMemoryWindowParameterGuard GuardMemoryDynamicTensorLayout.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyTreeFacts
  ClightTensorBackendGuard ClightTensorVolumeGuard ClightTensorSourceGuard ClightTensorBoxGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition tensor_coordinate_layout dimensions nest scalars :=
  memory_nest_bounds nest++scalars++tensor_dimension_registers dimensions.
Definition tensor_operation_accesses dimensions layout pointer logical_array source
    (operation:tensor_source_operation dimensions layout pointer logical_array source) :=
  map(@tensor_source_terms dimensions layout)(tensor_source_write operation::tensor_source_reads operation).
Definition tensor_complete_tree dimensions nest scalars cap profile tree :=
  decision_bind(tensor_source_layout_guard dimensions nest cap)
    (tensor_box_checked_tree profile(tensor_coordinate_layout dimensions nest scalars)tree)(Decision false).
Definition tensor_complete_flag dimensions nest scalars cap profile accesses entry :=
  tensor_source_layout_accept dimensions nest cap entry &&
    tensor_box_checked_flag profile(tensor_coordinate_layout dimensions nest scalars)
      (memory_nest_bounds nest)scalars dimensions accesses entry.

Lemma tensor_box_dimension_view dimensions sizes temps : tensor_dimension_view dimensions sizes temps -> Forall signed_range sizes ->
  map(tensor_box_dimension_value(tensor_box_word_valuation temps))dimensions=sizes.
Proof.
  intro VIEW; induction VIEW as [|source size sources sizes WORD VIEW IH]; intro RANGES; cbn [map]; [reflexivity|].
  inversion RANGES; subst; specialize(IH ltac:(assumption)).
  destruct source; cbn [tensor_dimension_value tensor_box_dimension_value] in *.
  - rewrite WORD,IH; reflexivity.
  - rewrite IH; unfold tensor_box_word_valuation,temp_word; rewrite WORD,Int.signed_repr by assumption; reflexivity.
Qed.

Lemma tensor_box_ranges_counts axes scalars temps counts :
  map Z.of_nat counts=memory_recursive_parameters axes temps ->
  tensor_box_ranges axes scalars(tensor_box_word_valuation temps)=
    tensor_iteration_box counts(memory_recursive_parameters scalars temps).
Proof.
  intro COUNTS; unfold tensor_box_ranges,tensor_iteration_box.
  replace(map(fun count=>(0,Z.of_nat count))counts)with(map(fun value=>(0,value))(map Z.of_nat counts))
    by(rewrite map_map; reflexivity).
  rewrite COUNTS; unfold memory_recursive_parameters; rewrite !map_map; reflexivity.
Qed.

Section SOURCE.
Variables dimensions : list tensor_dimension_source.
Variable nest : memory_source_nest.
Variable scalars : list ident.
Variables pointer logical_array : ident.
Variable operation : tensor_source_operation dimensions(memory_nest_iterators nest++scalars)pointer logical_array(memory_nest_leaf nest).
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable cap : Z.
Hypothesis CAP : signed_range cap.
Hypotheses (SHAPES:memory_nest_shapes nest)(FRESH:memory_nest_fresh nest).
Hypothesis PROTECTED : forall identifier,In identifier(memory_nest_iterators nest) ->
  ~In identifier(pointer::tensor_dimension_registers(tl dimensions)++scalars).
Hypothesis USED : forall identifier,In identifier scalars -> In identifier(tensor_dimension_registers(tl dimensions)) \/
  exists index,nth_error(memory_nest_iterators nest++scalars)index=Some identifier /\
    In index(memory_source_parameter_positions(tensor_source_value operation)).
Hypothesis DIMENSION_READS : forall identifier,In identifier(tensor_dimension_registers dimensions) ->
  In identifier(memory_nest_bounds nest) \/ In identifier(tensor_dimension_registers(tl dimensions)).
Let layout:=tensor_coordinate_layout dimensions nest scalars.
Let accesses:=tensor_operation_accesses operation.
Variable profile : list(Z*Z).
Variable tree : decision_tree.
Hypothesis COMPILE : compile_tensor_box_guard layout profile(memory_nest_bounds nest)scalars dimensions accesses=Some tree.

Lemma tensor_complete_prefix_words entry : tensor_original_defined nest fe entry ->
  decision_run entry(tensor_source_layout_guard dimensions nest cap)true ->
  Forall(fun identifier=>register_domain identifier entry)layout /\
  Forall(fun identifier=>0<tensor_box_word_valuation(entry_temps entry)identifier)(memory_nest_bounds nest).
Proof.
  destruct entry as [ge locals temps memory]; pose(entry:=Entry ge locals temps memory).
  intros DEFINED RUN; destruct(@tensor_source_layout_guard_sound dimensions nest scalars pointer logical_array operation fe cap
    CAP SHAPES FRESH PROTECTED USED DIMENSION_READS entry DEFINED RUN)as [INITIAL [RANGES _]].
  destruct DEFINED as [after [final SOURCE]].
  assert(POSITIVE:Forall(fun identifier=>0<Int.signed(temp_word identifier temps))(memory_nest_bounds nest)).
  { eapply Forall_impl; [|exact RANGES]; intros identifier [_ RANGE]; exact(proj1 RANGE). }
  destruct(@tensor_source_region_first_capability dimensions nest scalars pointer logical_array operation fe ge locals temps memory after final
    SHAPES FRESH PROTECTED USED POSITIVE INITIAL SOURCE)as [_ WORDS].
  split; [|exact POSITIVE].
  apply Forall_forall; intros identifier MEMBER; unfold layout,tensor_coordinate_layout in MEMBER.
  apply in_app_or in MEMBER as [BOUND|REST].
  - apply Forall_forall with(x:=identifier)in RANGES; [exact(proj1 RANGES)|exact BOUND].
  - apply in_app_or in REST as [SCALAR|DIMENSION].
    + apply WORDS; apply in_or_app; right; exact SCALAR.
    + destruct(DIMENSION_READS identifier DIMENSION)as [BOUND|READ].
      * apply Forall_forall with(x:=identifier)in RANGES; [exact(proj1 RANGES)|exact BOUND].
      * apply WORDS; apply in_or_app; left; exact READ.
Qed.
Theorem tensor_complete_guard_exact entry : tensor_original_defined nest fe entry ->
  forall accepted,decision_run entry(tensor_complete_tree dimensions nest scalars cap profile tree)accepted <->
    accepted=tensor_complete_flag dimensions nest scalars cap profile accesses entry.
Proof.
  intro DEFINED; unfold tensor_complete_tree,tensor_complete_flag; apply memory_guard_gate_exact.
  - exact(@tensor_source_layout_guard_exact dimensions nest scalars pointer logical_array operation fe cap
      CAP SHAPES FRESH PROTECTED USED DIMENSION_READS entry DEFINED).
  - intro ACCEPT.
    assert(RUN:decision_run entry(tensor_source_layout_guard dimensions nest cap)true).
    { apply(@tensor_source_layout_guard_exact dimensions nest scalars pointer logical_array operation fe cap
        CAP SHAPES FRESH PROTECTED USED DIMENSION_READS entry DEFINED); symmetry; exact ACCEPT. }
    destruct(tensor_complete_prefix_words DEFINED RUN)as [WORDS POSITIVE].
    exact(@tensor_box_checked_exact layout profile(memory_nest_bounds nest)scalars dimensions accesses tree entry COMPILE WORDS POSITIVE).
Qed.
Theorem tensor_complete_guard_pure : pure_tree(tensor_complete_tree dimensions nest scalars cap profile tree).
Proof.
  unfold tensor_complete_tree; apply pure_decision_bind;
    [exact(@tensor_source_layout_guard_pure dimensions nest scalars pointer logical_array operation cap
       SHAPES FRESH PROTECTED USED DIMENSION_READS)| |constructor].
  apply tensor_profile_tree_pure; eapply compile_tensor_box_guard_pure; exact COMPILE.
Qed.
Definition tensor_complete_condition O(observe:fragment_observation->O->Prop) :
  readonly_condition(readonly_clight_host fe observe)(tensor_original_defined nest fe)
    (fun entry=>tensor_complete_flag dimensions nest scalars cap profile accesses entry=true)
    (tensor_complete_tree dimensions nest scalars cap profile tree).
Proof.
  constructor.
  - intros entry DEFINED; eapply pure_decision_run_safe; [exact tensor_complete_guard_pure|].
    apply tensor_complete_guard_exact; [exact DEFINED|reflexivity].
  - intros entry DEFINED; exists(tensor_complete_flag dimensions nest scalars cap profile accesses entry),entry;
      split; [apply tensor_complete_guard_exact; [exact DEFINED|reflexivity]|reflexivity].
  - intros entry flag checked DEFINED [RUN SAME]; split; [exact SAME|].
    intro ACCEPT; subst flag; symmetry; apply tensor_complete_guard_exact; assumption.
Defined.

Lemma tensor_complete_guard_prefix entry :
  decision_run entry(tensor_complete_tree dimensions nest scalars cap profile tree)true ->
  decision_run entry(tensor_source_layout_guard dimensions nest cap)true /\
  decision_run entry(tensor_box_checked_tree profile layout tree)true.
Proof.
  intro RUN; unfold tensor_complete_tree in RUN; apply decision_bind_inv in RUN as [flag [FIRST NEXT]].
  destruct flag; cbn in NEXT; [split; assumption|inversion NEXT].
Qed.
Theorem tensor_complete_guard_sound entry : tensor_original_defined nest fe entry ->
  decision_run entry(tensor_complete_tree dimensions nest scalars cap profile tree)true ->
  memory_nest_initial nest(entry_temps entry) /\
  Forall(fun bound=>register_range bound cap entry)(memory_nest_bounds nest) /\
  exists sizes,tensor_observe_dimensions dimensions(entry_temps entry)=Some sizes /\
    tensor_layout_flag sizes=true /\
    tensor_source_operation_box operation(memory_recursive_counts(memory_nest_bounds nest)(entry_temps entry))
      (memory_recursive_parameters scalars(entry_temps entry))sizes=true.
Proof.
  destruct entry as [ge locals temps memory]; pose(entry:=Entry ge locals temps memory).
  intros DEFINED RUN; destruct(tensor_complete_guard_prefix RUN)as [FIRST NEXT].
  destruct(@tensor_source_layout_guard_sound dimensions nest scalars pointer logical_array operation fe cap
    CAP SHAPES FRESH PROTECTED USED DIMENSION_READS entry DEFINED FIRST)as [INITIAL [RANGES [sizes [OBSERVE LAYOUT]]]].
  destruct(tensor_complete_prefix_words DEFINED FIRST)as [WORDS POSITIVE].
  pose proof(proj1(@tensor_box_checked_exact layout profile(memory_nest_bounds nest)scalars dimensions accesses tree entry
    COMPILE WORDS POSITIVE true)NEXT)as ACCEPT; symmetry in ACCEPT.
  unfold tensor_box_checked_flag in ACCEPT; apply andb_true_iff in ACCEPT as [_ BOX].
  split; [exact INITIAL|]; split; [exact RANGES|exists sizes; split; [exact OBSERVE|split; [exact LAYOUT|]]].
  destruct(@memory_recursive_parameter_data cap(memory_nest_bounds nest)ge locals temps memory RANGES)as [_ [VALUES _]].
  destruct(@tensor_observe_dimensions_sound dimensions temps sizes OBSERVE)as [DIMENSIONS SIGNED].
  unfold tensor_box_entry_flag in BOX.
  change(forallb(fun terms=>tensor_coordinate_box_check
    (tensor_box_ranges(memory_nest_bounds nest)scalars(tensor_box_word_valuation temps))
    (map(tensor_box_dimension_value(tensor_box_word_valuation temps))dimensions)terms)accesses=true)in BOX.
  rewrite(@tensor_box_ranges_counts(memory_nest_bounds nest)scalars temps(memory_recursive_counts(memory_nest_bounds nest)temps)VALUES),
    (@tensor_box_dimension_view dimensions sizes temps DIMENSIONS SIGNED)in BOX.
  unfold accesses,tensor_operation_accesses in BOX; unfold tensor_source_operation_box.
  apply forallb_forall; intros access MEMBER; apply forallb_forall with(x:=tensor_source_terms access)in BOX;
    [exact BOX|apply in_map; exact MEMBER].
Qed.

End SOURCE.
Print Assumptions tensor_complete_prefix_words.
Print Assumptions tensor_complete_guard_exact.
Print Assumptions tensor_complete_guard_pure.
Print Assumptions tensor_complete_condition.
Print Assumptions tensor_box_dimension_view.
Print Assumptions tensor_box_ranges_counts.
Print Assumptions tensor_complete_guard_sound.
