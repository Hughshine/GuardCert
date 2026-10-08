From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightNoWrap ClightRedundantSet
  ClightRectangularGuard ClightCountedLoop ClightFiniteRegion ClightStraightLine ClightGuard ClightMatrixGuard.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRecursiveSource GuardMemoryRecursiveGuard
  GuardMemoryRecursiveWords GuardMemoryTripleGuard GuardMemoryMultiTensorSequence
  GuardMemoryMultiTensorSourceCapabilities GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorBackend.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyTreeFacts
  ClightTensorVolumeGuard ClightTensorBackendGuard ClightTensorSourceGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma multi_tensor_source_layout_guard_pure dimensions nest cap :
  pure_tree (tensor_source_layout_guard dimensions nest cap).
Proof.
  unfold tensor_source_layout_guard; destruct nest as [source|iterator bound body child]; [constructor|].
  apply pure_decision_bind; [apply register_tree_pure| |constructor].
  induction (memory_nest_bounds (MemorySourceAxis iterator bound body child)); cbn [memory_recursive_bounds_tree].
  - apply tensor_backend_guard_pure.
  - apply pure_decision_bind; [apply register_range_tree_pure|exact IHl|constructor].
Qed.

(** Reuse the existing static layout tree. Its observations are now licensed
    by an actual assignment-list source, with each RHS in its own memory. *)
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

Let NORMAL := @multi_tensor_sequence_normal dimensions _ items (memory_nest_leaf nest) BODY.
Let QUIET := @multi_tensor_sequence_quiet dimensions _ items (memory_nest_leaf nest) BODY.
Let WRITES := @multi_tensor_sequence_writes dimensions _ items (memory_nest_leaf nest) BODY.

Lemma multi_tensor_source_layout_ready entry :
  tensor_original_defined nest fe entry -> memory_nest_initial nest (entry_temps entry) ->
  memory_recursive_bounds_accept cap (memory_nest_bounds nest) entry = true ->
  tensor_backend_ready dimensions entry.
Proof.
  destruct entry as [ge locals temps memory]; pose (entry := Entry ge locals temps memory).
  intros [after [final SOURCE]] INITIAL ACCEPT.
  pose proof (@memory_recursive_source_bound_words fe ge locals nest cap CAP SHAPES FRESH
    NORMAL QUIET WRITES temps memory after final INITIAL SOURCE) as DOMAIN.
  pose proof (@memory_recursive_bounds_sound cap (memory_nest_bounds nest) entry CAP DOMAIN ACCEPT) as RANGES.
  assert (POSITIVE : Forall (fun bound => 0 < Int.signed (temp_word bound temps)) (memory_nest_bounds nest)).
  { eapply Forall_impl; [|exact RANGES]; intros bound [_ RANGE]; exact (proj1 RANGE). }
  destruct (@multi_tensor_source_region_first_capabilities dimensions nest scalars items fe ge locals temps memory
    after final BODY NONEMPTY SHAPES FRESH PROTECTED USED POSITIVE INITIAL SOURCE) as [_ WORDS].
  apply tensor_observe_dimensions_available; intros identifier MEMBER.
  destruct (DIMENSION_READS identifier MEMBER) as [BOUND|READ].
  - apply Forall_forall with (x:=identifier) in RANGES; [exact (proj1 RANGES)|exact BOUND].
  - apply WORDS; apply in_or_app; left; exact READ.
Qed.

Theorem multi_tensor_source_layout_guard_exact entry : tensor_original_defined nest fe entry ->
  forall accepted, decision_run entry (tensor_source_layout_guard dimensions nest cap) accepted <->
    accepted = tensor_source_layout_accept dimensions nest cap entry.
Proof.
  destruct entry as [ge locals temps memory]; pose (entry := Entry ge locals temps memory).
  intro DEFINED; pose proof (@multi_tensor_source_layout_ready entry DEFINED) as READY.
  unfold tensor_original_defined in DEFINED; unfold tensor_source_layout_guard,tensor_source_layout_accept.
  destruct nest as [source|iterator bound body child];
    [intro accepted; split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor]|].
  destruct DEFINED as [after [final SOURCE]].
  apply memory_guard_gate_exact.
  - apply memory_triple_register_exact.
    exact (@memory_recursive_source_iterator_word fe ge locals iterator bound body child temps memory after final SOURCE).
  - intro ZERO.
    assert (INITIAL : memory_nest_initial (MemorySourceAxis iterator bound body child) temps).
    { eapply (@register_flag_evidence iterator Int.zero entry); [|exact ZERO].
      exact (@memory_recursive_source_iterator_word fe ge locals iterator bound body child temps memory after final SOURCE). }
    apply memory_recursive_bounds_exact.
    + exact (@memory_recursive_source_bound_words fe ge locals (MemorySourceAxis iterator bound body child) cap
        CAP SHAPES FRESH NORMAL QUIET WRITES temps memory after final INITIAL SOURCE).
    + intro ALL.
      destruct (READY INITIAL ALL) as [sizes OBSERVE].
      change (tensor_observe_dimensions dimensions temps = Some sizes) in OBSERVE.
      change (forall flag, decision_run entry (tensor_backend_guard dimensions) flag <->
        flag = match tensor_observe_dimensions dimensions temps with
          | Some sizes => tensor_volume_check tensor_volume_cap 1 sizes | None => false end).
      rewrite OBSERVE; intro flag; split.
      * intro RUN; exact (pure_tree_determinate (tensor_backend_guard_pure dimensions) RUN
          (@tensor_backend_guard_run entry dimensions sizes OBSERVE)).
      * intro SAME; subst flag; exact (@tensor_backend_guard_run entry dimensions sizes OBSERVE).
Qed.

Theorem multi_tensor_source_layout_guard_sound entry : tensor_original_defined nest fe entry ->
  decision_run entry (tensor_source_layout_guard dimensions nest cap) true ->
  tensor_source_layout_property dimensions nest cap entry.
Proof.
  destruct entry as [ge locals temps memory]; pose (entry := Entry ge locals temps memory).
  intros DEFINED RUN; pose proof (proj1 (multi_tensor_source_layout_guard_exact DEFINED true) RUN) as ACCEPT.
  symmetry in ACCEPT; pose proof (@multi_tensor_source_layout_ready entry DEFINED) as READY.
  unfold tensor_original_defined in DEFINED; unfold tensor_source_layout_property,tensor_source_layout_accept in *.
  destruct nest as [source|iterator bound body child]; [discriminate|].
  apply andb_true_iff in ACCEPT as [ZERO REST]; apply andb_true_iff in REST as [ALL VOLUME].
  destruct DEFINED as [after [final SOURCE]].
  assert (INITIAL : memory_nest_initial (MemorySourceAxis iterator bound body child) temps).
  { eapply (@register_flag_evidence iterator Int.zero entry); [|exact ZERO].
    exact (@memory_recursive_source_iterator_word fe ge locals iterator bound body child temps memory after final SOURCE). }
  split; [exact INITIAL|]; split.
  - eapply memory_recursive_bounds_sound; [exact CAP| |exact ALL].
    exact (@memory_recursive_source_bound_words fe ge locals (MemorySourceAxis iterator bound body child) cap
      CAP SHAPES FRESH NORMAL QUIET WRITES temps memory after final INITIAL SOURCE).
  - destruct (READY INITIAL ALL) as [sizes OBSERVE]; exists sizes; split; [exact OBSERVE|].
    change (tensor_observe_dimensions dimensions temps = Some sizes) in OBSERVE.
    change (match tensor_observe_dimensions dimensions temps with
      | Some sizes => tensor_volume_check tensor_volume_cap 1 sizes | None => false end = true) in VOLUME.
    rewrite OBSERVE in VOLUME; apply tensor_volume_check_layout; exact VOLUME.
Qed.

Definition multi_tensor_source_layout_condition O (observe : fragment_observation -> O -> Prop) :
  readonly_condition (readonly_clight_host fe observe) (tensor_original_defined nest fe)
    (tensor_source_layout_property dimensions nest cap) (tensor_source_layout_guard dimensions nest cap).
Proof.
  constructor.
  - intros entry DEFINED; eapply pure_decision_run_safe; [apply multi_tensor_source_layout_guard_pure|].
    apply multi_tensor_source_layout_guard_exact; [exact DEFINED|reflexivity].
  - intros entry DEFINED; exists (tensor_source_layout_accept dimensions nest cap entry),entry;
      split; [apply multi_tensor_source_layout_guard_exact; [exact DEFINED|reflexivity]|reflexivity].
  - intros entry flag checked DEFINED [RUN SAME]; split; [exact SAME|].
    intro ACCEPT; subst flag; eapply multi_tensor_source_layout_guard_sound; eassumption.
Defined.
End SOURCE.

Print Assumptions multi_tensor_source_layout_guard_pure.
Print Assumptions multi_tensor_source_layout_ready.
Print Assumptions multi_tensor_source_layout_guard_exact.
Print Assumptions multi_tensor_source_layout_guard_sound.
Print Assumptions multi_tensor_source_layout_condition.
