From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightNoWrap ClightRedundantSet
  ClightRectangularGuard ClightGuard ClightCountedLoop ClightMatrixGuard.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRecursiveSource GuardMemoryRecursiveGuard
  GuardMemoryRecursiveWords GuardMemoryRegistryGuard GuardMemoryTripleGuard GuardMemorySourceParameters GuardMemoryTensorSource
  GuardMemoryTensorSourceRegion GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorBackend.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyTreeFacts
  ClightTensorVolumeGuard ClightTensorBackendGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma tensor_observe_dimensions_available dimensions temps :
  (forall identifier,In identifier(tensor_dimension_registers dimensions) -> exists word,temps!identifier=Some(Vint word)) ->
  exists sizes,tensor_observe_dimensions dimensions temps=Some sizes.
Proof.
  induction dimensions as [|source dimensions IH]; intro WORDS.
  - exists []; reflexivity.
  - assert(REST:exists sizes,tensor_observe_dimensions dimensions temps=Some sizes).
    { apply IH; intros identifier MEMBER; apply WORDS; destruct source; cbn; auto. }
    destruct REST as [sizes SIZES]; destruct source; cbn [tensor_observe_dimensions]; rewrite SIZES.
    + exists(Int.signed(Int.repr z)::sizes); reflexivity.
    + destruct(WORDS i ltac:(cbn; auto))as [word WORD]; rewrite WORD; eexists; reflexivity.
Qed.

Section ORIGINAL_SOURCE.
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

Definition tensor_original_defined entry := exists after final,
  exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)(memory_nest_source nest)E0 after final Out_normal.
Definition tensor_source_layout_guard := match nest with
  | MemorySourceLeaf _ => Decision false
  | MemorySourceAxis iterator _ _ _ => decision_bind(register_tree iterator Int.zero)
      (memory_recursive_bounds_tree cap(memory_nest_bounds nest)(tensor_backend_guard dimensions))(Decision false) end.
Definition tensor_source_layout_accept entry := match nest with
  | MemorySourceLeaf _ => false
  | MemorySourceAxis iterator _ _ _ => register_flag iterator Int.zero entry &&
      (memory_recursive_bounds_accept cap(memory_nest_bounds nest)entry &&
        match tensor_observe_dimensions dimensions(entry_temps entry)with
        | Some sizes=>tensor_volume_check tensor_volume_cap 1 sizes | None=>false end) end.

Lemma tensor_source_layout_ready entry :
  tensor_original_defined entry -> memory_nest_initial nest(entry_temps entry) ->
  memory_recursive_bounds_accept cap(memory_nest_bounds nest)entry=true ->
  tensor_backend_ready dimensions entry.
Proof.
  destruct entry as [ge locals temps memory]; pose(entry:=Entry ge locals temps memory).
  intros [after [final SOURCE]] INITIAL ACCEPT.
  pose proof(@memory_recursive_source_bound_words fe(entry_ge entry)(entry_env entry)nest cap CAP SHAPES FRESH
    (tensor_source_operation_normal operation)(tensor_source_operation_quiet operation)(tensor_source_operation_writes operation)
    (entry_temps entry)(entry_memory entry)after final INITIAL SOURCE)as DOMAIN.
  pose proof(@memory_recursive_bounds_sound cap(memory_nest_bounds nest)entry CAP DOMAIN ACCEPT)as RANGES.
  assert(POSITIVE:Forall(fun bound=>0<Int.signed(temp_word bound(entry_temps entry)))(memory_nest_bounds nest)).
  { eapply Forall_impl; [|exact RANGES]; intros bound [_ RANGE]; exact(proj1 RANGE). }
  destruct(@tensor_source_region_first_capability dimensions nest scalars pointer logical_array operation fe(entry_ge entry)(entry_env entry)
    (entry_temps entry)(entry_memory entry)after final SHAPES FRESH PROTECTED USED POSITIVE INITIAL SOURCE)as [_ WORDS].
  apply tensor_observe_dimensions_available; intros identifier MEMBER.
  destruct(DIMENSION_READS identifier MEMBER)as [BOUND|READ].
  - apply Forall_forall with(x:=identifier)in RANGES; [exact(proj1 RANGES)|exact BOUND].
  - apply WORDS; apply in_or_app; left; exact READ.
Qed.
Theorem tensor_source_layout_guard_exact entry : tensor_original_defined entry ->
  forall accepted,decision_run entry tensor_source_layout_guard accepted <-> accepted=tensor_source_layout_accept entry.
Proof.
  destruct entry as [ge locals temps memory]; pose(entry:=Entry ge locals temps memory).
  intro DEFINED; pose proof(@tensor_source_layout_ready entry DEFINED)as READY;
    unfold tensor_original_defined in DEFINED;
    unfold tensor_source_layout_guard,tensor_source_layout_accept;
    destruct nest as [source|iterator bound body child];
    [intro accepted; split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor]|].
  destruct DEFINED as [after [final SOURCE]].
  apply memory_guard_gate_exact.
  - apply memory_triple_register_exact.
    exact(@memory_recursive_source_iterator_word fe(entry_ge entry)(entry_env entry)iterator bound body child
      (entry_temps entry)(entry_memory entry)after final SOURCE).
  - intro ZERO.
    assert(INITIAL:memory_nest_initial(MemorySourceAxis iterator bound body child)(entry_temps entry)).
    { eapply register_flag_evidence; [|exact ZERO].
      exact(@memory_recursive_source_iterator_word fe(entry_ge entry)(entry_env entry)iterator bound body child
        (entry_temps entry)(entry_memory entry)after final SOURCE). }
    apply memory_recursive_bounds_exact.
    + exact(@memory_recursive_source_bound_words fe(entry_ge entry)(entry_env entry)(MemorySourceAxis iterator bound body child)cap
        CAP SHAPES FRESH(tensor_source_operation_normal operation)(tensor_source_operation_quiet operation)(tensor_source_operation_writes operation)
        (entry_temps entry)(entry_memory entry)after final INITIAL SOURCE).
    + intro ALL.
      destruct(READY INITIAL ALL)as [sizes OBSERVE].
      change(forall flag,decision_run entry(tensor_backend_guard dimensions)flag <->
        flag=match tensor_observe_dimensions dimensions(entry_temps entry)with
          |Some sizes=>tensor_volume_check tensor_volume_cap 1 sizes|None=>false end).
      rewrite OBSERVE; intro flag; split.
      * intro RUN; exact(pure_tree_determinate(tensor_backend_guard_pure dimensions)RUN(@tensor_backend_guard_run entry dimensions sizes OBSERVE)).
      * intro SAME; subst flag; exact(@tensor_backend_guard_run entry dimensions sizes OBSERVE).
Qed.
Theorem tensor_source_layout_guard_pure : pure_tree tensor_source_layout_guard.
Proof.
  unfold tensor_source_layout_guard; destruct nest as [source|iterator bound body child]; [constructor|].
  apply pure_decision_bind; [apply register_tree_pure| |constructor].
  clear DIMENSION_READS.
  induction(memory_nest_bounds(MemorySourceAxis iterator bound body child)); cbn [memory_recursive_bounds_tree].
  - apply tensor_backend_guard_pure.
  - apply pure_decision_bind; [apply register_range_tree_pure|exact IHl|constructor].
Qed.
Theorem tensor_source_layout_guard_available entry : tensor_original_defined entry ->
  decision_run entry tensor_source_layout_guard(tensor_source_layout_accept entry).
Proof. intro DEFINED; apply tensor_source_layout_guard_exact; [exact DEFINED|reflexivity]. Qed.

Definition tensor_source_layout_property entry :=
  memory_nest_initial nest(entry_temps entry) /\
  Forall(fun bound=>register_range bound cap entry)(memory_nest_bounds nest) /\
  exists sizes,tensor_observe_dimensions dimensions(entry_temps entry)=Some sizes /\
    tensor_layout_flag sizes=true.

Theorem tensor_source_layout_guard_sound entry : tensor_original_defined entry ->
  decision_run entry tensor_source_layout_guard true -> tensor_source_layout_property entry.
Proof.
  destruct entry as [ge locals temps memory]; pose(entry:=Entry ge locals temps memory).
  intros DEFINED RUN; pose proof(proj1(tensor_source_layout_guard_exact DEFINED true)RUN)as ACCEPT.
  symmetry in ACCEPT.
  pose proof(@tensor_source_layout_ready entry DEFINED)as READY.
  unfold tensor_original_defined in DEFINED; unfold tensor_source_layout_property,tensor_source_layout_accept in *.
  destruct nest as [source|iterator bound body child]; [discriminate|].
  apply andb_true_iff in ACCEPT as [ZERO REST]; apply andb_true_iff in REST as [ALL VOLUME].
  destruct DEFINED as [after [final SOURCE]].
  assert(INITIAL:memory_nest_initial(MemorySourceAxis iterator bound body child)(entry_temps entry)).
  { eapply register_flag_evidence; [|exact ZERO].
    exact(@memory_recursive_source_iterator_word fe ge locals iterator bound body child temps memory after final SOURCE). }
  split; [exact INITIAL|]; split.
  - eapply memory_recursive_bounds_sound; [exact CAP| |exact ALL].
    exact(@memory_recursive_source_bound_words fe ge locals(MemorySourceAxis iterator bound body child)cap CAP SHAPES FRESH
      (tensor_source_operation_normal operation)(tensor_source_operation_quiet operation)(tensor_source_operation_writes operation)
      temps memory after final INITIAL SOURCE).
  - destruct(READY INITIAL ALL)as [sizes OBSERVE]; exists sizes; split; [exact OBSERVE|].
    change(match tensor_observe_dimensions dimensions(entry_temps entry)with
      |Some sizes=>tensor_volume_check tensor_volume_cap 1 sizes|None=>false end=true)in VOLUME.
    rewrite OBSERVE in VOLUME; apply tensor_volume_check_layout; exact VOLUME.
Qed.

Definition tensor_source_layout_condition O(observe:fragment_observation->O->Prop) :
  readonly_condition(readonly_clight_host fe observe)tensor_original_defined
    tensor_source_layout_property tensor_source_layout_guard.
Proof.
  constructor.
  - intros entry DEFINED; eapply pure_decision_run_safe;
      [apply tensor_source_layout_guard_pure|apply tensor_source_layout_guard_available; exact DEFINED].
  - intros entry DEFINED; exists(tensor_source_layout_accept entry),entry;
      split; [apply tensor_source_layout_guard_available; exact DEFINED|reflexivity].
  - intros entry flag checked DEFINED [RUN SAME]; split; [exact SAME|].
    intro ACCEPT; subst flag; eapply tensor_source_layout_guard_sound; eassumption.
Defined.

End ORIGINAL_SOURCE.
Print Assumptions tensor_observe_dimensions_available.
Print Assumptions tensor_source_layout_ready.
Print Assumptions tensor_source_layout_guard_exact.
Print Assumptions tensor_source_layout_guard_pure.
Print Assumptions tensor_source_layout_guard_available.
Print Assumptions tensor_source_layout_guard_sound.
Print Assumptions tensor_source_layout_condition.
