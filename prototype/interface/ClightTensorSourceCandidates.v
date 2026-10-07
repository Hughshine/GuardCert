From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightRedundantSet ClightNoWrap.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryScalarLoops
  GuardMemoryScalarChecker GuardMemoryPointerBackend GuardMemoryRecursiveSource GuardMemoryTensorSource
  GuardMemoryTensorSourceRegion GuardMemoryDynamicTensorBackend GuardMemoryDynamicTensorLayout GuardMemoryPolyhedral GuardMemoryArrayBackend
  GuardMemoryRecursiveDomain GuardMemoryRecursiveRestore.
From GuardInterface Require Import ClightTensorBackendGuard ClightTensorCandidates.
Import CoreAlarmed ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma tensor_source_bindings_view identifiers values temps : memory_nest_bindings identifiers values temps ->
  Forall signed_range values -> MemoryNested.A.typed_view identifiers values temps.
Proof.
  intro WORDS; induction WORDS as [|identifier value identifiers values WORD WORDS IH];
    intros RANGES [|index] key LOOKUP; cbn in LOOKUP; try discriminate.
  - inversion LOOKUP; subst key; inversion RANGES; subst; exists(Int.repr value); split; [exact WORD|].
    cbn [nth]; rewrite Int.signed_repr by assumption; reflexivity.
  - inversion RANGES; subst; eapply IH; eassumption.
Qed.

Lemma tensor_source_binding_domains identifiers values temps : memory_nest_bindings identifiers values temps ->
  forall identifier,In identifier identifiers -> exists word,temps!identifier=Some(Vint word).
Proof.
  intro WORDS; induction WORDS; intros key MEMBER; [contradiction|].
  destruct MEMBER as [SAME|MEMBER]; [subst key; eexists; exact H|apply IHWORDS; exact MEMBER].
Qed.
Lemma tensor_source_binding_values identifiers values temps : memory_nest_bindings identifiers values temps ->
  Forall signed_range values -> values=memory_recursive_parameters identifiers temps.
Proof.
  intro WORDS; induction WORDS; intro RANGES; [reflexivity|].
  inversion RANGES; subst; unfold memory_recursive_parameters in *; cbn [map]; unfold temp_word at 1.
  rewrite H,Int.signed_repr by assumption; f_equal; apply IHWORDS; assumption.
Qed.

Section SOURCE_CANDIDATE.
Variables dimensions : list tensor_dimension_source.
Variable nest : memory_source_nest.
Variables scalars : list ident.
Variables pointer logical_array : ident.
Variable operation : tensor_source_operation dimensions(memory_nest_iterators nest++scalars)pointer logical_array(memory_nest_leaf nest).
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variables counts : list nat.
Variables scalar_values sizes : list Z.
Variable temps : temp_env.
Variables memory final : mem.
Variable after : temp_env.
Variable block : Values.block.
Variable base : ptrofs.
Variable cap : Z.
Variables live : list ident.
Variable pool : list(ident*ident).
Let parameters:=map Z.of_nat counts++scalar_values.
Let layout:=memory_nest_bounds nest++scalars.
Let instructions:=[tensor_source_instruction operation].
Hypotheses (SHAPES:memory_nest_shapes nest)(FRESH:memory_nest_fresh nest)
  (UNIQUE:NoDup(memory_nest_iterators nest++scalars)).
Hypothesis PROTECTED : forall identifier,In identifier(memory_nest_iterators nest) ->
  ~In identifier(pointer::tensor_dimension_registers dimensions++scalars).
Hypotheses (LENGTH:length counts=length(memory_nest_iterators nest))
  (COUNTS:Forall(fun count=>count<>O /\ signed_range(Z.of_nat count))counts)
  (BOUNDS:memory_nest_bindings(memory_nest_bounds nest)(map Z.of_nat counts)temps)
  (INITIAL:memory_nest_initial nest temps)
  (SCALARS:memory_nest_bindings scalars scalar_values temps)(SCALAR_RANGE:Forall signed_range scalar_values)
  (POINTER:temps!pointer=Some(Vptr block base))
  (OBSERVE:tensor_observe_dimensions dimensions temps=Some sizes)
  (GUARD:decision_run(Entry ge locals temps memory)(tensor_backend_guard dimensions)true)
  (BOX:tensor_source_operation_box operation counts scalar_values sizes=true)
  (WITHIN:MemoryNested.A.env_within(memory_scalar_static_bounds(length counts)cap(length scalar_values))parameters)
  (SOURCE:exec_stmt fe ge locals temps memory(memory_nest_source nest)E0 after final Out_normal).

Lemma tensor_original_source_model :
  L.loop_semantics(memory_scalar_rectangle 0(length counts)(length scalar_values)instructions)parameters
    (RuntimeState(tensor_pointer_locations logical_array block base sizes)memory)
    (RuntimeState(tensor_pointer_locations logical_array block base sizes)final) /\ after=memory_nest_exit nest counts temps.
Proof.
  destruct(@tensor_observe_dimensions_sound dimensions temps sizes OBSERVE)as [DIMENSIONS _].
  eapply tensor_source_region_decode; try eassumption.
  exact(@tensor_backend_guard_accepts(Entry ge locals temps memory)dimensions sizes OBSERVE GUARD).
Qed.
Lemma tensor_original_source_parameter_view : MemoryNested.A.typed_view layout parameters temps.
Proof.
  apply tensor_source_bindings_view.
  - apply memory_nest_bindings_append; assumption.
  - apply Forall_app; split; [|exact SCALAR_RANGE].
    apply Forall_map,Forall_forall; intros count MEMBER; apply Forall_forall with(x:=count)in COUNTS; [exact(proj2 COUNTS)|exact MEMBER].
Qed.
Lemma tensor_original_source_parameter_length : length parameters=length layout.
Proof.
  unfold parameters,layout; rewrite !length_app,length_map.
  pose proof(Forall2_length SCALARS)as SCALAR_LENGTH; rewrite LENGTH,(memory_nest_lengths nest).
  exact(f_equal(fun amount=>(length(memory_nest_bounds nest)+amount)%nat)(eq_sym SCALAR_LENGTH)).
Qed.

Theorem tensor_original_mapped_execution candidate steps code :
  mayReturn(check_tensor_mapped(length counts)cap(length scalar_values)instructions dimensions pointer logical_array layout live pool candidate steps)(Some code) ->
  exists candidate_temps,
    exec_stmt fe ge locals temps memory code E0 candidate_temps final Out_normal /\
    tensor_buffer_capability sizes dimensions pointer block base candidate_temps /\
    temp_agree(layout++tensor_buffer_protected dimensions pointer++live)temps candidate_temps /\
    after=memory_nest_exit nest counts temps.
Proof.
  intro CHECK; destruct tensor_original_source_model as [MODEL EXIT].
  destruct(@check_tensor_mapped_execution fe ge locals dimensions pointer logical_array block base
    (length counts)cap(length scalar_values)instructions layout live pool candidate steps code parameters temps
    (RuntimeState(tensor_pointer_locations logical_array block base sizes)memory)
    (RuntimeState(tensor_pointer_locations logical_array block base sizes)final)memory sizes
    CHECK OBSERVE GUARD tensor_original_source_parameter_view WITHIN tensor_original_source_parameter_length MODEL eq_refl POINTER)
    as [candidate_temps [candidate_memory [MEMORY [CAPABILITY [FRAME RUN]]]]].
  unfold tensor_buffer_view in MEMORY; inversion MEMORY; subst candidate_memory.
  exists candidate_temps; split; [exact RUN|split; [exact CAPABILITY|split; assumption]].
Qed.
Theorem tensor_original_tiled_execution rows columns code :
  mayReturn(check_tensor_tiled(length counts)cap(length scalar_values)instructions dimensions pointer logical_array layout live pool rows columns)(Some code) ->
  exists candidate_temps,
    exec_stmt fe ge locals temps memory code E0 candidate_temps final Out_normal /\
    tensor_buffer_capability sizes dimensions pointer block base candidate_temps /\
    temp_agree(layout++tensor_buffer_protected dimensions pointer++live)temps candidate_temps /\
    after=memory_nest_exit nest counts temps.
Proof.
  intro CHECK; destruct tensor_original_source_model as [MODEL EXIT].
  destruct(@check_tensor_tiled_execution fe ge locals dimensions pointer logical_array block base
    (length counts)cap(length scalar_values)instructions layout live pool rows columns code parameters temps
    (RuntimeState(tensor_pointer_locations logical_array block base sizes)memory)
    (RuntimeState(tensor_pointer_locations logical_array block base sizes)final)memory sizes
    CHECK OBSERVE GUARD tensor_original_source_parameter_view WITHIN tensor_original_source_parameter_length MODEL eq_refl POINTER)
    as [candidate_temps [candidate_memory [MEMORY [CAPABILITY [FRAME RUN]]]]].
  unfold tensor_buffer_view in MEMORY; inversion MEMORY; subst candidate_memory.
  exists candidate_temps; split; [exact RUN|split; [exact CAPABILITY|split; assumption]].
Qed.

(** Restoration reads the original count temporaries and returns all public
    source iterator values.  Scratch temporaries remain private; callers choose
    the public live set, which the existing candidate compiler checks. *)
Lemma tensor_original_candidate_restore code candidate_temps :
  exec_stmt fe ge locals temps memory code E0 candidate_temps final Out_normal ->
  temp_agree(layout++tensor_buffer_protected dimensions pointer++live)temps candidate_temps ->
  after=memory_nest_exit nest counts temps ->
  exists restored,
    exec_stmt fe ge locals temps memory(Ssequence code(memory_recursive_restore nest))E0 restored final Out_normal /\
    temp_agree live after restored.
Proof.
  intros RUN FRAME EXIT.
  assert(LIVE:temp_agree(memory_nest_bounds nest++live)temps candidate_temps).
  { eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER; apply in_app_or in MEMBER as [BOUND|PUBLIC].
    - apply in_or_app; left; unfold layout; apply in_or_app; left; exact BOUND.
    - apply in_or_app; right; apply in_or_app; right; exact PUBLIC. }
  assert(CANDIDATE_BOUNDS:memory_nest_bindings(memory_nest_bounds nest)(map Z.of_nat counts)candidate_temps).
  { eapply memory_nest_bindings_frame; [|exact BOUNDS]; eapply temp_agree_weaken; [|exact LIVE].
    intros identifier MEMBER; apply in_or_app; left; exact MEMBER. }
  assert(VALUES:map Z.of_nat counts=memory_recursive_parameters(memory_nest_bounds nest)temps).
  { apply tensor_source_binding_values; [exact BOUNDS|].
    apply Forall_map,Forall_forall; intros count MEMBER; apply Forall_forall with(x:=count)in COUNTS; [exact(proj2 COUNTS)|exact MEMBER]. }
  rewrite(@memory_recursive_exit_counts nest counts temps VALUES)in EXIT.
  exists(memory_recursive_exit nest candidate_temps); split.
  - eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=candidate_temps)(m1:=final); [exact RUN|].
    apply memory_recursive_restore_execution; [exact FRESH|].
    intros identifier MEMBER; exact(@tensor_source_binding_domains(memory_nest_bounds nest)(map Z.of_nat counts)
      candidate_temps CANDIDATE_BOUNDS identifier MEMBER).
  - rewrite EXIT; apply memory_recursive_exit_frame; exact LIVE.
Qed.
Theorem tensor_original_mapped_restored candidate steps code :
  mayReturn(check_tensor_mapped(length counts)cap(length scalar_values)instructions dimensions pointer logical_array layout live pool candidate steps)(Some code) ->
  exists restored,
    exec_stmt fe ge locals temps memory(Ssequence code(memory_recursive_restore nest))E0 restored final Out_normal /\
    temp_agree live after restored.
Proof.
  intro CHECK; destruct(@tensor_original_mapped_execution candidate steps code CHECK)as [candidate_temps [RUN [_ [FRAME EXIT]]]].
  eapply tensor_original_candidate_restore; eassumption.
Qed.
Theorem tensor_original_tiled_restored rows columns code :
  mayReturn(check_tensor_tiled(length counts)cap(length scalar_values)instructions dimensions pointer logical_array layout live pool rows columns)(Some code) ->
  exists restored,
    exec_stmt fe ge locals temps memory(Ssequence code(memory_recursive_restore nest))E0 restored final Out_normal /\
    temp_agree live after restored.
Proof.
  intro CHECK; destruct(@tensor_original_tiled_execution rows columns code CHECK)as [candidate_temps [RUN [_ [FRAME EXIT]]]].
  eapply tensor_original_candidate_restore; eassumption.
Qed.
End SOURCE_CANDIDATE.

Print Assumptions tensor_source_bindings_view.
Print Assumptions tensor_source_binding_domains.
Print Assumptions tensor_source_binding_values.
Print Assumptions tensor_original_source_model.
Print Assumptions tensor_original_mapped_execution.
Print Assumptions tensor_original_tiled_execution.
Print Assumptions tensor_original_candidate_restore.
Print Assumptions tensor_original_mapped_restored.
Print Assumptions tensor_original_tiled_restored.
