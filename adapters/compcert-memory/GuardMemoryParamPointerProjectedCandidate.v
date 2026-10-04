From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import AbstractGuard SemanticFacts CompCertMemoryEquivalence ClightGuard ClightCondition ClightNoWrap
  ClightTempFrame ClightTempFootprint ClightPrivateRegion ClightPrivateRule ClightProjectedExecution ClightRectangularGuard ClightCountedLoop ClightRedundantSet.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryLoopTrace GuardMemoryFootprintCapabilities GuardMemoryArrayBackend
  GuardMemoryRecursiveSource GuardMemoryRecursiveSyntax GuardMemoryRecursiveGuard GuardMemoryRecursiveDomain
  GuardMemoryRecursiveRestore GuardMemoryRecursiveChecker GuardMemoryRecursiveCandidate GuardMemoryParametricGuard GuardMemoryParametricSourceDomain
  GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerDomain GuardMemoryMultiPointerRegionGuard GuardMemoryMultiPointerFootprint GuardMemoryMultiPointerCells GuardMemoryActivatedAliasCondition GuardMemoryActivatedRectangle GuardMemoryFiniteFootprint GuardMemoryFootprintRestriction GuardMemoryMultiPointerBackend GuardMemoryScalarChecker GuardMemoryScalarPointerBounds GuardMemoryScalarLoops GuardMemoryPointerSequence GuardMemoryPointerBackend GuardMemoryBufferOffsets GuardMemoryProjectedCondition.
From GuardMemory Require Import GuardMemoryVectorBounds GuardMemoryVectorGuard GuardMemoryVectorChecker
  GuardMemoryVectorPointerBounds.
From GuardMemory Require Import GuardMemoryParamPointerBounds GuardMemoryParamPointerSyntax GuardMemoryParamPointerDomain GuardMemoryParamPointerHeader.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_param_pointer_caps_signed source (package : memory_param_pointer_region_package source) :
  Forall signed_range (param_pointer_region_limits package).
Proof.
  pose proof (param_pointer_region_caps (param_pointer_region_syntax package)) as CAPS.
  eapply Forall_impl; [|exact CAPS]; intros cap [_ SIGNED]; exact SIGNED.
Qed.
Lemma memory_vector_bounds_typed caps bounds s :
  Forall2 (fun cap bound => register_range bound cap s) caps bounds ->
  forall identifier, In identifier bounds -> register_domain identifier s.
Proof.
  intro RANGES; induction RANGES; intros identifier MEMBER; [contradiction|].
  cbn in MEMBER; destruct MEMBER as [<-|MEMBER]; [exact (proj1 H)|apply IHRANGES; exact MEMBER].
Qed.

Definition memory_param_pointer_runtime_context source (package : memory_param_pointer_region_package source) :=
  memory_nest_bounds (param_pointer_region_nest package)++param_pointer_region_parameters package++param_pointer_region_scalars package.
Definition memory_param_pointer_runtime_loop source (package : memory_param_pointer_region_package source) :=
  memory_scalar_rectangle 0 (length (memory_nest_iterators (param_pointer_region_nest package)))
    (length (param_pointer_region_parameters package++param_pointer_region_scalars package)) (memory_param_pointer_region_instructions package).
Definition memory_param_pointer_runtime_footprint source (package : memory_param_pointer_region_package source) temps :=
  memory_events_footprint (memory_loop_trace (memory_param_pointer_runtime_loop package)
    (memory_recursive_parameters (memory_param_pointer_runtime_context package) temps)).
Definition memory_param_pointer_runtime_presumption source (package : memory_param_pointer_region_package source) s :=
  memory_param_pointer_header_accept package s = true /\
  locations_nonalias (memory_restrict_locations
    (memory_footprint_allowed (memory_param_pointer_runtime_footprint package (entry_temps s)))
    (memory_multi_pointer_locations (entry_temps s) (param_pointer_region_window package))).
Definition memory_param_pointer_runtime_domain source (package : memory_param_pointer_region_package source) s :=
  memory_param_pointer_header_domain package s /\
  (memory_param_pointer_header_accept package s = true ->
    Forall (memory_cell_capable (memory_multi_pointer_locations (entry_temps s) (param_pointer_region_window package))
      (entry_memory s)) (memory_param_pointer_runtime_footprint package (entry_temps s))).

Theorem memory_param_pointer_source_runtime_domain source (package : memory_param_pointer_region_package source)
  fe ge locals temps memory after final :
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  memory_param_pointer_runtime_domain package (Entry ge locals temps memory).
Proof.
  intro SOURCE.
  pose proof (@memory_param_pointer_source_header_domain source package fe ge locals temps memory after final SOURCE) as DOMAIN.
  split; [exact DOMAIN|]; intro ACCEPT.
  destruct (@memory_param_pointer_header_sound source package (Entry ge locals temps memory) DOMAIN ACCEPT)
    as [INITIAL [RANGES PARAM_RANGES]].
  destruct (@memory_param_pointer_source_under_ranges source package fe ge locals temps memory after final INITIAL RANGES PARAM_RANGES SOURCE)
    as [PARAMETERS [SCALARS [LOOP EXIT]]].
  pose proof (@memory_loop_source_capabilities _ _
    (RuntimeState (memory_multi_pointer_locations temps (param_pointer_region_window package)) memory)
    (RuntimeState (memory_multi_pointer_locations temps (param_pointer_region_window package)) final)
    (memory_multi_pointer_locations_int32 temps (param_pointer_region_window package)) LOOP) as CAPABLE.
  unfold memory_param_pointer_runtime_footprint,memory_param_pointer_runtime_context,memory_param_pointer_runtime_loop.
  unfold memory_recursive_parameters; rewrite !map_app.
  apply Forall_forall; intros cell MEMBER.
  unfold memory_events_footprint in MEMBER; apply in_flat_map in MEMBER as [event [EVENT ACCESS]].
  apply Forall_forall with (x := event) in CAPABLE; [|exact EVENT].
  apply Forall_forall with (x := cell) in CAPABLE; [exact CAPABLE|exact ACCESS].
Qed.

Section CANDIDATE.
Variable source : statement.
Variable package : memory_param_pointer_region_package source.
Let nest := param_pointer_region_nest package.
Let caps := param_pointer_region_limits package.
Let pointers := param_pointer_region_pointers package.
Let extent := param_pointer_region_window package.
Let parameters := param_pointer_region_parameters package.
Let parameter_caps := param_pointer_region_parameter_limits package.
Let scalars := param_pointer_region_scalars package.
Let context := memory_nest_bounds nest++parameters++scalars.
Let dimensions := length (memory_nest_iterators nest).
Let instructions := memory_param_pointer_region_instructions package.
Variable live : list ident.
Variable pool : list (ident*ident).
Variable candidate : L.stmt.
Variable code : statement.
Hypothesis COMPILE : compile_memory_multi_pointer_buffer_loop pointers context (memory_param_pointer_static_bounds caps parameter_caps (length scalars)) live pool candidate = Some code.
Hypothesis CANDIDATE : memory_bounded_candidate_certificate (memory_param_static_bounds caps parameter_caps (length scalars)) dimensions (length (parameters++scalars)) instructions context candidate.

Theorem memory_param_pointer_projected_candidate_local fe ge locals le memory after final :
  memory_param_pointer_header_accept package (Entry ge locals le memory) = true ->
  locations_nonalias (memory_restrict_locations
    (memory_footprint_allowed (memory_param_pointer_runtime_footprint package le))
    (memory_multi_pointer_locations le extent)) ->
  exec_stmt fe ge locals le memory source E0 after final Out_normal ->
  exists target, exec_stmt fe ge locals le memory (memory_recursive_candidate code nest) E0 target final Out_normal /\ temp_agree live after target.
Proof.
  intros COUNTS SEPARATED SOURCE.
  pose proof (@memory_param_pointer_source_header_domain source package fe ge locals le memory after final SOURCE) as DOMAIN.
  destruct (@memory_param_pointer_header_sound source package (Entry ge locals le memory) DOMAIN COUNTS)
    as [INITIAL [RANGES PARAM_RANGES]].
  destruct (@memory_param_pointer_source_under_ranges source package fe ge locals le memory after final INITIAL RANGES PARAM_RANGES SOURCE)
    as [PARAM_BINDINGS [SCALAR_BINDINGS [LOOP EXIT]]].
  fold nest parameters parameter_caps scalars pointers extent instructions in LOOP,PARAM_RANGES.
  assert (PARAMETERS : memory_recursive_parameters (memory_nest_bounds nest) le++
    (memory_recursive_parameters parameters le++memory_recursive_parameters scalars le) =
    memory_recursive_parameters context le) by (unfold context,memory_recursive_parameters; rewrite !map_app; reflexivity).
  rewrite PARAMETERS in LOOP.
  change (L.loop_semantics (memory_scalar_rectangle 0 dimensions (length (parameters++scalars)) instructions)
    (memory_recursive_parameters context le)
    (RuntimeState (memory_multi_pointer_locations le extent) memory)
    (RuntimeState (memory_multi_pointer_locations le extent) final)) in LOOP.
  assert (VIEW : MemoryNested.A.typed_view context (memory_recursive_parameters context le) le).
  { change (MemoryNested.A.typed_view context (memory_source_parameter_values context (Entry ge locals le memory)) le).
    apply (@memory_source_parameter_view context (Entry ge locals le memory)); intros identifier MEMBER.
    unfold context in MEMBER; repeat rewrite in_app_iff in MEMBER; destruct MEMBER as [MEMBER|[MEMBER|MEMBER]].
    - eapply memory_vector_bounds_typed; [exact RANGES|exact MEMBER].
    - eapply memory_scalar_bindings_typed; [exact PARAM_BINDINGS|exact MEMBER].
    - eapply memory_scalar_bindings_typed; [exact SCALAR_BINDINGS|exact MEMBER]. }
  assert (WITHIN : MemoryNested.A.env_within (memory_param_static_bounds caps parameter_caps (length scalars))
    (memory_recursive_parameters context le)).
  { pose proof (@memory_param_validator_count_parameter_scalar_ranges caps (memory_nest_bounds nest) parameter_caps
      (memory_recursive_parameters parameters le) (memory_recursive_parameters scalars le) ge locals le memory RANGES PARAM_RANGES (memory_recursive_scalar_values_range scalars le)) as FACT.
    unfold memory_recursive_parameters in FACT; rewrite length_map in FACT.
    unfold context,memory_recursive_parameters; rewrite !map_app; exact FACT. }
  assert (POINTER_WITHIN : MemoryFramedNested.N.A.env_within (memory_param_pointer_static_bounds caps parameter_caps (length scalars))
    (memory_recursive_parameters context le)).
  { pose proof (@memory_param_encoder_count_parameter_scalar_ranges caps (memory_nest_bounds nest) parameter_caps
      (memory_recursive_parameters parameters le) (memory_recursive_parameters scalars le) ge locals le memory RANGES PARAM_RANGES (memory_recursive_scalar_values_range scalars le)) as FACT.
    unfold memory_recursive_parameters in FACT; rewrite length_map in FACT.
    unfold context,memory_recursive_parameters; rewrite !map_app; exact FACT. }
  pose proof (param_pointer_region_extent (param_pointer_region_syntax package)) as WINDOW.
  set (selected := memory_param_pointer_runtime_footprint package le).
  set (allowed := memory_footprint_allowed selected).
  set (restricted := memory_restrict_locations allowed (memory_multi_pointer_locations le extent)).
  assert (NONALIAS : GuardMemoryInstr.NonAlias (RuntimeState restricted memory)) by exact SEPARATED.
  assert (COVERED : memory_loop_cells_covered allowed (memory_scalar_rectangle 0 dimensions (length (parameters++scalars)) instructions)
    (memory_recursive_parameters context le)).
  { unfold allowed,selected,memory_param_pointer_runtime_footprint,memory_param_pointer_runtime_loop.
    fold nest parameters parameter_caps scalars pointers extent instructions dimensions context.
    apply memory_loop_own_footprint_covered. }
  assert (RESTRICTED : L.loop_semantics (memory_scalar_rectangle 0 dimensions (length (parameters++scalars)) instructions)
    (memory_recursive_parameters context le) (RuntimeState restricted memory) (RuntimeState restricted final)).
  { change (L.loop_semantics (memory_scalar_rectangle 0 dimensions (length (parameters++scalars)) instructions)
      (memory_recursive_parameters context le)
      (memory_restrict_state allowed (RuntimeState (memory_multi_pointer_locations le extent) memory))
      (memory_restrict_state allowed (RuntimeState (memory_multi_pointer_locations le extent) final))).
    eapply memory_restrict_loop_execution; [exact COVERED|exact LOOP]. }
  pose proof (@CANDIDATE (memory_recursive_parameters context le) (RuntimeState restricted memory) (RuntimeState restricted final)
    ltac:(unfold memory_recursive_parameters; apply length_map) WITHIN NONALIAS RESTRICTED) as VALIDATED.
  assert (TARGET : L.loop_semantics candidate (memory_recursive_parameters context le)
    (RuntimeState (memory_multi_pointer_locations le extent) memory) (RuntimeState (memory_multi_pointer_locations le extent) final))
    by (eapply memory_unrestrict_loop_execution; exact VALIDATED).
  destruct (@compile_memory_multi_pointer_buffer_loop_correct le extent (proj1 (proj2 WINDOW)) fe ge locals pointers
    context (memory_param_pointer_static_bounds caps parameter_caps (length scalars)) live pool candidate code (memory_recursive_parameters context le) le
    (RuntimeState (memory_multi_pointer_locations le extent) memory) (RuntimeState (memory_multi_pointer_locations le extent) final) memory
    COMPILE VIEW POINTER_WITHIN TARGET eq_refl (temp_agree_refl pointers le))
    as [private_temps [private_memory [MEMORY [POINTER_FINAL [FRAME EXEC]]]]].
  unfold memory_multi_pointer_buffer_view in MEMORY; inversion MEMORY; subst private_memory.
  assert (PUBLIC : temp_agree (context++live) le private_temps).
  { eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER.
    apply in_app_or in MEMBER as [MEMBER|MEMBER]; apply in_or_app; [left; exact MEMBER|right; apply in_or_app; right; exact MEMBER]. }
  exists (memory_recursive_exit nest private_temps); split.
  - unfold memory_recursive_candidate; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact EXEC|].
    apply memory_recursive_restore_execution; [exact (param_pointer_region_fresh (param_pointer_region_syntax package))|].
    intros identifier MEMBER; destruct (@memory_source_typed_word context (memory_recursive_parameters context le) le identifier VIEW ltac:(unfold context; apply in_or_app; left; exact MEMBER)) as [word WORD].
    exists word; cbn [entry_temps]; rewrite PUBLIC by
      (apply in_or_app; left; unfold context; apply in_or_app; left; exact MEMBER); exact WORD.
  - rewrite EXIT; apply memory_recursive_exit_frame; intros identifier MEMBER.
    apply PUBLIC; unfold context; apply in_app_or in MEMBER as [MEMBER|MEMBER];
      [apply in_or_app; left; apply in_or_app; left|apply in_or_app; right]; exact MEMBER.
Qed.
Definition memory_param_pointer_projected_candidate_rule :
  memory_projected_private_rule live source (memory_recursive_candidate code nest).
Proof.
  pose proof (param_pointer_region_syntax package) as CERT.
  assert (WRITES : writes_only (memory_nest_iterators nest) source).
  { rewrite (param_pointer_region_source CERT); apply memory_nest_source_writes; [exact (param_pointer_region_shapes CERT)|].
    apply memory_pointer_sequence_writes with (operations := param_pointer_region_code package); exact (param_pointer_region_body CERT). }
  refine {| projected_rule_writes := memory_nest_iterators nest; projected_rule_source_writes := WRITES;
    projected_rule_domain := memory_param_pointer_runtime_domain package;
    projected_rule_presumption := memory_param_pointer_runtime_presumption package |}.
  - intros temps p locals le memory after final RUN.
    exact (@memory_param_pointer_source_runtime_domain source package (adapter_entry temps) (globalenv p) locals le memory after final RUN).
  - intros temps p locals le memory after final SCOPE RUN [COUNTS NONALIAS].
    destruct (@memory_param_pointer_projected_candidate_local (adapter_entry temps) (globalenv p) locals le memory after final
      COUNTS NONALIAS RUN) as [target [EXEC FRAME]].
    exists target,final; split; [exact EXEC|split; [exact FRAME|apply memory_equivalent_refl]].
Defined.
End CANDIDATE.
Print Assumptions memory_param_pointer_source_runtime_domain.
Print Assumptions memory_param_pointer_projected_candidate_rule.
