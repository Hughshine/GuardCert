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
From GuardMemory Require Import GuardMemoryParamPointerBounds GuardMemoryParamPointerSyntax GuardMemoryParamPointerDomain GuardMemoryParamPointerHeader GuardMemoryParamPointerProjectedCandidate.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

From GuardMemory Require Import GuardMemoryStartedPackage GuardMemoryStartedPointerHeader
  GuardMemoryStartedPointerDomain GuardMemoryStartedPointerFootprint GuardMemoryStartedPointerBounds GuardMemoryBoundedSourceChecker.
Definition memory_started_pointer_runtime_presumption source (package : memory_started_pointer_package source) s :=
  memory_started_pointer_header_accept package s = true /\
  locations_nonalias (memory_restrict_locations
    (memory_footprint_allowed (memory_started_pointer_runtime_footprint package (entry_temps s)))
    (memory_multi_pointer_locations (entry_temps s) (param_pointer_region_window (started_pointer_package package)))).
Section CANDIDATE.
Variable source : statement.
Variable package : memory_started_pointer_package source.
Let nest := param_pointer_region_nest (started_pointer_package package).
Let caps := param_pointer_region_limits (started_pointer_package package).
Let pointers := param_pointer_region_pointers (started_pointer_package package).
Let extent := param_pointer_region_window (started_pointer_package package).
Let parameters := param_pointer_region_parameters (started_pointer_package package).
Let parameter_caps := param_pointer_region_parameter_limits (started_pointer_package package).
Let scalars := param_pointer_region_scalars (started_pointer_package package).
Let context := memory_started_pointer_context package.
Let source_loop := memory_started_pointer_loop package.
Let dimensions := length (memory_nest_iterators nest).
Let instructions := memory_param_pointer_region_instructions (started_pointer_package package).
Variable live : list ident.
Variable pool : list (ident*ident).
Variable candidate : L.stmt.
Variable code : statement.
Hypothesis COMPILE : compile_memory_multi_pointer_buffer_loop pointers context (memory_started_pointer_static_bounds package) live pool candidate = Some code.
Hypothesis CANDIDATE : memory_bounded_source_certificate (memory_started_static_bounds package) source_loop context candidate.

Theorem memory_started_pointer_projected_candidate_local fe ge locals le memory after final :
  memory_started_pointer_header_accept package (Entry ge locals le memory) = true ->
  locations_nonalias (memory_restrict_locations
    (memory_footprint_allowed (memory_started_pointer_runtime_footprint package le))
    (memory_multi_pointer_locations le extent)) ->
  exec_stmt fe ge locals le memory source E0 after final Out_normal ->
  exists target, exec_stmt fe ge locals le memory (memory_recursive_candidate code nest) E0 target final Out_normal /\ temp_agree live after target.
Proof.
  intros COUNTS SEPARATED SOURCE.
  pose proof (@memory_started_pointer_source_header_domain source package fe ge locals le memory after final SOURCE) as DOMAIN.
  destruct (@memory_started_pointer_header_sound source package (Entry ge locals le memory) DOMAIN COUNTS)
    as [ACTIVE [RANGES PARAM_RANGES]].
  destruct (@memory_started_pointer_source_under_ranges source (started_pointer_package package)
    (started_pointer_iterator package) (started_pointer_bound package) (started_pointer_body package) (started_pointer_child package)
    fe ge locals le memory after final (started_pointer_nest package) ACTIVE RANGES PARAM_RANGES SOURCE)
    as [PARAM_BINDINGS [SCALAR_BINDINGS [LOOP EXIT]]].
  fold nest parameters parameter_caps scalars pointers extent instructions in LOOP,PARAM_RANGES.
  assert (PARAMETERS : memory_recursive_parameters (memory_nest_bounds nest) le++
    (memory_recursive_parameters parameters le++memory_recursive_parameters scalars le)++[Int.signed (temp_word (started_pointer_iterator package) le)] =
    memory_recursive_parameters context le) by (unfold context,memory_started_pointer_context,memory_param_pointer_runtime_context,memory_recursive_parameters;
      rewrite !map_app; cbn [map]; repeat rewrite <-app_assoc; reflexivity).
  rewrite PARAMETERS in LOOP.
  change (L.loop_semantics (source_loop)
    (memory_recursive_parameters context le)
    (RuntimeState (memory_multi_pointer_locations le extent) memory)
    (RuntimeState (memory_multi_pointer_locations le extent) final)) in LOOP.
  assert (VIEW : MemoryNested.A.typed_view context (memory_recursive_parameters context le) le).
  { change (MemoryNested.A.typed_view context (memory_source_parameter_values context (Entry ge locals le memory)) le).
    apply (@memory_source_parameter_view context (Entry ge locals le memory)); intros identifier MEMBER.
    unfold context,memory_started_pointer_context,memory_param_pointer_runtime_context in MEMBER.
    repeat rewrite in_app_iff in MEMBER; destruct MEMBER as [[MEMBER|[MEMBER|MEMBER]]|MEMBER].
    - eapply memory_vector_bounds_typed; [exact RANGES|exact MEMBER].
    - eapply memory_scalar_bindings_typed; [exact PARAM_BINDINGS|exact MEMBER].
    - eapply memory_scalar_bindings_typed; [exact SCALAR_BINDINGS|exact MEMBER].
    - cbn in MEMBER; destruct MEMBER as [<-|[]]; exact (proj1 (proj1 DOMAIN)). }
  assert (ROOT_RANGE : 0 <= Int.signed (temp_word (started_pointer_iterator package) le) < memory_started_pointer_root_cap package).
  { exact (@memory_started_pointer_root_range source package (Entry ge locals le memory) DOMAIN COUNTS). }
  assert (BASE_LENGTH : length (memory_param_static_bounds caps parameter_caps (length scalars)) =
    length (memory_recursive_parameters (memory_param_pointer_runtime_context (started_pointer_package package)) le)).
  { unfold memory_param_static_bounds,memory_param_pointer_runtime_context,memory_recursive_parameters.
    rewrite !length_app,!length_map,repeat_length.
    unfold caps,parameter_caps,scalars,nest,parameters.
    rewrite (param_pointer_region_limits_length (param_pointer_region_syntax (started_pointer_package package))),
      (param_pointer_region_parameter_limits_length (param_pointer_region_syntax (started_pointer_package package))),memory_nest_lengths; rewrite !length_app; reflexivity. }
  assert (WITHIN : MemoryNested.A.env_within (memory_started_static_bounds package)
    (memory_recursive_parameters context le)).
  { pose proof (@memory_param_validator_count_parameter_scalar_ranges caps (memory_nest_bounds nest) parameter_caps
      (memory_recursive_parameters parameters le) (memory_recursive_parameters scalars le) ge locals le memory RANGES PARAM_RANGES (memory_recursive_scalar_values_range scalars le)) as FACT.
    unfold memory_recursive_parameters in FACT; rewrite length_map in FACT.
    unfold context,memory_started_pointer_context,memory_recursive_parameters; rewrite map_app; cbn [map].
    change (MemoryNested.A.env_within
      (memory_param_static_bounds caps parameter_caps (length scalars)++[MemoryNested.A.Interval 0 (memory_started_pointer_root_cap package-1)])
      (memory_recursive_parameters (memory_param_pointer_runtime_context (started_pointer_package package)) le++
        [Int.signed (temp_word (started_pointer_iterator package) le)])).
    apply memory_started_validator_within_append; [exact BASE_LENGTH| |].
    - unfold memory_param_pointer_runtime_context,memory_recursive_parameters; rewrite !map_app; exact FACT.
    - apply MemoryNested.A.env_within_cons; [unfold MemoryNested.A.contains; cbn; lia|].
      intros index interval ABSENT; rewrite nth_error_nil in ABSENT; discriminate. }
  assert (POINTER_WITHIN : MemoryFramedNested.N.A.env_within (memory_started_pointer_static_bounds package)
    (memory_recursive_parameters context le)).
  { pose proof (@memory_param_encoder_count_parameter_scalar_ranges caps (memory_nest_bounds nest) parameter_caps
      (memory_recursive_parameters parameters le) (memory_recursive_parameters scalars le) ge locals le memory RANGES PARAM_RANGES (memory_recursive_scalar_values_range scalars le)) as FACT.
    unfold memory_recursive_parameters in FACT; rewrite length_map in FACT.
    unfold context,memory_started_pointer_context,memory_recursive_parameters; rewrite map_app; cbn [map].
    change (MemoryFramedNested.N.A.env_within
      (memory_param_pointer_static_bounds caps parameter_caps (length scalars)++[MemoryFramedNested.N.A.Interval 0 (memory_started_pointer_root_cap package-1)])
      (memory_recursive_parameters (memory_param_pointer_runtime_context (started_pointer_package package)) le++
        [Int.signed (temp_word (started_pointer_iterator package) le)])).
    apply memory_started_encoder_within_append; [| |].
    - unfold memory_param_static_bounds in BASE_LENGTH; rewrite !length_app,!length_map,repeat_length in BASE_LENGTH.
      unfold memory_param_pointer_static_bounds; rewrite !length_app,!length_map,repeat_length; exact BASE_LENGTH.
    - unfold memory_param_pointer_runtime_context,memory_recursive_parameters; rewrite !map_app; exact FACT.
    - apply MemoryFramedNested.N.A.env_within_cons; [unfold MemoryFramedNested.N.A.contains; cbn; lia|].
      intros index interval ABSENT; rewrite nth_error_nil in ABSENT; discriminate. }
  pose proof (param_pointer_region_extent (param_pointer_region_syntax (started_pointer_package package))) as WINDOW.
  set (selected := memory_started_pointer_runtime_footprint package le).
  set (allowed := memory_footprint_allowed selected).
  set (restricted := memory_restrict_locations allowed (memory_multi_pointer_locations le extent)).
  assert (NONALIAS : GuardMemoryInstr.NonAlias (RuntimeState restricted memory)) by exact SEPARATED.
  assert (COVERED : memory_loop_cells_covered allowed (source_loop)
    (memory_recursive_parameters context le)).
  { unfold allowed,selected,memory_started_pointer_runtime_footprint,memory_started_pointer_loop.
    fold nest parameters parameter_caps scalars pointers extent instructions dimensions context source_loop.
    apply memory_loop_own_footprint_covered. }
  assert (RESTRICTED : L.loop_semantics (source_loop)
    (memory_recursive_parameters context le) (RuntimeState restricted memory) (RuntimeState restricted final)).
  { change (L.loop_semantics (source_loop)
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
    context (memory_started_pointer_static_bounds package) live pool candidate code (memory_recursive_parameters context le) le
    (RuntimeState (memory_multi_pointer_locations le extent) memory) (RuntimeState (memory_multi_pointer_locations le extent) final) memory
    COMPILE VIEW POINTER_WITHIN TARGET eq_refl (temp_agree_refl pointers le))
    as [private_temps [private_memory [MEMORY [POINTER_FINAL [FRAME EXEC]]]]].
  unfold memory_multi_pointer_buffer_view in MEMORY; inversion MEMORY; subst private_memory.
  assert (PUBLIC : temp_agree (context++live) le private_temps).
  { eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER.
    apply in_app_or in MEMBER as [MEMBER|MEMBER]; apply in_or_app; [left; exact MEMBER|right; apply in_or_app; right; exact MEMBER]. }
  exists (memory_recursive_exit nest private_temps); split.
  - unfold memory_recursive_candidate; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact EXEC|].
    apply memory_recursive_restore_execution; [exact (param_pointer_region_fresh (param_pointer_region_syntax (started_pointer_package package)))|].
    intros identifier MEMBER; destruct (@memory_source_typed_word context (memory_recursive_parameters context le) le identifier VIEW ltac:(unfold context,memory_started_pointer_context,memory_param_pointer_runtime_context; apply in_or_app; left; apply in_or_app; left; exact MEMBER)) as [word WORD].
    exists word; cbn [entry_temps]; rewrite PUBLIC by
      (apply in_or_app; left; unfold context,memory_started_pointer_context,memory_param_pointer_runtime_context; apply in_or_app; left; apply in_or_app; left; exact MEMBER); exact WORD.
  - rewrite EXIT; apply memory_recursive_exit_frame; intros identifier MEMBER.
    apply PUBLIC; apply in_app_or in MEMBER as [MEMBER|MEMBER].
    + apply in_or_app; left; unfold context,memory_started_pointer_context,memory_param_pointer_runtime_context.
      apply in_or_app; left; apply in_or_app; left; exact MEMBER.
    + apply in_or_app; right; exact MEMBER.
Qed.
Definition memory_started_pointer_projected_candidate_rule :
  memory_projected_private_rule live source (memory_recursive_candidate code nest).
Proof.
  pose proof (param_pointer_region_syntax (started_pointer_package package)) as CERT.
  assert (WRITES : writes_only (memory_nest_iterators nest) source).
  { rewrite (param_pointer_region_source CERT); apply memory_nest_source_writes; [exact (param_pointer_region_shapes CERT)|].
    apply memory_pointer_sequence_writes with (operations := param_pointer_region_code (started_pointer_package package)); exact (param_pointer_region_body CERT). }
  refine {| projected_rule_writes := memory_nest_iterators nest; projected_rule_source_writes := WRITES;
    projected_rule_domain := memory_started_pointer_runtime_domain package;
    projected_rule_presumption := memory_started_pointer_runtime_presumption package |}.
  - intros temps p locals le memory after final RUN.
    exact (@memory_started_pointer_source_runtime_domain source package (adapter_entry temps) (globalenv p) locals le memory after final RUN).
  - intros temps p locals le memory after final SCOPE RUN [COUNTS NONALIAS].
    destruct (@memory_started_pointer_projected_candidate_local (adapter_entry temps) (globalenv p) locals le memory after final
      COUNTS NONALIAS RUN) as [target [EXEC FRAME]].
    exists target,final; split; [exact EXEC|split; [exact FRAME|apply memory_equivalent_refl]].
Defined.
End CANDIDATE.
Print Assumptions memory_started_pointer_source_runtime_domain.
Print Assumptions memory_started_pointer_projected_candidate_rule.
