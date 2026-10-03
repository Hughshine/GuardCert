From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import AbstractGuard SemanticFacts CompCertMemoryEquivalence ClightGuard ClightCondition ClightNoWrap
  ClightTempFrame ClightTempFootprint ClightPrivateRegion ClightPrivateRule ClightProjectedExecution ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryLoopTrace GuardMemoryFootprintCapabilities GuardMemoryArrayBackend
  GuardMemoryRecursiveSource GuardMemoryRecursiveSyntax GuardMemoryRecursiveGuard GuardMemoryRecursiveDomain
  GuardMemoryRecursiveRestore GuardMemoryRecursiveChecker GuardMemoryRecursiveCandidate GuardMemoryParametricGuard GuardMemoryParametricSourceDomain
  GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerDomain GuardMemoryMultiPointerRegionGuard GuardMemoryMultiPointerFootprint GuardMemoryMultiPointerCells GuardMemoryActivatedAliasCondition GuardMemoryActivatedRectangle GuardMemoryFiniteFootprint GuardMemoryFootprintRestriction GuardMemoryMultiPointerBackend GuardMemoryScalarChecker GuardMemoryScalarPointerBounds GuardMemoryScalarLoops GuardMemoryPointerSequence GuardMemoryPointerBackend GuardMemoryBufferOffsets GuardMemoryProjectedCondition.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_multi_pointer_runtime_context source (package : memory_multi_pointer_region_package source) :=
  memory_nest_bounds (multi_pointer_region_nest package)++multi_pointer_region_scalars package.
Definition memory_multi_pointer_runtime_loop source (package : memory_multi_pointer_region_package source) :=
  memory_scalar_rectangle 0 (length (memory_nest_iterators (multi_pointer_region_nest package)))
    (length (multi_pointer_region_scalars package)) (memory_multi_pointer_region_instructions package).
Definition memory_multi_pointer_runtime_footprint source (package : memory_multi_pointer_region_package source) temps :=
  memory_events_footprint (memory_loop_trace (memory_multi_pointer_runtime_loop package)
    (memory_recursive_parameters (memory_multi_pointer_runtime_context package) temps)).
Definition memory_multi_pointer_runtime_presumption source (package : memory_multi_pointer_region_package source) s :=
  memory_recursive_guard_accept (multi_pointer_region_limit package) [] (multi_pointer_region_nest package) s = true /\
  locations_nonalias (memory_restrict_locations
    (memory_footprint_allowed (memory_multi_pointer_runtime_footprint package (entry_temps s)))
    (memory_multi_pointer_locations (entry_temps s) (multi_pointer_region_window package))).
Definition memory_multi_pointer_runtime_domain source (package : memory_multi_pointer_region_package source) s :=
  memory_recursive_guard_domain (multi_pointer_region_limit package) [] (multi_pointer_region_nest package) s /\
  (memory_recursive_guard_accept (multi_pointer_region_limit package) [] (multi_pointer_region_nest package) s = true ->
    Forall (memory_cell_capable (memory_multi_pointer_locations (entry_temps s) (multi_pointer_region_window package))
      (entry_memory s)) (memory_multi_pointer_runtime_footprint package (entry_temps s))).

Theorem memory_multi_pointer_source_runtime_domain source (package : memory_multi_pointer_region_package source)
  fe ge locals temps memory after final :
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  memory_multi_pointer_runtime_domain package (Entry ge locals temps memory).
Proof.
  intro SOURCE.
  pose proof (@memory_multi_pointer_region_source_domain source package fe ge locals temps memory after final SOURCE) as DOMAIN.
  split; [exact DOMAIN|]; intro ACCEPT.
  destruct (@memory_recursive_guard_sound (multi_pointer_region_limit package) [] (multi_pointer_region_nest package)
    (Entry ge locals temps memory) (proj2 (multi_pointer_region_cap (multi_pointer_region_syntax package))) DOMAIN ACCEPT)
    as [INITIAL [RANGES ALIAS]].
  destruct (@memory_multi_pointer_source_under_ranges source package fe ge locals temps memory after final INITIAL RANGES SOURCE)
    as [SCALARS [LOOP EXIT]].
  pose proof (@memory_loop_source_capabilities _ _
    (RuntimeState (memory_multi_pointer_locations temps (multi_pointer_region_window package)) memory)
    (RuntimeState (memory_multi_pointer_locations temps (multi_pointer_region_window package)) final)
    (memory_multi_pointer_locations_int32 temps (multi_pointer_region_window package)) LOOP) as CAPABLE.
  unfold memory_multi_pointer_runtime_footprint,memory_multi_pointer_runtime_context,memory_multi_pointer_runtime_loop.
  unfold memory_recursive_parameters; rewrite map_app.
  apply Forall_forall; intros cell MEMBER.
  unfold memory_events_footprint in MEMBER; apply in_flat_map in MEMBER as [event [EVENT ACCESS]].
  apply Forall_forall with (x := event) in CAPABLE; [|exact EVENT].
  apply Forall_forall with (x := cell) in CAPABLE; [exact CAPABLE|exact ACCESS].
Qed.

Section CANDIDATE.
Variable source : statement.
Variable package : memory_multi_pointer_region_package source.
Let nest := multi_pointer_region_nest package.
Let cap := multi_pointer_region_limit package.
Let pointers := multi_pointer_region_pointers package.
Let extent := multi_pointer_region_window package.
Let scalars := multi_pointer_region_scalars package.
Let context := memory_nest_bounds nest++scalars.
Let dimensions := length (memory_nest_iterators nest).
Let instructions := memory_multi_pointer_region_instructions package.
Variable live : list ident.
Variable pool : list (ident*ident).
Variable candidate : L.stmt.
Variable code : statement.
Hypothesis COMPILE : compile_memory_multi_pointer_buffer_loop pointers context (memory_scalar_pointer_static_bounds dimensions cap (length scalars)) live pool candidate = Some code.
Hypothesis CANDIDATE : memory_scalar_candidate_certificate dimensions cap (length scalars) instructions context candidate.

Theorem memory_multi_pointer_projected_candidate_local fe ge locals le memory after final :
  memory_recursive_guard_accept cap [] nest (Entry ge locals le memory) = true ->
  locations_nonalias (memory_restrict_locations
    (memory_footprint_allowed (memory_multi_pointer_runtime_footprint package le))
    (memory_multi_pointer_locations le extent)) ->
  exec_stmt fe ge locals le memory source E0 after final Out_normal ->
  exists target, exec_stmt fe ge locals le memory (memory_recursive_candidate code nest) E0 target final Out_normal /\ temp_agree live after target.
Proof.
  intros COUNTS SEPARATED SOURCE.
  pose proof (@memory_multi_pointer_region_source_domain source package fe ge locals le memory after final SOURCE) as DOMAIN.
  pose proof (proj2 (multi_pointer_region_cap (multi_pointer_region_syntax package))) as CAP.
  destruct (@memory_recursive_guard_sound cap [] nest (Entry ge locals le memory) CAP DOMAIN COUNTS) as [INITIAL [RANGES ALIAS]].
  destruct (@memory_multi_pointer_source_under_ranges source package fe ge locals le memory after final INITIAL RANGES SOURCE)
    as [SCALAR_BINDINGS [LOOP EXIT]].
  fold nest scalars pointers extent instructions in LOOP.
  assert (PARAMETERS : memory_recursive_parameters (memory_nest_bounds nest) le++memory_recursive_parameters scalars le =
    memory_recursive_parameters context le) by (unfold context,memory_recursive_parameters; rewrite map_app; reflexivity).
  rewrite PARAMETERS in LOOP.
  change (L.loop_semantics (memory_scalar_rectangle 0 dimensions (length scalars) instructions)
    (memory_recursive_parameters context le)
    (RuntimeState (memory_multi_pointer_locations le extent) memory)
    (RuntimeState (memory_multi_pointer_locations le extent) final)) in LOOP.
  assert (VIEW : MemoryNested.A.typed_view context (memory_recursive_parameters context le) le).
  { change (MemoryNested.A.typed_view context (memory_source_parameter_values context (Entry ge locals le memory)) le).
    apply (@memory_source_parameter_view context (Entry ge locals le memory)); intros identifier MEMBER.
    unfold context in MEMBER; apply in_app_or in MEMBER as [MEMBER|MEMBER].
    - apply Forall_forall with (x := identifier) in RANGES; [exact (proj1 RANGES)|exact MEMBER].
    - eapply memory_scalar_bindings_typed; [exact SCALAR_BINDINGS|exact MEMBER]. }
  assert (WITHIN : MemoryNested.A.env_within (memory_scalar_static_bounds dimensions cap (length scalars))
    (memory_recursive_parameters context le)).
  { unfold dimensions; rewrite memory_nest_lengths.
    pose proof (@memory_scalar_validator_count_scalar_ranges cap (memory_nest_bounds nest)
      (memory_recursive_parameters scalars le) ge locals le memory RANGES (memory_recursive_scalar_values_range scalars le)) as FACT.
    unfold memory_recursive_parameters in FACT; rewrite length_map in FACT.
    unfold context,memory_recursive_parameters; rewrite map_app; exact FACT. }
  assert (POINTER_WITHIN : MemoryFramedNested.N.A.env_within (memory_scalar_pointer_static_bounds dimensions cap (length scalars))
    (memory_recursive_parameters context le)).
  { unfold dimensions; rewrite memory_nest_lengths.
    pose proof (@memory_scalar_encoder_count_scalar_ranges cap (memory_nest_bounds nest)
      (memory_recursive_parameters scalars le) ge locals le memory RANGES (memory_recursive_scalar_values_range scalars le)) as FACT.
    unfold memory_recursive_parameters in FACT; rewrite length_map in FACT.
    unfold context,memory_recursive_parameters; rewrite map_app; exact FACT. }
  pose proof (multi_pointer_region_extent (multi_pointer_region_syntax package)) as WINDOW.
  set (selected := memory_multi_pointer_runtime_footprint package le).
  set (allowed := memory_footprint_allowed selected).
  set (restricted := memory_restrict_locations allowed (memory_multi_pointer_locations le extent)).
  assert (NONALIAS : GuardMemoryInstr.NonAlias (RuntimeState restricted memory)) by exact SEPARATED.
  assert (COVERED : memory_loop_cells_covered allowed (memory_scalar_rectangle 0 dimensions (length scalars) instructions)
    (memory_recursive_parameters context le)).
  { unfold allowed,selected,memory_multi_pointer_runtime_footprint,memory_multi_pointer_runtime_loop.
    fold nest scalars pointers extent instructions dimensions context.
    apply memory_loop_own_footprint_covered. }
  assert (RESTRICTED : L.loop_semantics (memory_scalar_rectangle 0 dimensions (length scalars) instructions)
    (memory_recursive_parameters context le) (RuntimeState restricted memory) (RuntimeState restricted final)).
  { change (L.loop_semantics (memory_scalar_rectangle 0 dimensions (length scalars) instructions)
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
    context (memory_scalar_pointer_static_bounds dimensions cap (length scalars)) live pool candidate code (memory_recursive_parameters context le) le
    (RuntimeState (memory_multi_pointer_locations le extent) memory) (RuntimeState (memory_multi_pointer_locations le extent) final) memory
    COMPILE VIEW POINTER_WITHIN TARGET eq_refl (temp_agree_refl pointers le))
    as [private_temps [private_memory [MEMORY [POINTER_FINAL [FRAME EXEC]]]]].
  unfold memory_multi_pointer_buffer_view in MEMORY; inversion MEMORY; subst private_memory.
  assert (PUBLIC : temp_agree (context++live) le private_temps).
  { eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER.
    apply in_app_or in MEMBER as [MEMBER|MEMBER]; apply in_or_app; [left; exact MEMBER|right; apply in_or_app; right; exact MEMBER]. }
  exists (memory_recursive_exit nest private_temps); split.
  - unfold memory_recursive_candidate; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact EXEC|].
    apply memory_recursive_restore_execution; [exact (multi_pointer_region_fresh (multi_pointer_region_syntax package))|].
    intros identifier MEMBER; destruct (@memory_source_typed_word context (memory_recursive_parameters context le) le identifier VIEW ltac:(unfold context; apply in_or_app; left; exact MEMBER)) as [word WORD].
    exists word; cbn [entry_temps]; rewrite PUBLIC by
      (apply in_or_app; left; unfold context; apply in_or_app; left; exact MEMBER); exact WORD.
  - rewrite EXIT; apply memory_recursive_exit_frame; intros identifier MEMBER.
    apply PUBLIC; unfold context; apply in_app_or in MEMBER as [MEMBER|MEMBER];
      [apply in_or_app; left; apply in_or_app; left|apply in_or_app; right]; exact MEMBER.
Qed.
Definition memory_multi_pointer_projected_candidate_rule :
  memory_projected_private_rule live source (memory_recursive_candidate code nest).
Proof.
  pose proof (multi_pointer_region_syntax package) as CERT.
  assert (WRITES : writes_only (memory_nest_iterators nest) source).
  { rewrite (multi_pointer_region_source CERT); apply memory_nest_source_writes; [exact (multi_pointer_region_shapes CERT)|].
    apply memory_pointer_sequence_writes with (operations := multi_pointer_region_code package); exact (multi_pointer_region_body CERT). }
  refine {| projected_rule_writes := memory_nest_iterators nest; projected_rule_source_writes := WRITES;
    projected_rule_domain := memory_multi_pointer_runtime_domain package;
    projected_rule_presumption := memory_multi_pointer_runtime_presumption package |}.
  - intros temps p locals le memory after final RUN.
    exact (@memory_multi_pointer_source_runtime_domain source package (adapter_entry temps) (globalenv p) locals le memory after final RUN).
  - intros temps p locals le memory after final SCOPE RUN [COUNTS NONALIAS].
    destruct (@memory_multi_pointer_projected_candidate_local (adapter_entry temps) (globalenv p) locals le memory after final
      COUNTS NONALIAS RUN) as [target [EXEC FRAME]].
    exists target,final; split; [exact EXEC|split; [exact FRAME|apply memory_equivalent_refl]].
Defined.
End CANDIDATE.
Print Assumptions memory_multi_pointer_source_runtime_domain.
Print Assumptions memory_multi_pointer_projected_candidate_rule.
