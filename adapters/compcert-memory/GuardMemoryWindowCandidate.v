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
From polcert.src Require Import PolyBase.
From GuardMemory Require Import GuardMemoryMultiPointerIdentifiers.
From GuardMemory Require Import GuardMemoryWindowSyntax GuardMemoryWindowPackage GuardMemoryWindowStartedPackage GuardMemoryWindowPackageHeader GuardMemoryWindowPackageBounds GuardMemoryWindowSourceDomain GuardMemoryWindowSingleRegistry GuardMemoryWindowSingleFootprint GuardMemoryWindowCells GuardMemoryWindowBackend.
Section WINDOW_CANDIDATE.
Variable source : statement.
Variable package : window_started_package source.
Let base := window_started_base package.
Let nest := window_region_nest base.
Let pointers := window_region_pointers base.
Let lower := window_region_lower base.
Let upper := window_region_upper base.
Let parameters := window_region_parameters base.
Let scalars := window_region_scalars base.
Let context := window_package_context package.
Let source_loop := window_package_loop package.
Variable pointer : ident.
Hypothesis SINGLE : pointers = [pointer].
Variable live : list ident.
Variable pool : list (ident*ident).
Variable candidate : L.stmt.
Variable code : statement.
Hypothesis COMPILE : compile_window_multi_pointer_buffer_loop pointers context (window_package_pointer_bounds package) live pool candidate = Some code.
Hypothesis CANDIDATE : memory_bounded_source_certificate (window_package_static_bounds package) source_loop context candidate.
Theorem window_single_candidate_local fe ge locals le memory after final :
  window_package_header_accept package (Entry ge locals le memory) = true ->
  exec_stmt fe ge locals le memory source E0 after final Out_normal ->
  exists target, exec_stmt fe ge locals le memory (memory_recursive_candidate code nest) E0 target final Out_normal /\ temp_agree live after target.
Proof.
  intros ACCEPT SOURCE.
  pose proof (@window_package_source_header_domain source package fe ge locals le memory after final SOURCE) as DOMAIN.
  destruct (window_package_header_sound DOMAIN ACCEPT) as [ACTIVE [ROOT [RANGES PARAM_RANGES]]].
  destruct (@window_source_under_ranges source base (window_started_iterator package) (window_started_bound package)
    (window_started_body package) (window_started_child package) fe ge locals le memory after final
    (window_started_nest package) ACTIVE RANGES PARAM_RANGES SOURCE) as [PARAM_BINDINGS [SCALAR_BINDINGS [LOOP EXIT]]].
  assert (PARAMETERS : memory_recursive_parameters (memory_nest_bounds nest) le++
    (memory_recursive_parameters parameters le++memory_recursive_parameters scalars le)++[Int.signed (temp_word (window_started_iterator package) le)] =
    memory_recursive_parameters context le).
  { unfold context,window_package_context,nest,parameters,scalars,base,memory_recursive_parameters.
    rewrite !map_app; cbn [map]; repeat rewrite <-app_assoc; reflexivity. }
  fold nest parameters scalars in LOOP,PARAM_BINDINGS,SCALAR_BINDINGS,PARAM_RANGES.
  rewrite PARAMETERS in LOOP.
  change (L.loop_semantics source_loop (memory_recursive_parameters context le)
    (RuntimeState (window_multi_pointer_locations le lower upper) memory)
    (RuntimeState (window_multi_pointer_locations le lower upper) final)) in LOOP.
  assert (VIEW : MemoryNested.A.typed_view context (memory_recursive_parameters context le) le).
  { change (MemoryNested.A.typed_view context (memory_source_parameter_values context (Entry ge locals le memory)) le).
    apply memory_source_parameter_view; intros identifier MEMBER.
    unfold context,window_package_context in MEMBER; repeat rewrite in_app_iff in MEMBER.
    destruct MEMBER as [MEMBER|[MEMBER|[MEMBER|MEMBER]]].
    - eapply memory_vector_bounds_typed; [exact RANGES|exact MEMBER].
    - eapply memory_scalar_bindings_typed; [exact PARAM_BINDINGS|exact MEMBER].
    - eapply memory_scalar_bindings_typed; [exact SCALAR_BINDINGS|exact MEMBER].
    - cbn in MEMBER; destruct MEMBER as [<-|[]]; exact (proj1 (proj1 DOMAIN)). }
  set (allowed := fun cell => Pos.eqb (arr_id cell) pointer).
  set (restricted := window_single_locations pointer le lower upper).
  pose proof (window_region_certificate base) as CERT.
  assert (NONALIAS : GuardMemoryInstr.NonAlias (RuntimeState restricted memory)).
  { apply window_single_locations_nonalias; exact (proj2 (proj2 (proj2 (window_source_window CERT)))). }
  assert (COVERED : memory_loop_cells_covered allowed source_loop (memory_recursive_parameters context le)).
  { unfold allowed,source_loop,window_package_loop,window_region_instructions.
    apply window_started_scalar_single_covered.
    pose proof (window_source_covered CERT) as OWNED; change (Forall (memory_multi_pointer_operation_covered pointers) (window_region_operations base)) in OWNED.
    rewrite SINGLE in OWNED; exact OWNED. }
  assert (RESTRICTED : L.loop_semantics source_loop (memory_recursive_parameters context le)
    (RuntimeState restricted memory) (RuntimeState restricted final)).
  { change (L.loop_semantics source_loop (memory_recursive_parameters context le)
      (memory_restrict_state allowed (RuntimeState (window_multi_pointer_locations le lower upper) memory))
      (memory_restrict_state allowed (RuntimeState (window_multi_pointer_locations le lower upper) final))).
    eapply memory_restrict_loop_execution; [exact COVERED|exact LOOP]. }
  pose proof (@CANDIDATE (memory_recursive_parameters context le) (RuntimeState restricted memory) (RuntimeState restricted final)
    ltac:(unfold memory_recursive_parameters; apply length_map) (window_package_validator_within DOMAIN ACCEPT) NONALIAS RESTRICTED) as VALIDATED.
  assert (TARGET : L.loop_semantics candidate (memory_recursive_parameters context le)
    (RuntimeState (window_multi_pointer_locations le lower upper) memory)
    (RuntimeState (window_multi_pointer_locations le lower upper) final))
    by (eapply memory_unrestrict_loop_execution; exact VALIDATED).
  destruct (@compile_window_multi_pointer_buffer_loop_correct le lower upper (proj1 (proj2 (window_source_window CERT)))
    (proj1 (proj2 (proj2 (window_source_window CERT)))) fe ge locals pointers context (window_package_pointer_bounds package)
    live pool candidate code (memory_recursive_parameters context le) le
    (RuntimeState (window_multi_pointer_locations le lower upper) memory) (RuntimeState (window_multi_pointer_locations le lower upper) final)
    memory COMPILE VIEW (window_package_encoder_within DOMAIN ACCEPT) TARGET eq_refl (temp_agree_refl pointers le))
    as [private_temps [private_memory [MEMORY [POINTER_FINAL [FRAME EXEC]]]]].
  unfold window_multi_pointer_buffer_view in MEMORY; inversion MEMORY; subst private_memory.
  assert (PUBLIC : temp_agree (context++live) le private_temps).
  { eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER.
    apply in_app_or in MEMBER as [MEMBER|MEMBER]; apply in_or_app; [left; exact MEMBER|right; apply in_or_app; right; exact MEMBER]. }
  assert (BOUNDS_IN_CONTEXT : forall identifier, In identifier (memory_nest_bounds nest) -> In identifier context).
  { intros identifier MEMBER; unfold context,window_package_context; apply in_or_app; left; exact MEMBER. }
  exists (memory_recursive_exit nest private_temps); split.
  - unfold memory_recursive_candidate; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact EXEC|].
    apply memory_recursive_restore_execution; [exact (window_source_fresh CERT)|].
    intros identifier MEMBER; destruct (@memory_source_typed_word context (memory_recursive_parameters context le) le identifier VIEW
      (BOUNDS_IN_CONTEXT identifier MEMBER)) as [word WORD].
    exists word; cbn [entry_temps]; rewrite PUBLIC by (apply in_or_app; left; apply BOUNDS_IN_CONTEXT; exact MEMBER); exact WORD.
  - rewrite EXIT; apply memory_recursive_exit_frame; intros identifier MEMBER.
    apply PUBLIC; apply in_app_or in MEMBER as [MEMBER|MEMBER].
    + apply in_or_app; left; apply BOUNDS_IN_CONTEXT; exact MEMBER.
    + apply in_or_app; right; exact MEMBER.
Qed.
Definition window_single_candidate_rule :
  memory_projected_private_rule live source (memory_recursive_candidate code nest).
Proof.
  pose proof (window_region_certificate base) as CERT.
  assert (WRITES : writes_only (memory_nest_iterators nest) source).
  { rewrite (window_source_exact CERT); apply memory_nest_source_writes; [exact (window_source_shapes CERT)|].
    apply memory_pointer_sequence_writes with (operations := window_region_operations base); exact (window_source_body CERT). }
  refine {| projected_rule_writes := memory_nest_iterators nest; projected_rule_source_writes := WRITES;
    projected_rule_domain := window_package_header_domain package;
    projected_rule_presumption := fun s => window_package_header_accept package s = true |}.
  - intros temps p locals le memory after final RUN.
    exact (@window_package_source_header_domain source package (adapter_entry temps) (globalenv p) locals le memory after final RUN).
  - intros temps p locals le memory after final SCOPE RUN ACCEPT.
    destruct (@window_single_candidate_local (adapter_entry temps) (globalenv p) locals le memory after final ACCEPT RUN)
      as [target [EXEC FRAME]].
    exists target,final; split; [exact EXEC|split; [exact FRAME|apply memory_equivalent_refl]].
Defined.
End WINDOW_CANDIDATE.
Print Assumptions window_single_candidate_local.
Print Assumptions window_single_candidate_rule.
