From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import AbstractGuard SemanticFacts CompCertMemoryEquivalence ClightGuard ClightCondition ClightNoWrap
  ClightTempFrame ClightStraightLine ClightLoopSyntax ClightRegionProgress ClightPrivateRule
  ClightProjectedExecution ClightTempFootprint ClightRedundantSet ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryMultipleArrays GuardMemoryRegistryBackend GuardMemoryRegistryGuard GuardMemoryNaryBodyModel
  GuardMemoryParametricGuard GuardMemoryParametricSourceDomain GuardMemoryNaryLoops GuardMemoryRecursiveSource
  GuardMemoryRecursiveSyntax GuardMemoryRecursiveGuard GuardMemoryRecursiveDomain GuardMemoryRecursiveRestore GuardMemoryRecursiveChecker.
From GuardMemory Require Import GuardMemoryRecursiveCandidate GuardMemoryScalarArraySyntax GuardMemoryScalarArrayDomain
  GuardMemoryScalarPointerBounds GuardMemoryScalarChecker GuardMemoryScalarLoops GuardMemoryNarySequence.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section CANDIDATE.
Variable source : statement.
Variable package : memory_scalar_array_region_package source.
Let nest := scalar_array_region_nest package.
Let cap := scalar_array_region_limit package.
Let scalars := scalar_array_region_scalars package.
Let context := memory_nest_bounds nest++scalars.
Let scalar_count := length scalars.
Let dimensions := length (memory_nest_iterators nest).
Let descriptors := memory_scalar_array_region_descriptors package.
Let instructions := memory_scalar_array_region_instructions package.
Variable live : list ident.
Variable pool : list (ident*ident).
Variable candidate : L.stmt.
Variable code : statement.
Hypothesis COMPILE : compile_memory_registry_loop descriptors context (memory_scalar_static_bounds dimensions cap scalar_count) live pool candidate = Some code.
Hypothesis CANDIDATE : memory_scalar_candidate_certificate dimensions cap scalar_count instructions context candidate.

Theorem memory_scalar_array_candidate_local fe ge locals le memory after final :
  memory_recursive_guard_accept cap descriptors nest (Entry ge locals le memory) = true ->
  exec_stmt fe ge locals le memory source E0 after final Out_normal ->
  exists target, exec_stmt fe ge locals le memory (memory_recursive_candidate code nest) E0 target final Out_normal /\
    temp_agree live after target.
Proof.
  intros ACCEPT SOURCE.
  pose proof (@memory_scalar_array_region_source_domain source package fe ge locals le memory after final SOURCE) as DOMAIN.
  pose proof (proj2 (scalar_array_region_cap (scalar_array_region_syntax package))) as CAP.
  destruct (@memory_recursive_guard_sound cap descriptors nest (Entry ge locals le memory) CAP DOMAIN ACCEPT)
    as [INITIAL [RANGES ALIAS]].
  destruct (@memory_scalar_array_source_under_ranges source package fe ge locals le memory after final INITIAL RANGES SOURCE)
    as [entries [ARRAYS [UNIQUE [POINTERS [SCALARS [LOOP EXIT]]]]]].
  fold nest scalars descriptors instructions in LOOP,SCALARS,ARRAYS.
  assert (PARAMETERS : memory_recursive_parameters (memory_nest_bounds nest) le++memory_recursive_parameters scalars le =
    memory_recursive_parameters context le) by (unfold memory_recursive_parameters,context; rewrite map_app; reflexivity).
  rewrite PARAMETERS in LOOP.
  assert (VIEW : MemoryNested.A.typed_view context (memory_recursive_parameters context le) le).
  { change (MemoryNested.A.typed_view context (memory_source_parameter_values context (Entry ge locals le memory)) le).
    apply (@memory_source_parameter_view context (Entry ge locals le memory)); intros identifier MEMBER.
    unfold context in MEMBER; apply in_app_or in MEMBER as [MEMBER|MEMBER].
    - apply Forall_forall with (x := identifier) in RANGES; [exact (proj1 RANGES)|exact MEMBER].
    - eapply memory_scalar_bindings_typed; eassumption. }
  assert (WITHIN : MemoryNested.A.env_within (memory_scalar_static_bounds dimensions cap scalar_count) (memory_recursive_parameters context le)).
  { pose proof (@memory_scalar_validator_count_scalar_ranges cap (memory_nest_bounds nest)
      (memory_recursive_parameters scalars le) ge locals le memory RANGES (memory_recursive_scalar_values_range scalars le)) as WITHIN.
    unfold memory_recursive_parameters in WITHIN; rewrite <- map_app,length_map in WITHIN.
    change (MemoryNested.A.env_within (memory_scalar_static_bounds (length (memory_nest_bounds nest)) cap scalar_count)
      (memory_recursive_parameters context le)) in WITHIN.
    unfold dimensions; rewrite memory_nest_lengths; exact WITHIN. }
  destruct ALIAS as [other [OTHER BLOCKS]].
  assert (SAME : map memory_array_block entries = map memory_array_block other).
  { rewrite <- (@memory_descriptor_blocks_binding descriptors entries (Entry ge locals le memory) ARRAYS).
    rewrite <- (@memory_descriptor_blocks_binding descriptors other (Entry ge locals le memory) OTHER); reflexivity. }
  assert (NONALIAS : GuardMemoryInstr.NonAlias (RuntimeState (memory_array_registry entries) memory))
    by (apply memory_array_registry_nonalias; rewrite SAME; exact BLOCKS).
  pose proof (@CANDIDATE (memory_recursive_parameters context le) (RuntimeState (memory_array_registry entries) memory)
    (RuntimeState (memory_array_registry entries) final) ltac:(unfold memory_recursive_parameters; apply length_map) WITHIN NONALIAS LOOP) as TARGET.
  destruct (@compile_memory_registry_loop_correct descriptors entries fe ge locals ARRAYS context
    (memory_scalar_static_bounds dimensions cap scalar_count) live pool candidate code (memory_recursive_parameters context le) le
    (RuntimeState (memory_array_registry entries) memory) (RuntimeState (memory_array_registry entries) final) memory
    COMPILE VIEW WITHIN TARGET eq_refl) as [private_temps [private_memory [MEMORY [FRAME EXEC]]]].
  unfold memory_registry_view in MEMORY; inversion MEMORY; subst private_memory.
  exists (memory_recursive_exit nest private_temps); split.
  - unfold memory_recursive_candidate; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact EXEC|].
    apply memory_recursive_restore_execution; [exact (scalar_array_region_fresh (scalar_array_region_syntax package))|].
    intros identifier MEMBER; destruct (@memory_source_typed_word context (memory_recursive_parameters context le) le identifier VIEW ltac:(unfold context; apply in_or_app; left; exact MEMBER)) as [word WORD].
    exists word; cbn [entry_temps]; rewrite FRAME by (apply in_or_app; left; unfold context; apply in_or_app; left; exact MEMBER); exact WORD.
  - rewrite EXIT; apply memory_recursive_exit_frame; intros identifier MEMBER.
    apply FRAME; apply in_app_or in MEMBER as [MEMBER|MEMBER].
    + apply in_or_app; left; unfold context; apply in_or_app; left; exact MEMBER.
    + apply in_or_app; right; exact MEMBER.
Qed.
Definition memory_scalar_array_candidate_rule : encoded_private_rule live source (memory_recursive_candidate code nest).
Proof.
  pose proof (scalar_array_region_syntax package) as CERT.
  assert (WRITES : writes_only (memory_nest_iterators nest) source).
  { rewrite (scalar_array_region_source CERT).
    apply memory_nest_source_writes; [exact (scalar_array_region_shapes CERT)|exact (@memory_nary_compute_sequence_writes (scalar_array_region_code package) (memory_nest_leaf nest) (scalar_array_region_body CERT))]. }
  refine {| private_rule_writes := memory_nest_iterators nest; private_rule_source_writes := WRITES;
    private_rule_atoms := unit;
    private_rule_domain := memory_recursive_guard_domain cap descriptors nest;
    private_rule_dimension := memory_recursive_guard_dimension cap descriptors nest;
    private_rule_primitives := memory_recursive_guard_primitives cap descriptors nest;
    private_rule_formula := Fact tt |}.
  - intros temps p locals le memory after final RUN.
    exact (@memory_scalar_array_region_source_domain source package (adapter_entry temps) (globalenv p) locals le memory after final RUN).
  - intros temps p locals le memory after final SCOPE RUN ACCEPT.
    destruct (@memory_scalar_array_candidate_local (adapter_entry temps) (globalenv p) locals le memory after final ACCEPT RUN) as [target [EXEC FRAME]].
    exists target,final; split; [exact EXEC|split; [exact FRAME|apply memory_equivalent_refl]].
Defined.
End CANDIDATE.
Print Assumptions memory_scalar_array_candidate_local.
Print Assumptions memory_scalar_array_candidate_rule.
