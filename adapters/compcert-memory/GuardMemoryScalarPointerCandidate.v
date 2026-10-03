From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import AbstractGuard SemanticFacts CompCertMemoryEquivalence ClightGuard ClightCondition ClightNoWrap
  ClightTempFrame ClightPrivateRule ClightProjectedExecution ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryRecursiveSource GuardMemoryRecursiveSyntax GuardMemoryRecursiveGuard GuardMemoryRecursiveDomain
  GuardMemoryRecursiveRestore GuardMemoryRecursiveChecker GuardMemoryRecursiveCandidate GuardMemoryParametricGuard GuardMemoryParametricSourceDomain
  GuardMemoryScalarPointerSyntax GuardMemoryScalarPointerDomain GuardMemoryScalarChecker GuardMemoryScalarPointerBounds GuardMemoryScalarLoops GuardMemoryPointerSequence GuardMemoryPointerBackend GuardMemoryBufferOffsets.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section CANDIDATE.
Variable source : statement.
Variable package : memory_scalar_pointer_region_package source.
Let nest := scalar_pointer_region_nest package.
Let cap := scalar_pointer_region_limit package.
Let pointer := scalar_pointer_region_pointer package.
Let extent := scalar_pointer_region_window package.
Let scalars := scalar_pointer_region_scalars package.
Let context := memory_nest_bounds nest++scalars.
Let dimensions := length (memory_nest_iterators nest).
Let instructions := memory_scalar_pointer_region_instructions package.
Variable live : list ident.
Variable pool : list (ident*ident).
Variable candidate : L.stmt.
Variable code : statement.
Hypothesis COMPILE : compile_memory_pointer_buffer_loop pointer pointer context (memory_scalar_pointer_static_bounds dimensions cap (length scalars)) live pool candidate = Some code.
Hypothesis CANDIDATE : memory_scalar_candidate_certificate dimensions cap (length scalars) instructions context candidate.

Theorem memory_scalar_pointer_candidate_local fe ge locals le memory after final :
  memory_recursive_guard_accept cap [] nest (Entry ge locals le memory) = true ->
  exec_stmt fe ge locals le memory source E0 after final Out_normal ->
  exists target, exec_stmt fe ge locals le memory (memory_recursive_candidate code nest) E0 target final Out_normal /\ temp_agree live after target.
Proof.
  intros ACCEPT SOURCE.
  pose proof (@memory_scalar_pointer_region_source_domain source package fe ge locals le memory after final SOURCE) as DOMAIN.
  pose proof (proj2 (scalar_pointer_region_cap (scalar_pointer_region_syntax package))) as CAP.
  destruct (@memory_recursive_guard_sound cap [] nest (Entry ge locals le memory) CAP DOMAIN ACCEPT) as [INITIAL [RANGES ALIAS]].
  destruct (@memory_scalar_pointer_source_under_ranges source package fe ge locals le memory after final INITIAL RANGES SOURCE)
    as [block [base [POINTER [SCALAR_BINDINGS [LOOP EXIT]]]]].
  fold nest scalars pointer extent instructions in LOOP.
  assert (PARAMETERS : memory_recursive_parameters (memory_nest_bounds nest) le++memory_recursive_parameters scalars le =
    memory_recursive_parameters context le) by (unfold context,memory_recursive_parameters; rewrite map_app; reflexivity).
  rewrite PARAMETERS in LOOP.
  change (L.loop_semantics (memory_scalar_rectangle 0 dimensions (length scalars) instructions)
    (memory_recursive_parameters context le)
    (RuntimeState (memory_pointer_buffer_locations pointer block base extent) memory)
    (RuntimeState (memory_pointer_buffer_locations pointer block base extent) final)) in LOOP.
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
  pose proof (scalar_pointer_region_extent (scalar_pointer_region_syntax package)) as WINDOW.
  assert (NONALIAS : GuardMemoryInstr.NonAlias (RuntimeState (memory_pointer_buffer_locations pointer block base extent) memory))
    by (apply memory_pointer_buffer_locations_nonalias; exact (proj2 (proj2 WINDOW))).
  pose proof (@CANDIDATE (memory_recursive_parameters context le)
    (RuntimeState (memory_pointer_buffer_locations pointer block base extent) memory)
    (RuntimeState (memory_pointer_buffer_locations pointer block base extent) final)
    ltac:(unfold memory_recursive_parameters; apply length_map) WITHIN NONALIAS LOOP) as TARGET.
  destruct (@compile_memory_pointer_buffer_loop_correct extent (proj1 (proj2 WINDOW)) fe ge locals pointer pointer block base
    context (memory_scalar_pointer_static_bounds dimensions cap (length scalars)) live pool candidate code (memory_recursive_parameters context le) le
    (RuntimeState (memory_pointer_buffer_locations pointer block base extent) memory)
    (RuntimeState (memory_pointer_buffer_locations pointer block base extent) final) memory
    COMPILE VIEW POINTER_WITHIN TARGET eq_refl POINTER) as [private_temps [private_memory [MEMORY [POINTER_FINAL [FRAME EXEC]]]]].
  unfold memory_pointer_buffer_view in MEMORY; inversion MEMORY; subst private_memory.
  assert (PUBLIC : temp_agree (context++live) le private_temps).
  { eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER.
    apply in_app_or in MEMBER as [MEMBER|MEMBER]; apply in_or_app; [left; exact MEMBER|right; cbn; auto]. }
  exists (memory_recursive_exit nest private_temps); split.
  - unfold memory_recursive_candidate; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact EXEC|].
    apply memory_recursive_restore_execution; [exact (scalar_pointer_region_fresh (scalar_pointer_region_syntax package))|].
    intros identifier MEMBER; destruct (@memory_source_typed_word context (memory_recursive_parameters context le) le identifier VIEW ltac:(unfold context; apply in_or_app; left; exact MEMBER)) as [word WORD].
    exists word; cbn [entry_temps]; rewrite PUBLIC by
      (apply in_or_app; left; unfold context; apply in_or_app; left; exact MEMBER); exact WORD.
  - rewrite EXIT; apply memory_recursive_exit_frame; intros identifier MEMBER.
    apply PUBLIC; unfold context; apply in_app_or in MEMBER as [MEMBER|MEMBER];
      [apply in_or_app; left; apply in_or_app; left|apply in_or_app; right]; exact MEMBER.
Qed.
Definition memory_scalar_pointer_candidate_rule : encoded_private_rule live source (memory_recursive_candidate code nest).
Proof.
  pose proof (scalar_pointer_region_syntax package) as CERT.
  assert (WRITES : writes_only (memory_nest_iterators nest) source).
  { rewrite (scalar_pointer_region_source CERT); apply memory_nest_source_writes; [exact (scalar_pointer_region_shapes CERT)|].
    apply memory_pointer_sequence_writes with (operations := scalar_pointer_region_code package); exact (scalar_pointer_region_body CERT). }
  refine {| private_rule_writes := memory_nest_iterators nest; private_rule_source_writes := WRITES;
    private_rule_atoms := unit; private_rule_domain := memory_recursive_guard_domain cap [] nest;
    private_rule_dimension := memory_recursive_guard_dimension cap [] nest;
    private_rule_primitives := memory_recursive_guard_primitives cap [] nest; private_rule_formula := Fact tt |}.
  - intros temps p locals le memory after final RUN.
    exact (@memory_scalar_pointer_region_source_domain source package (adapter_entry temps) (globalenv p) locals le memory after final RUN).
  - intros temps p locals le memory after final SCOPE RUN ACCEPT.
    destruct (@memory_scalar_pointer_candidate_local (adapter_entry temps) (globalenv p) locals le memory after final ACCEPT RUN) as [target [EXEC FRAME]].
    exists target,final; split; [exact EXEC|split; [exact FRAME|apply memory_equivalent_refl]].
Defined.
End CANDIDATE.
Print Assumptions memory_scalar_pointer_candidate_local.
Print Assumptions memory_scalar_pointer_candidate_rule.
