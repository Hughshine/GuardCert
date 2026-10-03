From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import AbstractGuard SemanticFacts CompCertMemoryEquivalence ClightGuard ClightCondition ClightNoWrap
  ClightTempFrame ClightStraightLine ClightLoopSyntax ClightRegionProgress ClightFrontendLoopProtocol ClightCountedLoop
  ClightPrivateRule ClightProjectedExecution ClightTempFootprint.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryMultipleArrays GuardMemoryRegistryBackend GuardMemoryRegistryGuard GuardMemoryNaryBodyModel
  GuardMemoryParametricGuard GuardMemoryParametricSourceDomain GuardMemoryNaryLoops GuardMemoryTripleSource
  GuardMemoryTripleSyntax GuardMemoryTripleGuard GuardMemoryTripleDomain GuardMemoryTripleRestore GuardMemoryTripleChecker.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_triple_candidate code d := Ssequence code (memory_triple_restore d).
Section CANDIDATE.
Variable source : statement.
Variable package : memory_triple_region_package source.
Let d := triple_region_description package.
Let context := memory_triple_context d.
Let descriptors := memory_triple_region_descriptors package.
Let instructions := memory_triple_region_instructions package.
Variable live : list ident.
Variable pool : list (ident*ident).
Variable candidate : L.stmt.
Variable code : statement.
Hypothesis COMPILE : compile_memory_registry_loop descriptors context (memory_triple_bounds (triple_cap d)) live pool candidate = Some code.
Hypothesis CANDIDATE : memory_triple_candidate_certificate (triple_cap d) instructions context candidate.

Theorem memory_triple_candidate_local fe ge locals le memory after final :
  memory_triple_guard_accept (triple_cap d) descriptors (triple_row d) (triple_row_bound d)
    (triple_column_bound d) (triple_depth_bound d) (Entry ge locals le memory) = true ->
  exec_stmt fe ge locals le memory source E0 after final Out_normal ->
  exists target, exec_stmt fe ge locals le memory (memory_triple_candidate code d) E0 target final Out_normal /\
    temp_agree live after target.
Proof.
  intros ACCEPT SOURCE.
  pose proof (@memory_triple_region_source_domain source package fe ge locals le memory after final SOURCE) as DOMAIN.
  pose proof (triple_region_cap (triple_region_syntax package)) as [_ CAP].
  destruct (@memory_triple_guard_sound (triple_cap d) descriptors (triple_row d) (triple_row_bound d)
    (triple_column_bound d) (triple_depth_bound d) (Entry ge locals le memory) CAP DOMAIN ACCEPT)
    as [ZERO [NRANGE [MRANGE [LRANGE ALIAS]]]].
  destruct (@memory_triple_source_under_ranges source package fe ge locals le memory after final
    ZERO NRANGE MRANGE LRANGE SOURCE) as [entries [ARRAYS [UNIQUE [POINTERS [LOOP EXIT]]]]].
  assert (VIEW : MemoryNested.A.typed_view context (memory_triple_parameters d le) le).
  { change (MemoryNested.A.typed_view context (memory_source_parameter_values context (Entry ge locals le memory)) le).
    apply (@memory_source_parameter_view context (Entry ge locals le memory)); intros identifier MEMBER; unfold context,memory_triple_context in MEMBER; cbn in MEMBER.
    destruct MEMBER as [<-|[<-|[<-|ABSENT]]]; try contradiction; exact (proj1 NRANGE) || exact (proj1 MRANGE) || exact (proj1 LRANGE). }
  assert (WITHIN : MemoryNested.A.env_within (memory_triple_bounds (triple_cap d)) (memory_triple_parameters d le)).
  { unfold memory_triple_bounds,memory_triple_parameters; cbn [map].
    destruct NRANGE as [_ NR],MRANGE as [_ MR],LRANGE as [_ LR]; cbn [entry_temps] in NR,MR,LR.
    repeat apply MemoryNested.A.env_within_cons; try (unfold MemoryNested.A.contains; cbn; lia).
    intros index bound ABSENT; rewrite nth_error_nil in ABSENT; discriminate. }
  destruct ALIAS as [other [OTHER BLOCKS]].
  assert (SAME : map memory_array_block entries = map memory_array_block other).
  { rewrite <- (@memory_descriptor_blocks_binding descriptors entries (Entry ge locals le memory) ARRAYS).
    rewrite <- (@memory_descriptor_blocks_binding descriptors other (Entry ge locals le memory) OTHER); reflexivity. }
  assert (NONALIAS : GuardMemoryInstr.NonAlias (RuntimeState (memory_array_registry entries) memory))
    by (apply memory_array_registry_nonalias; rewrite SAME; exact BLOCKS).
  pose proof (@CANDIDATE (memory_triple_parameters d le) (RuntimeState (memory_array_registry entries) memory)
    (RuntimeState (memory_array_registry entries) final) eq_refl WITHIN NONALIAS LOOP) as TARGET.
  destruct (@compile_memory_registry_loop_correct descriptors entries fe ge locals ARRAYS context
    (memory_triple_bounds (triple_cap d)) live pool candidate code (memory_triple_parameters d le) le
    (RuntimeState (memory_array_registry entries) memory) (RuntimeState (memory_array_registry entries) final) memory
    COMPILE VIEW WITHIN TARGET eq_refl) as [private_temps [private_memory [MEMORY [FRAME EXEC]]]].
  unfold memory_registry_view in MEMORY; inversion MEMORY; subst private_memory.
  exists (memory_triple_exit d private_temps); split.
  - unfold memory_triple_candidate; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact EXEC|].
    apply memory_triple_restore_execution.
    + pose proof (triple_region_dm (triple_region_syntax package)); unfold d; congruence.
    + pose proof (triple_region_dn (triple_region_syntax package)); unfold d; congruence.
    + pose proof (triple_region_cn (triple_region_syntax package)); unfold d; congruence.
    + intros identifier MEMBER; destruct (@memory_source_typed_word context (memory_triple_parameters d le) le identifier VIEW MEMBER) as [word WORD].
      exists word; cbn [entry_temps]; rewrite FRAME by (apply in_or_app; left; exact MEMBER); exact WORD.
  - rewrite EXIT; apply memory_triple_exit_frame; exact FRAME.
Qed.

Definition memory_triple_candidate_rule : encoded_private_rule live source (memory_triple_candidate code d).
Proof.
  pose proof (triple_region_syntax package) as CERT.
  assert (WRITES : writes_only [triple_row d;triple_column d;triple_depth d] source).
  { rewrite (triple_region_source CERT).
    apply memory_frontend_loop_writes; [cbn; auto|].
    eapply memory_reset_child_writes; [exact (triple_region_outer CERT)|cbn; auto|].
    apply memory_frontend_loop_writes; [cbn; auto|].
    eapply memory_reset_child_writes; [exact (triple_region_middle CERT)|cbn; auto|].
    apply memory_frontend_loop_writes; [cbn; auto|].
    eapply writes_only_weaken with (small := []); [cbn; tauto|exact (nary_body_writes (triple_region_model CERT))]. }
  refine {| private_rule_writes := [triple_row d;triple_column d;triple_depth d]; private_rule_source_writes := WRITES;
    private_rule_atoms := unit;
    private_rule_domain := memory_triple_guard_domain (triple_cap d) descriptors (triple_row d) (triple_row_bound d)
      (triple_column_bound d) (triple_depth_bound d);
    private_rule_dimension := memory_triple_guard_dimension (triple_cap d) descriptors (triple_row d) (triple_row_bound d)
      (triple_column_bound d) (triple_depth_bound d);
    private_rule_primitives := memory_triple_guard_primitives (triple_cap d) descriptors (triple_row d) (triple_row_bound d)
      (triple_column_bound d) (triple_depth_bound d);
    private_rule_formula := Fact tt |}.
  - intros temps p locals le memory after final RUN.
    exact (@memory_triple_region_source_domain source package (adapter_entry temps) (globalenv p) locals le memory after final RUN).
  - intros temps p locals le memory after final SCOPE RUN ACCEPT.
    destruct (@memory_triple_candidate_local (adapter_entry temps) (globalenv p) locals le memory after final ACCEPT RUN) as [target [EXEC FRAME]].
    exists target,final; split; [exact EXEC|split; [exact FRAME|apply memory_equivalent_refl]].
Defined.
End CANDIDATE.
Print Assumptions memory_triple_candidate_local.
Print Assumptions memory_triple_candidate_rule.
