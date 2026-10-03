From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightRedundantSet ClightCountedLoop ClightMatrixGuard ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryRecursiveSource GuardMemoryRecursiveSyntax
  GuardMemoryRecursiveGuard GuardMemoryRecursiveWords GuardMemoryRecursiveDomain GuardMemoryRegistryGuard
  GuardMemoryNarySequence GuardMemoryNaryLoops GuardMemoryMultipleArrays GuardMemoryLayoutRegistry GuardMemoryRegistryBackend
  GuardMemoryScalarArraySyntax GuardMemoryScalarArrayBody GuardMemoryScalarPointerBody GuardMemoryScalarLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem memory_scalar_array_source_under_ranges source (package : memory_scalar_array_region_package source)
  fe ge locals temps memory after final :
  memory_nest_initial (scalar_array_region_nest package) temps ->
  Forall (fun bound => register_range bound (scalar_array_region_limit package) (Entry ge locals temps memory))
    (memory_nest_bounds (scalar_array_region_nest package)) ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists entries,
    Forall2 (memory_descriptor_binding ge locals) (memory_scalar_array_region_descriptors package) entries /\
    NoDup (map memory_array_id entries) /\
    Forall (fun entry => Mem.valid_pointer memory (memory_array_block entry) 0 = true) entries /\
    memory_nest_bindings (scalar_array_region_scalars package)
      (memory_recursive_parameters (scalar_array_region_scalars package) temps) temps /\
    L.loop_semantics (memory_scalar_rectangle 0 (length (memory_nest_iterators (scalar_array_region_nest package)))
      (length (scalar_array_region_scalars package)) (memory_scalar_array_region_instructions package))
      (memory_recursive_parameters (memory_nest_bounds (scalar_array_region_nest package)) temps++
        memory_recursive_parameters (scalar_array_region_scalars package) temps)
      (RuntimeState (memory_array_registry entries) memory) (RuntimeState (memory_array_registry entries) final) /\
    after = memory_recursive_exit (scalar_array_region_nest package) temps.
Proof.
  intros INITIAL RANGES SOURCE.
  assert (POSITIVE : Forall (fun bound => 0 < Int.signed (temp_word bound temps)) (memory_nest_bounds (scalar_array_region_nest package))).
  { eapply Forall_impl; [|exact RANGES]; intros bound [_ POSITIVE]; exact (proj1 POSITIVE). }
  pose proof (@memory_scalar_array_source_first_capability source package fe ge locals temps memory after final POSITIVE INITIAL SOURCE) as TYPED.
  assert (SCALARS : memory_nest_bindings (scalar_array_region_scalars package)
    (memory_recursive_parameters (scalar_array_region_scalars package) temps) temps)
    by (apply memory_scalar_register_bindings; exact TYPED).
  destruct (@memory_recursive_parameter_data (scalar_array_region_limit package) (memory_nest_bounds (scalar_array_region_nest package))
    ge locals temps memory RANGES) as [BINDINGS [VALUES [COUNTS LIMITS]]].
  assert (LENGTH : length (memory_recursive_counts (memory_nest_bounds (scalar_array_region_nest package)) temps) =
    length (memory_nest_iterators (scalar_array_region_nest package))).
  { unfold memory_recursive_counts,memory_recursive_parameters; rewrite !length_map,memory_nest_lengths; reflexivity. }
  destruct (@memory_scalar_array_body_source_decode source package fe ge locals
    (memory_recursive_counts (memory_nest_bounds (scalar_array_region_nest package)) temps)
    (memory_recursive_parameters (scalar_array_region_scalars package) temps) temps memory after final
    LENGTH COUNTS ltac:(unfold memory_recursive_limits; rewrite memory_nest_lengths; exact LIMITS)
    BINDINGS INITIAL SCALARS SOURCE) as [entries [ARRAYS [IDS [POINTERS [LOOP EXIT]]]]].
  exists entries; split; [exact ARRAYS|]; split; [exact IDS|]; split; [exact POINTERS|]; split; [exact SCALARS|]; split.
  - rewrite LENGTH,VALUES in LOOP.
    replace (length (memory_recursive_parameters (scalar_array_region_scalars package) temps)) with
      (length (scalar_array_region_scalars package)) in LOOP by (unfold memory_recursive_parameters; apply eq_sym,length_map).
    exact LOOP.
  - rewrite EXIT; apply memory_recursive_exit_counts; exact VALUES.
Qed.
Theorem memory_scalar_array_region_source_domain source (package : memory_scalar_array_region_package source)
  fe ge locals temps memory after final :
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  memory_recursive_guard_domain (scalar_array_region_limit package) (memory_scalar_array_region_descriptors package)
    (scalar_array_region_nest package) (Entry ge locals temps memory).
Proof.
  intro SOURCE; pose proof (scalar_array_region_syntax package) as CERT.
  pose proof (scalar_array_region_source CERT) as EQUAL; pose proof (scalar_array_region_fresh CERT) as FRESH.
  pose proof (scalar_array_region_shapes CERT) as SHAPES; pose proof (proj2 (scalar_array_region_cap CERT)) as CAP.
  pose proof (scalar_array_region_body CERT) as BODY.
  assert (NORMAL := @memory_nary_compute_sequence_normal (scalar_array_region_code package) (memory_nest_leaf (scalar_array_region_nest package)) BODY).
  assert (QUIET := @memory_nary_compute_sequence_quiet (scalar_array_region_code package) (memory_nest_leaf (scalar_array_region_nest package)) BODY).
  assert (WRITES := @memory_nary_compute_sequence_writes (scalar_array_region_code package) (memory_nest_leaf (scalar_array_region_nest package)) BODY).
  rewrite EQUAL in SOURCE; destruct (scalar_array_region_nest package) as [code|iterator bound body child] eqn:NEST.
  - pose proof (scalar_array_region_nonempty CERT) as NONEMPTY; cbn in NONEMPTY; contradiction.
  - assert (ITERATOR : register_domain iterator (Entry ge locals temps memory)) by (eapply memory_recursive_source_iterator_word; exact SOURCE).
    split; [exact ITERATOR|]; intro ZERO.
    assert (INITIAL : memory_nest_initial (MemorySourceAxis iterator bound body child) temps)
      by (exact (@register_flag_evidence iterator Int.zero (Entry ge locals temps memory) ITERATOR ZERO)).
    pose proof (@memory_recursive_source_bound_words fe ge locals (MemorySourceAxis iterator bound body child)
      (scalar_array_region_limit package) CAP SHAPES FRESH NORMAL QUIET WRITES temps memory after final INITIAL SOURCE) as BOUNDS.
    split; [exact BOUNDS|]; intro ALL.
    pose proof (@memory_recursive_bounds_sound (scalar_array_region_limit package)
      (memory_nest_bounds (MemorySourceAxis iterator bound body child)) (Entry ge locals temps memory) CAP BOUNDS ALL) as RANGES.
    rewrite <- EQUAL in SOURCE; rewrite <- NEST in INITIAL,RANGES.
    destruct (@memory_scalar_array_source_under_ranges source package fe ge locals temps memory after final INITIAL RANGES SOURCE)
      as [entries [ARRAYS [IDS [POINTERS REST]]]].
    exists entries; split; assumption.
Qed.
Print Assumptions memory_scalar_array_source_under_ranges.
Print Assumptions memory_scalar_array_region_source_domain.
