From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightRedundantSet ClightCountedLoop ClightMatrixGuard ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryRecursiveSource GuardMemoryRecursiveSyntax
  GuardMemoryRecursiveGuard GuardMemoryRecursiveWords GuardMemoryRecursiveDomain GuardMemoryRegistryGuard
  GuardMemoryPointerSyntax GuardMemoryPointerBody GuardMemoryPointerSequence GuardMemoryNaryLoops GuardMemoryBufferOffsets.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem memory_pointer_source_under_ranges source (package : memory_pointer_region_package source)
  fe ge locals temps memory after final :
  memory_nest_initial (pointer_region_nest package) temps ->
  Forall (fun bound => register_range bound (pointer_region_limit package) (Entry ge locals temps memory))
    (memory_nest_bounds (pointer_region_nest package)) ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists block base, temps ! (pointer_region_pointer package) = Some (Vptr block base) /\
    L.loop_semantics (memory_nary_rectangle 0 (length (memory_nest_iterators (pointer_region_nest package)))
      (memory_pointer_region_instructions package))
      (memory_recursive_parameters (memory_nest_bounds (pointer_region_nest package)) temps)
      (RuntimeState (memory_pointer_buffer_locations (pointer_region_pointer package) block base (pointer_region_window package)) memory)
      (RuntimeState (memory_pointer_buffer_locations (pointer_region_pointer package) block base (pointer_region_window package)) final) /\
    after = memory_recursive_exit (pointer_region_nest package) temps.
Proof.
  intros INITIAL RANGES SOURCE.
  assert (POSITIVE : Forall (fun bound => 0 < Int.signed (temp_word bound temps)) (memory_nest_bounds (pointer_region_nest package))).
  { eapply Forall_impl; [|exact RANGES]; intros bound [_ POSITIVE]; exact (proj1 POSITIVE). }
  destruct (@memory_pointer_source_first_base source package fe ge locals temps memory after final POSITIVE INITIAL SOURCE)
    as [block [base POINTER]].
  destruct (@memory_recursive_parameter_data (pointer_region_limit package) (memory_nest_bounds (pointer_region_nest package))
    ge locals temps memory RANGES) as [BINDINGS [VALUES [COUNTS LIMITS]]].
  assert (LENGTH : length (memory_recursive_counts (memory_nest_bounds (pointer_region_nest package)) temps) =
    length (memory_nest_iterators (pointer_region_nest package))).
  { unfold memory_recursive_counts,memory_recursive_parameters; rewrite !length_map,memory_nest_lengths; reflexivity. }
  destruct (@memory_pointer_body_source_decode source package fe ge locals
    (memory_recursive_counts (memory_nest_bounds (pointer_region_nest package)) temps) temps memory after final block base
    LENGTH COUNTS ltac:(unfold memory_recursive_limits; rewrite memory_nest_lengths; exact LIMITS)
    BINDINGS INITIAL POINTER SOURCE) as [LOOP EXIT].
  exists block,base; split; [exact POINTER|]; split.
  - rewrite LENGTH,VALUES in LOOP; exact LOOP.
  - rewrite EXIT; apply memory_recursive_exit_counts; exact VALUES.
Qed.
Theorem memory_pointer_region_source_domain source (package : memory_pointer_region_package source)
  fe ge locals temps memory after final :
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  memory_recursive_guard_domain (pointer_region_limit package) [] (pointer_region_nest package) (Entry ge locals temps memory).
Proof.
  intro SOURCE; pose proof (pointer_region_syntax package) as CERT.
  pose proof (pointer_region_source CERT) as EQUAL; pose proof (pointer_region_fresh CERT) as FRESH.
  pose proof (pointer_region_shapes CERT) as SHAPES; pose proof (proj2 (pointer_region_cap CERT)) as CAP.
  pose proof (pointer_region_body CERT) as BODY.
  assert (NORMAL := @memory_pointer_sequence_normal (pointer_region_code package) (memory_nest_leaf (pointer_region_nest package)) BODY).
  assert (QUIET := @memory_pointer_sequence_quiet (pointer_region_code package) (memory_nest_leaf (pointer_region_nest package)) BODY).
  assert (WRITES := @memory_pointer_sequence_writes (pointer_region_code package) (memory_nest_leaf (pointer_region_nest package)) BODY).
  rewrite EQUAL in SOURCE; destruct (pointer_region_nest package) as [code|iterator bound body child] eqn:NEST.
  - pose proof (pointer_region_nonempty CERT) as NONEMPTY; cbn in NONEMPTY; contradiction.
  - assert (ITERATOR : register_domain iterator (Entry ge locals temps memory))
      by (eapply memory_recursive_source_iterator_word; exact SOURCE).
    split; [exact ITERATOR|]; intro ZERO.
    assert (INITIAL : memory_nest_initial (MemorySourceAxis iterator bound body child) temps)
      by (exact (@register_flag_evidence iterator Int.zero (Entry ge locals temps memory) ITERATOR ZERO)).
    split.
    + eapply memory_recursive_source_bound_words; eassumption.
    + intro ALL; exists []; split; constructor.
Qed.
Print Assumptions memory_pointer_source_under_ranges.
Print Assumptions memory_pointer_region_source_domain.
