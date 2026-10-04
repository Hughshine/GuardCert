From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightRedundantSet ClightCountedLoop ClightMatrixGuard ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryRecursiveSource GuardMemoryRecursiveSyntax
  GuardMemoryNaryRanges GuardMemoryRecursiveGuard GuardMemoryRecursiveWords GuardMemoryRecursiveDomain GuardMemoryRegistryGuard
  GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerBody GuardMemoryMultiPointerCells GuardMemoryScalarPointerBody GuardMemoryScalarLoops GuardMemoryPointerSequence GuardMemoryNaryLoops GuardMemoryBufferOffsets.
From GuardMemory Require Import GuardMemoryVectorBounds GuardMemoryVectorDomain GuardMemoryVectorGuard
  GuardMemoryVectorPointerSyntax.
From GuardMemory Require Import GuardMemoryParamPointerSyntax GuardMemoryParamPointerBody.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem memory_param_pointer_source_under_ranges source (package : memory_param_pointer_region_package source)
  fe ge locals temps memory after final :
  memory_nest_initial (param_pointer_region_nest package) temps ->
  Forall2 (fun cap bound => register_range bound cap (Entry ge locals temps memory))
    (param_pointer_region_limits package) (memory_nest_bounds (param_pointer_region_nest package)) ->
  memory_nary_ranges (param_pointer_region_parameter_limits package)
    (memory_recursive_parameters (param_pointer_region_parameters package) temps) ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  memory_nest_bindings (param_pointer_region_parameters package)
      (memory_recursive_parameters (param_pointer_region_parameters package) temps) temps /\
  memory_nest_bindings (param_pointer_region_scalars package)
      (memory_recursive_parameters (param_pointer_region_scalars package) temps) temps /\
    L.loop_semantics (memory_scalar_rectangle 0 (length (memory_nest_iterators (param_pointer_region_nest package)))
      (length (param_pointer_region_parameters package++param_pointer_region_scalars package))
      (memory_param_pointer_region_instructions package))
      (memory_recursive_parameters (memory_nest_bounds (param_pointer_region_nest package)) temps++
        (memory_recursive_parameters (param_pointer_region_parameters package) temps++
         memory_recursive_parameters (param_pointer_region_scalars package) temps))
      (RuntimeState (memory_multi_pointer_locations temps (param_pointer_region_window package)) memory)
      (RuntimeState (memory_multi_pointer_locations temps (param_pointer_region_window package)) final) /\
    after = memory_recursive_exit (param_pointer_region_nest package) temps.
Proof.
  intros INITIAL RANGES PARAM_RANGES SOURCE.
  assert (POSITIVE : Forall (fun bound => 0 < Int.signed (temp_word bound temps)) (memory_nest_bounds (param_pointer_region_nest package))).
  { induction RANGES; constructor; [exact (proj1 (proj2 H))|exact IHRANGES]. }
  pose proof (@memory_param_pointer_source_first_capability source package fe ge locals temps memory after final POSITIVE INITIAL SOURCE) as TYPED.
  assert (SCALARS : memory_nest_bindings (param_pointer_region_scalars package)
    (memory_recursive_parameters (param_pointer_region_scalars package) temps) temps)
    by (apply memory_scalar_register_bindings; intros identifier MEMBER; apply TYPED; apply in_or_app; right; exact MEMBER).
  assert (PARAMETERS : memory_nest_bindings (param_pointer_region_parameters package)
    (memory_recursive_parameters (param_pointer_region_parameters package) temps) temps)
    by (apply memory_scalar_register_bindings; intros identifier MEMBER; apply TYPED; apply in_or_app; left; exact MEMBER).
  destruct (@memory_vector_parameter_data (param_pointer_region_limits package) (memory_nest_bounds (param_pointer_region_nest package))
    ge locals temps memory RANGES) as [BINDINGS [VALUES [COUNTS LIMITS]]].
  assert (LENGTH : length (memory_recursive_counts (memory_nest_bounds (param_pointer_region_nest package)) temps) =
    length (memory_nest_iterators (param_pointer_region_nest package))).
  { unfold memory_recursive_counts,memory_recursive_parameters; rewrite !length_map,memory_nest_lengths; reflexivity. }
  destruct (@memory_param_pointer_body_source_decode source package fe ge locals
    (memory_recursive_counts (memory_nest_bounds (param_pointer_region_nest package)) temps)
    (memory_recursive_parameters (param_pointer_region_parameters package) temps)
    (memory_recursive_parameters (param_pointer_region_scalars package) temps) temps memory after final
    LENGTH COUNTS LIMITS
    BINDINGS INITIAL PARAMETERS PARAM_RANGES SCALARS SOURCE) as [LOOP EXIT].
  split; [exact PARAMETERS|]; split; [exact SCALARS|]; split.
  - rewrite LENGTH,VALUES in LOOP.
    replace (length (memory_recursive_parameters (param_pointer_region_parameters package) temps++
      memory_recursive_parameters (param_pointer_region_scalars package) temps)) with
      (length (param_pointer_region_parameters package++param_pointer_region_scalars package)) in LOOP
      by (unfold memory_recursive_parameters; rewrite !length_app,!length_map; reflexivity).
    exact LOOP.
  - rewrite EXIT; apply memory_recursive_exit_counts; exact VALUES.
Qed.
Theorem memory_param_pointer_region_source_domain source (package : memory_param_pointer_region_package source)
  fe ge locals temps memory after final :
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  memory_vector_guard_domain (param_pointer_region_limits package) (param_pointer_region_nest package)
    (Entry ge locals temps memory).
Proof.
  intro SOURCE; pose proof (param_pointer_region_syntax package) as CERT.
  pose proof (param_pointer_region_source CERT) as EQUAL; pose proof (param_pointer_region_fresh CERT) as FRESH.
  pose proof (param_pointer_region_shapes CERT) as SHAPES; pose proof (param_pointer_region_caps CERT) as CAPS.
  pose proof (param_pointer_region_limits_length CERT) as LENGTH; pose proof (param_pointer_region_body CERT) as BODY.
  assert (NORMAL := @memory_pointer_sequence_normal (param_pointer_region_code package) (memory_nest_leaf (param_pointer_region_nest package)) BODY).
  assert (QUIET := @memory_pointer_sequence_quiet (param_pointer_region_code package) (memory_nest_leaf (param_pointer_region_nest package)) BODY).
  assert (WRITES := @memory_pointer_sequence_writes (param_pointer_region_code package) (memory_nest_leaf (param_pointer_region_nest package)) BODY).
  rewrite EQUAL in SOURCE; destruct (param_pointer_region_nest package) as [code|iterator bound body child] eqn:NEST.
  - exact I.
  - assert (ITERATOR : register_domain iterator (Entry ge locals temps memory))
      by (eapply memory_recursive_source_iterator_word; exact SOURCE).
    split; [exact ITERATOR|]; intro ZERO.
    assert (INITIAL : memory_nest_initial (MemorySourceAxis iterator bound body child) temps)
      by (exact (@register_flag_evidence iterator Int.zero (Entry ge locals temps memory) ITERATOR ZERO)).
    eapply memory_vector_source_bound_words; [| |exact SHAPES|exact FRESH|exact NORMAL|exact QUIET|exact WRITES|exact INITIAL|exact SOURCE].
    + rewrite <-memory_nest_lengths; exact LENGTH.
    + eapply Forall_impl; [|exact CAPS]; intros cap [_ SIGNED]; exact SIGNED.
Qed.
Print Assumptions memory_param_pointer_source_under_ranges.
Print Assumptions memory_param_pointer_region_source_domain.
