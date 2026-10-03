From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightGuard ClightNoWrap ClightRedundantSet ClightCountedLoop
  ClightStraightLine ClightRectangularGuard ClightMatrixGuard.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryMultipleArrays GuardMemoryRegistryBackend
  GuardMemoryControlSettle GuardMemoryNaryBodyModel GuardMemoryNaryLoops GuardMemoryRecursiveSource
  GuardMemoryRecursiveBody GuardMemoryRecursiveSyntax GuardMemoryRecursiveGuard GuardMemoryRecursiveWords GuardMemoryRegistryGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_recursive_parameters (bounds : list ident) temps := map (fun identifier => Int.signed (temp_word identifier temps)) bounds.
Definition memory_recursive_counts bounds temps := map Z.to_nat (memory_recursive_parameters bounds temps).
Definition memory_recursive_exit nest temps := memory_settle_controls
  (combine (memory_nest_iterators nest) (map (fun bound => Vint (temp_word bound temps)) (memory_nest_bounds nest))) temps.
Lemma memory_recursive_parameter_data cap bounds ge locals temps memory :
  Forall (fun bound => register_range bound cap (Entry ge locals temps memory)) bounds ->
  memory_nest_bindings bounds (map Z.of_nat (memory_recursive_counts bounds temps)) temps /\
  map Z.of_nat (memory_recursive_counts bounds temps) = memory_recursive_parameters bounds temps /\
  Forall (fun count => count <> O /\ signed_range (Z.of_nat count)) (memory_recursive_counts bounds temps) /\
  Forall2 (fun count limit => Z.of_nat count <= limit) (memory_recursive_counts bounds temps) (repeat cap (length bounds)).
Proof.
  intro RANGES; induction RANGES as [|bound bounds [[word WORD] RANGE] RANGES IH];
    unfold memory_recursive_counts,memory_recursive_parameters in *; cbn [map length repeat].
  - repeat split; constructor.
  - cbn [entry_temps] in WORD,RANGE; unfold temp_word in *; rewrite WORD in *.
    assert (COUNT : Z.of_nat (Z.to_nat (Int.signed word)) = Int.signed word) by (apply Z2Nat.id; lia).
    destruct IH as [BINDINGS [VALUES [COUNTS LIMITS]]]; repeat split.
    + constructor; [rewrite COUNT,Int.repr_signed; exact WORD|exact BINDINGS].
    + rewrite COUNT,VALUES; reflexivity.
    + constructor; [split; [intro ZERO; rewrite ZERO in COUNT; cbn in COUNT; lia|rewrite COUNT; apply Int.signed_range]|exact COUNTS].
    + constructor; [rewrite COUNT; exact (proj2 RANGE)|exact LIMITS].
Qed.
Lemma memory_recursive_exit_counts nest counts temps :
  map Z.of_nat counts = memory_recursive_parameters (memory_nest_bounds nest) temps ->
  memory_nest_exit nest counts temps = memory_recursive_exit nest temps.
Proof.
  intro COUNTS; unfold memory_nest_exit,memory_nest_assignments,memory_recursive_exit.
  assert (WORDS : map (fun count => Vint (Int.repr (Z.of_nat count))) counts =
    map (fun bound => Vint (temp_word bound temps)) (memory_nest_bounds nest)).
  { replace (map (fun count => Vint (Int.repr (Z.of_nat count))) counts) with
      (map (fun value => Vint (Int.repr value)) (map Z.of_nat counts)) by (rewrite map_map; reflexivity).
    rewrite COUNTS; unfold memory_recursive_parameters; rewrite map_map.
    apply map_ext; intro identifier; rewrite Int.repr_signed; reflexivity. }
  rewrite WORDS; reflexivity.
Qed.

Theorem memory_recursive_source_under_ranges source (package : memory_recursive_region_package source)
  fe ge locals temps memory after final :
  memory_nest_initial (recursive_region_nest package) temps ->
  Forall (fun bound => register_range bound (recursive_region_limit package) (Entry ge locals temps memory))
    (memory_nest_bounds (recursive_region_nest package)) ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists entries,
    Forall2 (memory_descriptor_binding ge locals) (memory_recursive_region_descriptors package) entries /\
    NoDup (map memory_array_id entries) /\
    Forall (fun entry => Mem.valid_pointer memory (memory_array_block entry) 0 = true) entries /\
    L.loop_semantics (memory_nary_rectangle 0 (length (memory_nest_iterators (recursive_region_nest package)))
      (memory_recursive_region_instructions package))
      (memory_recursive_parameters (memory_nest_bounds (recursive_region_nest package)) temps)
      (RuntimeState (memory_array_registry entries) memory) (RuntimeState (memory_array_registry entries) final) /\
    after = memory_recursive_exit (recursive_region_nest package) temps.
Proof.
  destruct package as [nest cap CERT]; destruct CERT as [EQUAL NONEMPTY SHAPES FRESH CAP MODEL]; cbn in *.
  intros INITIAL RANGES SOURCE; subst source.
  destruct (@memory_recursive_parameter_data cap (memory_nest_bounds nest) ge locals temps memory RANGES)
    as [BINDINGS [VALUES [COUNTS LIMITS]]].
  assert (LENGTH : length (memory_recursive_counts (memory_nest_bounds nest) temps) = length (memory_nest_iterators nest)).
  { unfold memory_recursive_counts,memory_recursive_parameters; rewrite !length_map,memory_nest_lengths; reflexivity. }
  destruct (@memory_recursive_body_source_decode fe ge locals nest (memory_recursive_limits nest cap) MODEL
    (memory_recursive_counts (memory_nest_bounds nest) temps) temps memory after final SHAPES FRESH LENGTH COUNTS
    ltac:(unfold memory_recursive_limits; rewrite memory_nest_lengths; exact LIMITS) BINDINGS INITIAL SOURCE)
    as [entries [ARRAYS [UNIQUE [POINTERS [LOOP EXIT]]]]].
  exists entries; split; [exact ARRAYS|]; split; [exact UNIQUE|]; split; [exact POINTERS|]; split.
  - rewrite LENGTH,VALUES in LOOP; exact LOOP.
  - rewrite EXIT; apply memory_recursive_exit_counts; exact VALUES.
Qed.

Theorem memory_recursive_region_source_domain source (package : memory_recursive_region_package source)
  fe ge locals temps memory after final :
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  memory_recursive_guard_domain (recursive_region_limit package) (memory_recursive_region_descriptors package)
    (recursive_region_nest package) (Entry ge locals temps memory).
Proof.
  intro SOURCE; pose proof (recursive_region_syntax package) as CERT.
  pose proof (recursive_region_model CERT) as MODEL; pose proof (recursive_region_source CERT) as EQUAL.
  pose proof (recursive_region_fresh CERT) as FRESH; pose proof (recursive_region_shapes CERT) as SHAPES.
  pose proof (proj2 (recursive_region_cap CERT)) as CAP.
  rewrite EQUAL in SOURCE.
  destruct (recursive_region_nest package) as [code|iterator bound body child] eqn:NEST.
  - pose proof (recursive_region_nonempty CERT) as NONEMPTY; cbn in NONEMPTY; contradiction.
  - assert (ITERATOR : register_domain iterator (Entry ge locals temps memory))
      by (eapply memory_recursive_source_iterator_word; exact SOURCE).
    split; [exact ITERATOR|]; intro ZERO.
    assert (INITIAL : memory_nest_initial (MemorySourceAxis iterator bound body child) temps).
    { exact (@register_flag_evidence iterator Int.zero (Entry ge locals temps memory) ITERATOR ZERO). }
    pose proof (@memory_recursive_source_bound_words fe ge locals (MemorySourceAxis iterator bound body child)
      (recursive_region_limit package) CAP SHAPES FRESH (nary_body_normal MODEL) (nary_body_quiet MODEL)
      (nary_body_writes MODEL) temps memory after final INITIAL SOURCE) as BOUNDS.
    split; [exact BOUNDS|]; intro ALL.
    pose proof (@memory_recursive_bounds_sound (recursive_region_limit package)
      (memory_nest_bounds (MemorySourceAxis iterator bound body child)) (Entry ge locals temps memory) CAP BOUNDS ALL) as RANGES.
    rewrite <- EQUAL in SOURCE; rewrite <- NEST in INITIAL,RANGES.
    destruct (@memory_recursive_source_under_ranges source package fe ge locals temps memory after final INITIAL RANGES SOURCE)
      as [entries [ARRAYS [UNIQUE [POINTERS REST]]]].
    exists entries; split; assumption.
Qed.
Print Assumptions memory_recursive_source_under_ranges.
Print Assumptions memory_recursive_region_source_domain.
