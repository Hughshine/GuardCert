From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCountedLoop ClightTempFrame ClightFiniteRegion ClightStraightLine ClightNoWrap.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryNaryRanges GuardMemoryNaryLoops
  GuardMemoryNaryLift GuardMemoryRecursiveSource GuardMemoryRecursiveSyntax GuardMemoryRecursiveBody
  GuardMemoryRecursiveFramedExecution GuardMemoryRecursiveFirstLeaf GuardMemoryNaryCompute GuardMemoryNarySequence
  GuardMemoryNaryAffineAccess GuardMemoryMultipleArrays GuardMemoryRegistryBackend GuardMemoryLayoutRegistry
  GuardMemoryScalarArraySyntax GuardMemoryScalarArraySequence GuardMemoryScalarArrayCompute GuardMemoryScalarArrayAnchors
  GuardMemoryScalarPointerBody GuardMemoryRecursiveDomain GuardMemoryScalarLoops GuardMemoryScalarLift GuardMemorySourceParameters.
From GuardMemory Require Import GuardMemoryInstructionPadding.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem memory_scalar_array_source_first_capability source (package : memory_scalar_array_region_package source) fe ge locals temps memory after final :
  Forall (fun bound => 0 < Int.signed (temp_word bound temps)) (memory_nest_bounds (scalar_array_region_nest package)) ->
  memory_nest_initial (scalar_array_region_nest package) temps ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  forall identifier, In identifier (scalar_array_region_scalars package) -> exists word, temps ! identifier = Some (Vint word).
Proof.
  intros POSITIVE INITIAL SOURCE.
  destruct package as [nest cap scalars operations CERT]; cbn in *.
  destruct CERT as [EQUAL NONEMPTY SHAPES FRESH CAP UNIQUE STABLE USED OPS VALID BODY COVER]; subst source.
  assert (DISJOINT : forall identifier, In identifier (memory_nest_iterators nest) -> ~ In identifier scalars).
  { intros identifier MEMBER BAD; exact (STABLE identifier BAD MEMBER). }
  destruct (@memory_recursive_first_leaf fe ge locals nest SHAPES FRESH
    (@memory_nary_compute_sequence_normal operations (memory_nest_leaf nest) BODY)
    (@memory_nary_compute_sequence_quiet operations (memory_nest_leaf nest) BODY)
    (@memory_nary_compute_sequence_writes operations (memory_nest_leaf nest) BODY) scalars temps memory after final
    DISJOINT POSITIVE INITIAL SOURCE) as [leaf_temps [leaf_after [leaf_final [FRAME LEAF]]]].
  apply flatten_region_execution in LEAF; rewrite BODY in LEAF.
  intros identifier MEMBER; destruct (USED identifier MEMBER) as [operation [index [IN [LOOKUP USE]]]].
  destruct (@memory_scalar_array_sequence_used_register (memory_recursive_limits nest cap) operations (memory_nest_iterators nest)
    scalars fe ge locals identifier index VALID LOOKUP leaf_temps memory leaf_after leaf_final LEAF operation IN USE) as [word WORD].
  exists word; rewrite (FRAME identifier MEMBER) in WORD; exact WORD.
Qed.
Print Assumptions memory_scalar_array_source_first_capability.

Theorem memory_scalar_array_body_source_decode source (package : memory_scalar_array_region_package source)
  fe ge locals counts scalar_values temps memory after final :
  length counts = length (memory_nest_iterators (scalar_array_region_nest package)) ->
  Forall (fun count => count <> O /\ signed_range (Z.of_nat count)) counts ->
  Forall2 (fun count limit => Z.of_nat count <= limit) counts
    (memory_recursive_limits (scalar_array_region_nest package) (scalar_array_region_limit package)) ->
  memory_nest_bindings (memory_nest_bounds (scalar_array_region_nest package)) (map Z.of_nat counts) temps ->
  memory_nest_initial (scalar_array_region_nest package) temps ->
  memory_nest_bindings (scalar_array_region_scalars package) scalar_values temps ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists entries,
    Forall2 (memory_descriptor_binding ge locals) (memory_scalar_array_region_descriptors package) entries /\
    NoDup (map memory_array_id entries) /\
    Forall (fun entry => Mem.valid_pointer memory (memory_array_block entry) 0 = true) entries /\
    L.loop_semantics (memory_scalar_rectangle 0 (length counts) (length scalar_values)
      (memory_scalar_array_region_instructions package)) (map Z.of_nat counts++scalar_values)
      (RuntimeState (memory_array_registry entries) memory) (RuntimeState (memory_array_registry entries) final) /\
    after = memory_nest_exit (scalar_array_region_nest package) counts temps.
Proof.
  destruct package as [nest cap scalars operations CERT]; cbn in *.
  destruct CERT as [EQUAL NONEMPTY SHAPES FRESH CAP UNIQUE STABLE USED OPS VALID BODY COVER]; subst source.
  intros LENGTH COUNTS LIMITS BOUNDS INITIAL SCALARS SOURCE.
  set (physical := fun coordinates => memory_nary_compute_sequence_physical ge locals (coordinates++scalar_values) operations).
  set (capability := fun le => memory_nest_bindings scalars scalar_values le).
  assert (DISJOINT : forall identifier, In identifier (memory_nest_iterators nest) -> ~ In identifier scalars).
  { intros identifier MEMBER BAD; exact (STABLE identifier BAD MEMBER). }
  assert (CAP_FRAME : forall first second, temp_agree scalars first second -> capability first -> capability second).
  { intros first second FRAME WORDS; eapply memory_nest_bindings_frame_from; [|exact FRAME|exact WORDS]; auto. }
  assert (DECODE : forall coordinates le before next target, memory_nary_domain counts [] coordinates ->
    memory_nest_bindings (memory_nest_iterators nest) coordinates le -> capability le ->
    exec_stmt fe ge locals le before (memory_nest_leaf nest) E0 next target Out_normal -> physical coordinates before target /\ next = le).
  { intros coordinates le before next target DOMAIN WORDS SCALAR_WORDS RUN.
    assert (FULL_WORDS : memory_nest_bindings (memory_nest_iterators nest++scalars) (coordinates++scalar_values) le)
      by (apply memory_nest_bindings_append; assumption).
    destruct (memory_nest_bindings_valuation UNIQUE FULL_WORDS) as [valuation [VALUES BINDINGS]].
    assert (COORDINATES : map valuation (memory_nest_iterators nest) = coordinates).
    { apply memory_list_prefix_equal with (trailing := map valuation scalars) (other := scalar_values).
      - rewrite length_map; apply Forall2_length in WORDS; exact WORDS.
      - rewrite <- map_app; exact VALUES. }
    unfold physical; rewrite <- VALUES; apply flatten_region_execution in RUN; rewrite BODY in RUN.
    eapply memory_scalar_array_sequence_tail_inverse; [exact VALID| |exact BINDINGS|exact RUN].
    rewrite COORDINATES; eapply memory_nary_domain_ranges; eassumption. }
  destruct (@memory_recursive_source_decode_framed fe ge locals nest scalars capability CAP_FRAME SHAPES FRESH DISJOINT
    (@memory_nary_compute_sequence_normal operations (memory_nest_leaf nest) BODY)
    (@memory_nary_compute_sequence_quiet operations (memory_nest_leaf nest) BODY)
    (@memory_nary_compute_sequence_writes operations (memory_nest_leaf nest) BODY)
    counts physical [] [] temps memory after final LENGTH COUNTS ltac:(cbn; tauto) DECODE
    ltac:(constructor) BOUNDS INITIAL SCALARS SOURCE) as [ITER EXIT].
  assert (POSITIVE : Forall (fun count => count <> O) counts).
  { eapply Forall_impl; [|exact COUNTS]; intros count [POS RANGE]; exact POS. }
  destruct (@memory_nary_first mem physical counts POSITIVE [] memory final ITER) as [first HEAD].
  unfold physical in HEAD; rewrite LENGTH in HEAD.
  destruct (@memory_scalar_array_sequence_registry (memory_recursive_limits nest cap) (memory_nest_iterators nest) scalars
    ge locals scalar_values operations memory first VALID HEAD) as [entries [ARRAYS [IDS POINTERS]]].
  exists entries; split; [exact ARRAYS|]; split; [exact IDS|]; split; [exact POINTERS|]; split; [|exact EXIT].
  assert (POINT : forall coordinates before target, memory_nary_domain counts [] coordinates ->
    (physical coordinates before target <-> memory_scalar_sequence_point (memory_pad_instructions (length scalars) (map memory_nary_compute_instruction operations))
      coordinates scalar_values (RuntimeState (memory_array_registry entries) before) (RuntimeState (memory_array_registry entries) target))).
  { intros coordinates before target DOMAIN; unfold physical,memory_scalar_sequence_point; rewrite memory_pad_sequence_point.
    assert (RANGES : memory_nary_ranges (memory_recursive_limits nest cap) coordinates) by (eapply memory_nary_domain_ranges; eassumption).
    apply memory_scalar_array_sequence_point_execution with (limits := memory_recursive_limits nest cap)
      (layout := memory_nest_iterators nest) (scalars := scalars)
      (descriptors := memory_unique_descriptors (memory_nary_compute_sequence_anchors operations));
      [exact ARRAYS|exact IDS|apply memory_nary_compute_sequence_cover; exact COVER|exact VALID|exact RANGES|].
    apply Forall2_length in RANGES; unfold memory_recursive_limits in RANGES; rewrite repeat_length in RANGES; lia. }
  apply (proj1 (@memory_scalar_rectangle_lift (memory_array_registry entries) (memory_pad_instructions (length scalars) (map memory_nary_compute_instruction operations))
    physical counts scalar_values memory final POINT)); exact ITER.
Qed.
Print Assumptions memory_scalar_array_body_source_decode.
