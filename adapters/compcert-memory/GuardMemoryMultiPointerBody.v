From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCountedLoop ClightTempFrame ClightFiniteRegion ClightStraightLine ClightNoWrap.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryNaryRanges GuardMemoryNaryLoops
  GuardMemoryNaryLift GuardMemoryRecursiveSource GuardMemoryRecursiveSyntax GuardMemoryRecursiveBody GuardMemoryRecursiveFramedExecution GuardMemoryRecursiveFirstLeaf
  GuardMemoryPointerSequence GuardMemoryPointerSyntax GuardMemoryPointerCompute GuardMemoryNaryCompute GuardMemoryNaryAffineAccess GuardMemoryBufferOffsets.
From GuardMemory Require Import GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerSequence GuardMemoryMultiPointerCompute GuardMemoryMultiPointerIdentifiers GuardMemoryMultiPointerCells GuardMemoryScalarPointerBody GuardMemoryRecursiveDomain GuardMemoryScalarLoops GuardMemoryScalarLift GuardMemorySourceParameters.
From GuardMemory Require Import GuardMemoryInstructionPadding.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem memory_multi_pointer_source_first_capability source (package : memory_multi_pointer_region_package source) fe ge locals temps memory after final :
  Forall (fun bound => 0 < Int.signed (temp_word bound temps)) (memory_nest_bounds (multi_pointer_region_nest package)) ->
  memory_nest_initial (multi_pointer_region_nest package) temps ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  forall identifier, In identifier (multi_pointer_region_scalars package) -> exists word, temps ! identifier = Some (Vint word).
Proof.
  intros POSITIVE INITIAL SOURCE.
  destruct package as [nest cap pointers extent scalars operations CERT]; cbn in *.
  destruct CERT as [EQUAL NONEMPTY SHAPES FRESH CAP WINDOW PROTECTED UNIQUE STABLE USED OPS VALID COVERED BODY]; subst source.
  assert (DISJOINT : forall identifier, In identifier (memory_nest_iterators nest) -> ~ In identifier (pointers++scalars)).
  { intros identifier MEMBER BAD; apply in_app_iff in BAD as [BAD|BAD];
      [exact (PROTECTED identifier BAD MEMBER)|exact (STABLE identifier BAD MEMBER)]. }
  destruct (@memory_recursive_first_leaf fe ge locals nest SHAPES FRESH
    (@memory_pointer_sequence_normal operations (memory_nest_leaf nest) BODY)
    (@memory_pointer_sequence_quiet operations (memory_nest_leaf nest) BODY)
    (@memory_pointer_sequence_writes operations (memory_nest_leaf nest) BODY) (pointers++scalars) temps memory after final
    DISJOINT POSITIVE INITIAL SOURCE) as [leaf_temps [leaf_after [leaf_final [FRAME LEAF]]]].
  apply flatten_region_execution in LEAF; rewrite BODY in LEAF.
  assert (TYPED : forall identifier, In identifier scalars -> exists word, temps ! identifier = Some (Vint word)).
  { intros identifier MEMBER; destruct (USED identifier MEMBER) as [operation [index [IN [LOOKUP USE]]]].
    destruct (@memory_multi_pointer_sequence_used_register (memory_recursive_limits nest cap) operations (memory_nest_iterators nest)
      scalars extent fe ge locals identifier index VALID LOOKUP leaf_temps memory leaf_after leaf_final LEAF operation IN USE)
      as [word WORD].
    exists word; rewrite (FRAME identifier ltac:(apply in_or_app; right; assumption)) in WORD; exact WORD. }
  exact TYPED.
Qed.
Print Assumptions memory_multi_pointer_source_first_capability.

Theorem memory_multi_pointer_body_source_decode source (package : memory_multi_pointer_region_package source)
  fe ge locals counts scalar_values temps memory after final :
  length counts = length (memory_nest_iterators (multi_pointer_region_nest package)) ->
  Forall (fun count => count <> O /\ signed_range (Z.of_nat count)) counts ->
  Forall2 (fun count limit => Z.of_nat count <= limit) counts
    (memory_recursive_limits (multi_pointer_region_nest package) (multi_pointer_region_limit package)) ->
  memory_nest_bindings (memory_nest_bounds (multi_pointer_region_nest package)) (map Z.of_nat counts) temps ->
  memory_nest_initial (multi_pointer_region_nest package) temps ->
  memory_nest_bindings (multi_pointer_region_scalars package) scalar_values temps ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  L.loop_semantics (memory_scalar_rectangle 0 (length counts) (length scalar_values)
    (memory_multi_pointer_region_instructions package)) (map Z.of_nat counts++scalar_values)
    (RuntimeState (memory_multi_pointer_locations temps (multi_pointer_region_window package)) memory)
    (RuntimeState (memory_multi_pointer_locations temps (multi_pointer_region_window package)) final) /\
  after = memory_nest_exit (multi_pointer_region_nest package) counts temps.
Proof.
  destruct package as [nest cap pointers extent scalars operations CERT]; cbn in *.
  destruct CERT as [EQUAL NONEMPTY SHAPES FRESH CAP WINDOW PROTECTED UNIQUE STABLE USED OPS VALID COVERED BODY]; subst source.
  intros LENGTH COUNTS LIMITS BOUNDS INITIAL SCALARS SOURCE.
  set (physical := fun coordinates => memory_multi_pointer_sequence_physical temps (coordinates++scalar_values) operations).
  set (capability := fun le => temp_agree pointers temps le /\ memory_nest_bindings scalars scalar_values le).
  assert (DISJOINT : forall identifier, In identifier (memory_nest_iterators nest) -> ~ In identifier (pointers++scalars)).
  { intros identifier MEMBER BAD; apply in_app_iff in BAD as [BAD|BAD];
      [exact (PROTECTED identifier BAD MEMBER)|exact (STABLE identifier BAD MEMBER)]. }
  assert (CAP_FRAME : forall first second, temp_agree (pointers++scalars) first second -> capability first -> capability second).
  { intros first second FRAME [WORD WORDS]; split.
    - eapply temp_agree_trans; [exact WORD|].
      eapply temp_agree_weaken; [|exact FRAME]; intros; apply in_or_app; left; assumption.
    - eapply memory_nest_bindings_frame_from; [|exact FRAME|exact WORDS]; intros; apply in_or_app; right; assumption. }
  assert (DECODE : forall coordinates le before next target, memory_nary_domain counts [] coordinates ->
    memory_nest_bindings (memory_nest_iterators nest) coordinates le -> capability le ->
    exec_stmt fe ge locals le before (memory_nest_leaf nest) E0 next target Out_normal -> physical coordinates before target /\ next = le).
  { intros coordinates le before next target DOMAIN WORDS [WORD SCALAR_WORDS] RUN.
    assert (FULL_WORDS : memory_nest_bindings (memory_nest_iterators nest++scalars) (coordinates++scalar_values) le)
      by (apply memory_nest_bindings_append; assumption).
    destruct (memory_nest_bindings_valuation UNIQUE FULL_WORDS) as [valuation [VALUES BINDINGS]].
    assert (COORDINATES : map valuation (memory_nest_iterators nest) = coordinates).
    { apply memory_list_prefix_equal with (trailing := map valuation scalars) (other := scalar_values).
      - rewrite length_map; apply Forall2_length in WORDS; exact WORDS.
      - rewrite <- map_app; exact VALUES. }
    unfold physical; rewrite <- VALUES; apply flatten_region_execution in RUN; rewrite BODY in RUN.
    destruct (@memory_multi_pointer_sequence_tail_inverse (memory_recursive_limits nest cap) operations
      (memory_nest_iterators nest) scalars extent fe ge locals valuation le before next target VALID
      ltac:(rewrite COORDINATES; eapply memory_nary_domain_ranges; eassumption) BINDINGS RUN) as [ACTION EXIT].
    split; [|exact EXIT].
    eapply memory_multi_pointer_sequence_frame; [exact COVERED| |exact ACTION].
    intros identifier MEMBER; symmetry; exact (WORD identifier MEMBER).
 }
  destruct (@memory_recursive_source_decode_framed fe ge locals nest (pointers++scalars) capability CAP_FRAME SHAPES FRESH DISJOINT
    (@memory_pointer_sequence_normal operations (memory_nest_leaf nest) BODY)
    (@memory_pointer_sequence_quiet operations (memory_nest_leaf nest) BODY)
    (@memory_pointer_sequence_writes operations (memory_nest_leaf nest) BODY)
    counts physical [] [] temps memory after final LENGTH COUNTS ltac:(cbn; tauto) DECODE
    ltac:(constructor) BOUNDS INITIAL ltac:(split; [apply temp_agree_refl|exact SCALARS]) SOURCE) as [ITER EXIT].
  split; [|exact EXIT].
  assert (POINT : forall coordinates before target, memory_nary_domain counts [] coordinates ->
    (physical coordinates before target <-> memory_scalar_sequence_point (memory_pad_instructions (length scalars) (map memory_nary_compute_instruction operations))
      coordinates scalar_values (RuntimeState (memory_multi_pointer_locations temps extent) before)
      (RuntimeState (memory_multi_pointer_locations temps extent) target))).
  { intros coordinates before target DOMAIN; unfold physical,memory_scalar_sequence_point; rewrite memory_pad_sequence_point.
    assert (RANGES : memory_nary_ranges (memory_recursive_limits nest cap) coordinates)
      by (eapply memory_nary_domain_ranges; eassumption).
    apply memory_multi_pointer_sequence_point_execution with (limits := memory_recursive_limits nest cap)
      (layout := memory_nest_iterators nest) (scalars := scalars); [exact VALID|exact RANGES|].
    apply Forall2_length in RANGES; unfold memory_recursive_limits in RANGES; rewrite repeat_length in RANGES; lia. }
  apply (proj1 (@memory_scalar_rectangle_lift (memory_multi_pointer_locations temps extent)
    (memory_pad_instructions (length scalars) (map memory_nary_compute_instruction operations)) physical counts scalar_values memory final POINT)); exact ITER.
Qed.
Print Assumptions memory_multi_pointer_body_source_decode.
