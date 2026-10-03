From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCountedLoop ClightTempFrame ClightFiniteRegion ClightStraightLine ClightNoWrap.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryNaryRanges GuardMemoryNaryLoops
  GuardMemoryNaryLift GuardMemoryRecursiveSource GuardMemoryRecursiveSyntax GuardMemoryRecursiveBody GuardMemoryRecursiveFramedExecution GuardMemoryRecursiveFirstLeaf
  GuardMemoryPointerSequence GuardMemoryPointerSyntax GuardMemoryPointerCompute GuardMemoryNaryCompute GuardMemoryNaryAffineAccess GuardMemoryBufferOffsets.
From GuardMemory Require Import GuardMemoryScalarPointerSyntax GuardMemoryScalarPointerSequence GuardMemoryScalarPointerCompute GuardMemoryRecursiveDomain GuardMemoryScalarLoops GuardMemoryScalarLift GuardMemorySourceParameters.
From GuardMemory Require Import GuardMemoryInstructionPadding.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_scalar_register_bindings identifiers temps :
  (forall identifier, In identifier identifiers -> exists word, temps ! identifier = Some (Vint word)) ->
  memory_nest_bindings identifiers (memory_recursive_parameters identifiers temps) temps.
Proof.
  intro WORDS; induction identifiers as [|identifier identifiers IH]; cbn [memory_recursive_parameters map]; constructor.
  - destruct (WORDS identifier ltac:(cbn; auto)) as [word WORD].
    unfold temp_word; rewrite WORD,Int.repr_signed; reflexivity.
  - apply IH; intros key MEMBER; apply WORDS; cbn; auto.
Qed.
Theorem memory_scalar_pointer_source_first_capability source (package : memory_scalar_pointer_region_package source) fe ge locals temps memory after final :
  Forall (fun bound => 0 < Int.signed (temp_word bound temps)) (memory_nest_bounds (scalar_pointer_region_nest package)) ->
  memory_nest_initial (scalar_pointer_region_nest package) temps ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists block base, temps ! (scalar_pointer_region_pointer package) = Some (Vptr block base) /\
    forall identifier, In identifier (scalar_pointer_region_scalars package) -> exists word, temps ! identifier = Some (Vint word).
Proof.
  intros POSITIVE INITIAL SOURCE.
  destruct package as [nest cap pointer extent scalars operations CERT]; cbn in *.
  destruct CERT as [EQUAL NONEMPTY SHAPES FRESH CAP WINDOW PROTECTED UNIQUE STABLE USED OPS VALID BODY]; subst source.
  assert (DISJOINT : forall identifier, In identifier (memory_nest_iterators nest) -> ~ In identifier (pointer::scalars)).
  { intros identifier MEMBER [SAME|BAD].
    - subst identifier; contradiction.
    - exact (STABLE identifier BAD MEMBER). }
  destruct (@memory_recursive_first_leaf fe ge locals nest SHAPES FRESH
    (@memory_pointer_sequence_normal operations (memory_nest_leaf nest) BODY)
    (@memory_pointer_sequence_quiet operations (memory_nest_leaf nest) BODY)
    (@memory_pointer_sequence_writes operations (memory_nest_leaf nest) BODY) (pointer::scalars) temps memory after final
    DISJOINT POSITIVE INITIAL SOURCE) as [leaf_temps [leaf_after [leaf_final [FRAME LEAF]]]].
  apply flatten_region_execution in LEAF; rewrite BODY in LEAF.
  assert (TYPED : forall identifier, In identifier scalars -> exists word, temps ! identifier = Some (Vint word)).
  { intros identifier MEMBER; destruct (USED identifier MEMBER) as [operation [index [IN [LOOKUP USE]]]].
    destruct (@memory_scalar_pointer_sequence_used_register (memory_recursive_limits nest cap) operations (memory_nest_iterators nest)
      scalars pointer extent fe ge locals identifier index VALID LOOKUP leaf_temps memory leaf_after leaf_final LEAF operation IN USE)
      as [word WORD].
    exists word; rewrite (FRAME identifier ltac:(cbn; auto)) in WORD; exact WORD. }
  destruct operations as [|operation operations]; [contradiction|].
  cbn [map] in LEAF; inversion LEAF; subst.
  match goal with POINT : exec_stmt _ _ _ _ _ (memory_pointer_compute_statement operation) _ _ _ _ |- _ =>
    destruct (@memory_pointer_statement_has_base operation fe ge locals leaf_temps memory _ _ POINT) as [block [base POINTER]] end.
  inversion VALID as [|head tail HEAD TAIL]; subst head tail.
  destruct HEAD as [[OTHER [ID EXTENT]] REST]; rewrite ID in POINTER.
  exists block,base; split.
  - rewrite <- (FRAME pointer ltac:(cbn; auto)); exact POINTER.
  - exact TYPED.
Qed.
Print Assumptions memory_scalar_pointer_source_first_capability.

Lemma memory_list_prefix_equal {A} (first second trailing other : list A) :
  length first = length second -> first++trailing = second++other -> first = second.
Proof.
  revert second; induction first as [|head first IH]; intros [|value second] LENGTH SAME;
    cbn in LENGTH,SAME; try discriminate; [reflexivity|].
  inversion SAME; subst value; f_equal; eapply IH; [lia|eassumption].
Qed.
Theorem memory_scalar_pointer_body_source_decode source (package : memory_scalar_pointer_region_package source)
  fe ge locals counts scalar_values temps memory after final block base :
  length counts = length (memory_nest_iterators (scalar_pointer_region_nest package)) ->
  Forall (fun count => count <> O /\ signed_range (Z.of_nat count)) counts ->
  Forall2 (fun count limit => Z.of_nat count <= limit) counts
    (memory_recursive_limits (scalar_pointer_region_nest package) (scalar_pointer_region_limit package)) ->
  memory_nest_bindings (memory_nest_bounds (scalar_pointer_region_nest package)) (map Z.of_nat counts) temps ->
  memory_nest_initial (scalar_pointer_region_nest package) temps ->
  temps ! (scalar_pointer_region_pointer package) = Some (Vptr block base) ->
  memory_nest_bindings (scalar_pointer_region_scalars package) scalar_values temps ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  L.loop_semantics (memory_scalar_rectangle 0 (length counts) (length scalar_values)
    (memory_scalar_pointer_region_instructions package)) (map Z.of_nat counts++scalar_values)
    (RuntimeState (memory_pointer_buffer_locations (scalar_pointer_region_pointer package) block base
      (scalar_pointer_region_window package)) memory)
    (RuntimeState (memory_pointer_buffer_locations (scalar_pointer_region_pointer package) block base
      (scalar_pointer_region_window package)) final) /\
  after = memory_nest_exit (scalar_pointer_region_nest package) counts temps.
Proof.
  destruct package as [nest cap pointer extent scalars operations CERT]; cbn in *.
  destruct CERT as [EQUAL NONEMPTY SHAPES FRESH CAP WINDOW PROTECTED UNIQUE STABLE USED OPS VALID BODY]; subst source.
  intros LENGTH COUNTS LIMITS BOUNDS INITIAL POINTER SCALARS SOURCE.
  set (physical := fun coordinates => memory_pointer_sequence_physical block base (coordinates++scalar_values) operations).
  set (capability := fun le => le ! pointer = Some (Vptr block base) /\ memory_nest_bindings scalars scalar_values le).
  assert (DISJOINT : forall identifier, In identifier (memory_nest_iterators nest) -> ~ In identifier (pointer::scalars)).
  { intros identifier MEMBER [SAME|BAD]; [subst; contradiction|exact (STABLE identifier BAD MEMBER)]. }
  assert (CAP_FRAME : forall first second, temp_agree (pointer::scalars) first second -> capability first -> capability second).
  { intros first second FRAME [WORD WORDS]; split.
    - rewrite FRAME by (cbn; auto); exact WORD.
    - eapply memory_nest_bindings_frame_from; [|exact FRAME|exact WORDS]; intros; cbn; auto. }
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
    eapply memory_scalar_pointer_sequence_tail_inverse; [exact VALID| |exact BINDINGS|exact WORD|exact RUN].
    rewrite COORDINATES; eapply memory_nary_domain_ranges; eassumption. }
  destruct (@memory_recursive_source_decode_framed fe ge locals nest (pointer::scalars) capability CAP_FRAME SHAPES FRESH DISJOINT
    (@memory_pointer_sequence_normal operations (memory_nest_leaf nest) BODY)
    (@memory_pointer_sequence_quiet operations (memory_nest_leaf nest) BODY)
    (@memory_pointer_sequence_writes operations (memory_nest_leaf nest) BODY)
    counts physical [] [] temps memory after final LENGTH COUNTS ltac:(cbn; tauto) DECODE
    ltac:(constructor) BOUNDS INITIAL ltac:(split; assumption) SOURCE) as [ITER EXIT].
  split; [|exact EXIT].
  assert (POINT : forall coordinates before target, memory_nary_domain counts [] coordinates ->
    (physical coordinates before target <-> memory_scalar_sequence_point (memory_pad_instructions (length scalars) (map memory_nary_compute_instruction operations))
      coordinates scalar_values (RuntimeState (memory_pointer_buffer_locations pointer block base extent) before)
      (RuntimeState (memory_pointer_buffer_locations pointer block base extent) target))).
  { intros coordinates before target DOMAIN; unfold physical,memory_scalar_sequence_point; rewrite memory_pad_sequence_point.
    assert (RANGES : memory_nary_ranges (memory_recursive_limits nest cap) coordinates)
      by (eapply memory_nary_domain_ranges; eassumption).
    apply memory_scalar_pointer_sequence_point_execution with (limits := memory_recursive_limits nest cap)
      (layout := memory_nest_iterators nest) (scalars := scalars); [exact VALID|exact RANGES|].
    apply Forall2_length in RANGES; unfold memory_recursive_limits in RANGES; rewrite repeat_length in RANGES; lia. }
  apply (proj1 (@memory_scalar_rectangle_lift (memory_pointer_buffer_locations pointer block base extent)
    (memory_pad_instructions (length scalars) (map memory_nary_compute_instruction operations)) physical counts scalar_values memory final POINT)); exact ITER.
Qed.
Print Assumptions memory_scalar_pointer_body_source_decode.
