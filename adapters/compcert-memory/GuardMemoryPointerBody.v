From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCountedLoop ClightTempFrame ClightFiniteRegion ClightStraightLine ClightNoWrap.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryNaryRanges GuardMemoryNaryLoops
  GuardMemoryNaryLift GuardMemoryRecursiveSource GuardMemoryRecursiveSyntax GuardMemoryRecursiveBody GuardMemoryRecursiveFramedExecution GuardMemoryRecursiveFirstLeaf
  GuardMemoryPointerSequence GuardMemoryPointerSyntax GuardMemoryPointerCompute GuardMemoryNaryCompute GuardMemoryNaryAffineAccess GuardMemoryBufferOffsets.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem memory_pointer_source_first_base source (package : memory_pointer_region_package source) fe ge locals temps memory after final :
  Forall (fun bound => 0 < Int.signed (temp_word bound temps)) (memory_nest_bounds (pointer_region_nest package)) ->
  memory_nest_initial (pointer_region_nest package) temps ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists block base, temps ! (pointer_region_pointer package) = Some (Vptr block base).
Proof.
  intros POSITIVE INITIAL SOURCE.
  destruct package as [nest cap pointer extent operations CERT]; cbn in *.
  destruct CERT as [EQUAL NONEMPTY SHAPES FRESH CAP WINDOW PROTECTED OPS VALID BODY]; subst source.
  destruct (@memory_recursive_first_leaf fe ge locals nest SHAPES FRESH
    (@memory_pointer_sequence_normal operations (memory_nest_leaf nest) BODY)
    (@memory_pointer_sequence_quiet operations (memory_nest_leaf nest) BODY)
    (@memory_pointer_sequence_writes operations (memory_nest_leaf nest) BODY) [pointer] temps memory after final
    ltac:(intros identifier MEMBER BAD; cbn in BAD; destruct BAD as [SAME|[]]; subst; contradiction)
    POSITIVE INITIAL SOURCE) as [leaf_temps [leaf_after [leaf_final [FRAME LEAF]]]].
  destruct operations as [|operation operations]; [contradiction|].
  apply flatten_region_execution in LEAF; rewrite BODY in LEAF; cbn [map] in LEAF; inversion LEAF; subst.
  match goal with POINT : exec_stmt _ _ _ _ _ (memory_pointer_compute_statement operation) _ _ _ _ |- _ =>
    destruct (@memory_pointer_statement_has_base operation fe ge locals leaf_temps memory _ _ POINT) as [block [base POINTER]] end.
  inversion VALID as [|head tail HEAD TAIL]; subst head tail.
  destruct HEAD as [[OTHER [ID EXTENT]] REST]; rewrite ID in POINTER.
  exists block,base; rewrite <- (FRAME pointer ltac:(cbn; auto)); exact POINTER.
Qed.

Theorem memory_pointer_body_source_decode source (package : memory_pointer_region_package source)
  fe ge locals counts temps memory after final block base :
  length counts = length (memory_nest_iterators (pointer_region_nest package)) ->
  Forall (fun count => count <> O /\ signed_range (Z.of_nat count)) counts ->
  Forall2 (fun count limit => Z.of_nat count <= limit) counts (memory_recursive_limits (pointer_region_nest package) (pointer_region_limit package)) ->
  memory_nest_bindings (memory_nest_bounds (pointer_region_nest package)) (map Z.of_nat counts) temps ->
  memory_nest_initial (pointer_region_nest package) temps ->
  temps ! (pointer_region_pointer package) = Some (Vptr block base) ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  L.loop_semantics (memory_nary_rectangle 0 (length counts) (memory_pointer_region_instructions package)) (map Z.of_nat counts)
    (RuntimeState (memory_pointer_buffer_locations (pointer_region_pointer package) block base (pointer_region_window package)) memory)
    (RuntimeState (memory_pointer_buffer_locations (pointer_region_pointer package) block base (pointer_region_window package)) final) /\
  after = memory_nest_exit (pointer_region_nest package) counts temps.
Proof.
  destruct package as [nest cap pointer extent operations CERT]; cbn in *.
  destruct CERT as [EQUAL NONEMPTY SHAPES FRESH CAP WINDOW PROTECTED OPS VALID BODY]; subst source.
  intros LENGTH COUNTS LIMITS BOUNDS INITIAL POINTER SOURCE.
  set (physical := fun values => memory_pointer_sequence_physical block base values operations).
  assert (CAP_FRAME : forall first second, temp_agree [pointer] first second ->
    first ! pointer = Some (Vptr block base) -> second ! pointer = Some (Vptr block base)).
  { intros first second FRAME WORD; rewrite FRAME; [exact WORD|cbn; auto]. }
  assert (DECODE : forall values le before next target, memory_nary_domain counts [] values ->
    memory_nest_bindings (memory_nest_iterators nest) values le -> le ! pointer = Some (Vptr block base) ->
    exec_stmt fe ge locals le before (memory_nest_leaf nest) E0 next target Out_normal -> physical values before target /\ next = le).
  { intros values le before next target DOMAIN WORDS WORD RUN.
    destruct (memory_nest_bindings_valuation (proj1 FRESH) WORDS) as [valuation [VALUES BINDINGS]].
    rewrite <- VALUES; unfold physical; apply flatten_region_execution in RUN; rewrite BODY in RUN.
    eapply memory_pointer_sequence_tail_inverse; [exact VALID| |exact BINDINGS|exact WORD|exact RUN].
    rewrite VALUES; eapply memory_nary_domain_ranges; eassumption. }
  destruct (@memory_recursive_source_decode_framed fe ge locals nest [pointer]
    (fun le => le ! pointer = Some (Vptr block base)) CAP_FRAME SHAPES FRESH
    ltac:(intros identifier MEMBER BAD; cbn in BAD; destruct BAD as [SAME|[]]; subst; contradiction)
    (@memory_pointer_sequence_normal operations (memory_nest_leaf nest) BODY)
    (@memory_pointer_sequence_quiet operations (memory_nest_leaf nest) BODY)
    (@memory_pointer_sequence_writes operations (memory_nest_leaf nest) BODY)
    counts physical [] [] temps memory after final LENGTH COUNTS ltac:(cbn; tauto) DECODE
    ltac:(constructor) BOUNDS INITIAL POINTER SOURCE) as [ITER EXIT].
  split; [|exact EXIT].
  apply (proj1 (@memory_nary_rectangle_lift (memory_pointer_buffer_locations pointer block base extent)
    (map memory_nary_compute_instruction operations) physical counts memory final
    ltac:(intros values before target DOMAIN; apply memory_pointer_sequence_point_execution with
      (limits := memory_recursive_limits nest cap) (layout := memory_nest_iterators nest);
      [exact VALID|eapply memory_nary_domain_ranges; eassumption]))).
  exact ITER.
Qed.
Print Assumptions memory_pointer_source_first_base.
Print Assumptions memory_pointer_body_source_decode.
