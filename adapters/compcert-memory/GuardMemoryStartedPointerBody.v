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
From GuardMemory Require Import GuardMemoryParamPointerSyntax GuardMemoryPointerSourceWords.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

From GuardMemory Require Import GuardMemoryStartedFramedSource GuardMemoryStartedScalarLoop GuardMemoryStartedScalarLift.
Theorem memory_started_pointer_body_source_decode source (package : memory_param_pointer_region_package source)
  iterator bound body child fe ge locals upper count counts start parameter_values scalar_values temps memory after final :
  param_pointer_region_nest package = MemorySourceAxis iterator bound body child ->
  length counts = length (memory_nest_iterators child) ->
  Forall (fun count => count <> O /\ signed_range (Z.of_nat count)) counts ->
  count <> O -> 0 <= start -> signed_range start ->
  0 < Z.of_nat upper -> signed_range (Z.of_nat upper) -> Z.of_nat upper = start+Z.of_nat count ->
  Forall2 (fun count limit => Z.of_nat count <= limit) (upper::counts)
    (param_pointer_region_limits package) ->
  memory_nest_bindings (memory_nest_bounds (param_pointer_region_nest package)) (map Z.of_nat (upper::counts)) temps ->
  temps ! iterator = Some (Vint (Int.repr start)) ->
  memory_nest_bindings (param_pointer_region_parameters package) parameter_values temps ->
  memory_nary_ranges (param_pointer_region_parameter_limits package) parameter_values ->
  memory_nest_bindings (param_pointer_region_scalars package) scalar_values temps ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  L.loop_semantics (memory_started_scalar_loop (S (length counts)) (length (parameter_values++scalar_values))
    (memory_param_pointer_region_instructions package)) (map Z.of_nat (upper::counts)++(parameter_values++scalar_values)++[start])
    (RuntimeState (memory_multi_pointer_locations temps (param_pointer_region_window package)) memory)
    (RuntimeState (memory_multi_pointer_locations temps (param_pointer_region_window package)) final) /\
  after = memory_nest_exit (param_pointer_region_nest package) (upper::counts) temps.
Proof.
  destruct package as [nest caps parameters parameter_caps pointers extent scalars operations CERT]; cbn in *.
  destruct CERT as [EQUAL NONEMPTY SHAPES FRESH CAPS_LENGTH CAPS PARAM_LENGTH PARAM_CAPS PARAM_STABLE PARAM_USED WINDOW PROTECTED UNIQUE STABLE USED OPS VALID COVERED BODY].
  intros NEST LENGTH COUNTS ROOT_POS START_NONNEG START_RANGE UPPER_POS UPPER_RANGE SPAN LIMITS BOUNDS INITIAL PARAMETERS PARAM_RANGES SCALARS SOURCE.
  subst nest; subst source.
  set (nest := MemorySourceAxis iterator bound body child) in *.
  set (physical := fun coordinates => memory_multi_pointer_sequence_physical temps ((coordinates++parameter_values)++scalar_values) operations).
  set (capability := fun le => temp_agree pointers temps le /\ memory_nest_bindings parameters parameter_values le /\ memory_nest_bindings scalars scalar_values le).
  assert (DISJOINT : forall identifier, In identifier (memory_nest_iterators nest) -> ~ In identifier (pointers++parameters++scalars)).
  { intros identifier MEMBER BAD; repeat rewrite in_app_iff in BAD.
    destruct BAD as [BAD|[BAD|BAD]];
      [exact (PROTECTED identifier BAD MEMBER)|exact (PARAM_STABLE identifier BAD MEMBER)|exact (STABLE identifier BAD MEMBER)]. }
  assert (CAP_FRAME : forall first second, temp_agree (pointers++parameters++scalars) first second -> capability first -> capability second).
  { intros first second FRAME [WORD [PARAM_WORDS WORDS]]; split.
    - eapply temp_agree_trans; [exact WORD|].
      eapply temp_agree_weaken; [|exact FRAME]; intros; apply in_or_app; left; assumption.
    - split.
      + eapply memory_nest_bindings_frame_from; [|exact FRAME|exact PARAM_WORDS]; intros; apply in_or_app; right; apply in_or_app; left; assumption.
      + eapply memory_nest_bindings_frame_from; [|exact FRAME|exact WORDS]; intros; apply in_or_app; right; apply in_or_app; right; assumption. }
  assert (DECODE : forall coordinates le before next target, memory_started_domain upper counts start coordinates ->
    memory_nest_bindings (memory_nest_iterators nest) coordinates le -> capability le ->
    exec_stmt fe ge locals le before (memory_nest_leaf nest) E0 next target Out_normal -> physical coordinates before target /\ next = le).
  { intros coordinates le before next target DOMAIN WORDS [WORD [PARAM_WORDS SCALAR_WORDS]] RUN.
    pose proof (@memory_started_domain_subset upper counts start coordinates START_NONNEG DOMAIN) as OLD_DOMAIN.
    assert (GEOMETRY_WORDS : memory_nest_bindings (memory_nest_iterators nest++parameters) (coordinates++parameter_values) le)
      by (apply memory_nest_bindings_append; assumption).
    assert (FULL_WORDS : memory_nest_bindings ((memory_nest_iterators nest++parameters)++scalars)
      ((coordinates++parameter_values)++scalar_values) le)
      by (apply memory_nest_bindings_append; assumption).
    destruct (memory_nest_bindings_valuation UNIQUE FULL_WORDS) as [valuation [VALUES BINDINGS]].
    assert (GEOMETRY : map valuation (memory_nest_iterators nest++parameters) = coordinates++parameter_values).
    { apply memory_list_prefix_equal with (trailing := map valuation scalars) (other := scalar_values).
      - rewrite length_map; apply Forall2_length in GEOMETRY_WORDS; exact GEOMETRY_WORDS.
      - rewrite <- map_app; exact VALUES. }
    unfold physical; rewrite <- VALUES; apply flatten_region_execution in RUN; rewrite BODY in RUN.
    destruct (@memory_multi_pointer_sequence_tail_inverse (caps++parameter_caps) operations
      (memory_nest_iterators nest++parameters) scalars extent fe ge locals valuation le before next target VALID
      ltac:(rewrite GEOMETRY; unfold memory_nary_ranges; apply Forall2_app;
        [eapply memory_nary_domain_ranges; eassumption|exact PARAM_RANGES]) BINDINGS RUN) as [ACTION EXIT].
    split; [|exact EXIT].
    eapply memory_multi_pointer_sequence_frame; [exact COVERED| |exact ACTION].
    intros identifier MEMBER; symmetry; exact (WORD identifier MEMBER).
 }
  destruct (@memory_started_source_decode_framed fe ge locals iterator bound body child
    (pointers++parameters++scalars) capability CAP_FRAME SHAPES FRESH DISJOINT
    (@memory_pointer_sequence_normal operations (memory_nest_leaf nest) BODY)
    (@memory_pointer_sequence_quiet operations (memory_nest_leaf nest) BODY)
    (@memory_pointer_sequence_writes operations (memory_nest_leaf nest) BODY)
    upper count counts start physical [] [] temps memory after final LENGTH COUNTS ROOT_POS UPPER_POS UPPER_RANGE
    START_RANGE SPAN ltac:(cbn; tauto) DECODE ltac:(constructor) BOUNDS INITIAL
    ltac:(split; [apply temp_agree_refl|split; [exact PARAMETERS|exact SCALARS]]) SOURCE) as [ITER EXIT].
  split; [|exact EXIT].
  assert (POINT : forall coordinates before target, memory_started_domain upper counts start coordinates ->
    (physical coordinates before target <-> memory_scalar_sequence_point (memory_pad_instructions (length scalars) (map memory_nary_compute_instruction operations))
      coordinates (parameter_values++scalar_values) (RuntimeState (memory_multi_pointer_locations temps extent) before)
      (RuntimeState (memory_multi_pointer_locations temps extent) target))).
  { intros coordinates before target DOMAIN;
    pose proof (@memory_started_domain_subset upper counts start coordinates START_NONNEG DOMAIN) as OLD_DOMAIN; unfold physical,memory_scalar_sequence_point; rewrite memory_pad_sequence_point.
    rewrite app_assoc.
    assert (RANGES : memory_nary_ranges (caps++parameter_caps) (coordinates++parameter_values)).
    { unfold memory_nary_ranges; apply Forall2_app; [eapply memory_nary_domain_ranges; eassumption|exact PARAM_RANGES]. }
    apply memory_multi_pointer_sequence_point_execution with (limits := caps++parameter_caps)
      (layout := memory_nest_iterators nest++parameters) (scalars := scalars); [exact VALID|exact RANGES|].
    rewrite !length_app; pose proof (@Forall2_length _ _ _ _ _ RANGES) as RANGE_LENGTH.
    rewrite !length_app,CAPS_LENGTH,PARAM_LENGTH in RANGE_LENGTH; exact (eq_sym RANGE_LENGTH). }
  apply (proj1 (@memory_started_scalar_loop_lift (memory_multi_pointer_locations temps extent)
    (memory_pad_instructions (length scalars) (map memory_nary_compute_instruction operations)) physical upper counts (parameter_values++scalar_values) start count memory final SPAN POINT)); exact ITER.
Qed.
Print Assumptions memory_started_pointer_body_source_decode.
