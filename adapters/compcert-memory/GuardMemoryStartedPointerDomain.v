From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightRedundantSet ClightCountedLoop ClightMatrixGuard ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryRecursiveSource GuardMemoryRecursiveSyntax
  GuardMemoryNaryRanges GuardMemoryRecursiveGuard GuardMemoryRecursiveWords GuardMemoryRecursiveDomain GuardMemoryRegistryGuard
  GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerBody GuardMemoryMultiPointerCells GuardMemoryScalarPointerBody GuardMemoryScalarLoops
  GuardMemoryPointerSequence GuardMemoryNaryLoops GuardMemoryBufferOffsets GuardMemoryVectorBounds GuardMemoryVectorDomain GuardMemoryVectorGuard
  GuardMemoryParamPointerSyntax.
From GuardMemory Require Import GuardMemoryStartedPointerBody GuardMemoryStartedPointerWords GuardMemoryStartedScalarLoop.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem memory_started_pointer_source_under_ranges source (package : memory_param_pointer_region_package source)
  iterator bound body child fe ge locals temps memory after final :
  param_pointer_region_nest package = MemorySourceAxis iterator bound body child ->
  0 <= Int.signed (temp_word iterator temps) < Int.signed (temp_word bound temps) ->
  Forall2 (fun cap bound => register_range bound cap (Entry ge locals temps memory))
    (param_pointer_region_limits package) (memory_nest_bounds (param_pointer_region_nest package)) ->
  memory_nary_ranges (param_pointer_region_parameter_limits package)
    (memory_recursive_parameters (param_pointer_region_parameters package) temps) ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  memory_nest_bindings (param_pointer_region_parameters package)
      (memory_recursive_parameters (param_pointer_region_parameters package) temps) temps /\
  memory_nest_bindings (param_pointer_region_scalars package)
      (memory_recursive_parameters (param_pointer_region_scalars package) temps) temps /\
  L.loop_semantics (memory_started_scalar_loop (length (memory_nest_iterators (param_pointer_region_nest package)))
      (length (param_pointer_region_parameters package++param_pointer_region_scalars package))
      (memory_param_pointer_region_instructions package))
      (memory_recursive_parameters (memory_nest_bounds (param_pointer_region_nest package)) temps++
        (memory_recursive_parameters (param_pointer_region_parameters package) temps++
         memory_recursive_parameters (param_pointer_region_scalars package) temps)++[Int.signed (temp_word iterator temps)])
      (RuntimeState (memory_multi_pointer_locations temps (param_pointer_region_window package)) memory)
      (RuntimeState (memory_multi_pointer_locations temps (param_pointer_region_window package)) final) /\
  after = memory_recursive_exit (param_pointer_region_nest package) temps.
Proof.
  intros NEST [START_NONNEG ACTIVE] RANGES PARAM_RANGES SOURCE.
  assert (POSITIVE : Forall (fun key => 0 < Int.signed (temp_word key temps))
    (memory_nest_bounds (param_pointer_region_nest package))).
  { induction RANGES; constructor; [exact (proj1 (proj2 H))|exact IHRANGES]. }
  assert (CHILD_POSITIVE : Forall (fun key => 0 < Int.signed (temp_word key temps)) (memory_nest_bounds child)).
  { rewrite NEST in POSITIVE; inversion POSITIVE; assumption. }
  pose proof (@memory_started_pointer_source_first_capability source package iterator bound body child fe ge locals
    temps memory after final NEST CHILD_POSITIVE ACTIVE SOURCE) as TYPED.
  assert (SCALARS : memory_nest_bindings (param_pointer_region_scalars package)
    (memory_recursive_parameters (param_pointer_region_scalars package) temps) temps)
    by (apply memory_scalar_register_bindings; intros identifier MEMBER; apply TYPED; apply in_or_app; right; exact MEMBER).
  assert (PARAMETERS : memory_nest_bindings (param_pointer_region_parameters package)
    (memory_recursive_parameters (param_pointer_region_parameters package) temps) temps)
    by (apply memory_scalar_register_bindings; intros identifier MEMBER; apply TYPED; apply in_or_app; left; exact MEMBER).
  destruct (@memory_vector_parameter_data (param_pointer_region_limits package) (memory_nest_bounds (param_pointer_region_nest package))
    ge locals temps memory RANGES) as [BINDINGS [VALUES [COUNTS LIMITS]]].
  assert (LENGTH : length (memory_recursive_counts (memory_nest_bounds (param_pointer_region_nest package)) temps) =
    S (length (memory_nest_iterators child))).
  { unfold memory_recursive_counts,memory_recursive_parameters; rewrite !length_map,<-memory_nest_lengths,NEST; reflexivity. }
  remember (memory_recursive_counts (memory_nest_bounds (param_pointer_region_nest package)) temps) as all_counts eqn:ALL_COUNTS.
  destruct all_counts as [|upper counts]; [discriminate LENGTH|].
  assert (CHILD_LENGTH : length counts = length (memory_nest_iterators child)) by (cbn in LENGTH; lia).
  inversion COUNTS as [|same rest [UPPER_NONZERO UPPER_RANGE] CHILD_COUNTS]; subst same rest.
  assert (UPPER_POSITIVE : 0 < Z.of_nat upper) by (destruct upper; [contradiction|cbn; lia]).
  assert (SOURCE_ROOT : temps ! iterator = Some (Vint (Int.repr (Int.signed (temp_word iterator temps))))).
  { assert (ROOT_DOMAIN : register_domain iterator (Entry ge locals temps memory)).
    { eapply memory_recursive_source_iterator_word.
      rewrite <-NEST,<- (param_pointer_region_source (param_pointer_region_syntax package)); exact SOURCE. }
    destruct ROOT_DOMAIN as [word WORD]; cbn [entry_temps] in WORD.
    unfold temp_word; rewrite WORD,Int.repr_signed; reflexivity. }
  assert (BOUND_VALUE : Z.of_nat upper = Int.signed (temp_word bound temps)).
  { rewrite NEST in VALUES; cbn [memory_nest_bounds memory_recursive_parameters map] in VALUES.
    inversion VALUES; reflexivity. }
  set (start := Int.signed (temp_word iterator temps)).
  set (count := Z.to_nat (Z.of_nat upper-start)).
  assert (SPAN : Z.of_nat upper = start+Z.of_nat count) by (unfold count,start; rewrite Z2Nat.id; lia).
  assert (ROOT_POSITIVE : count <> O).
  { intro ZERO; rewrite ZERO in SPAN; cbn in SPAN; unfold start in SPAN; lia. }
  assert (START_RANGE : signed_range start) by (unfold start; apply Int.signed_range).
  destruct (@memory_started_pointer_body_source_decode source package iterator bound body child fe ge locals
    upper count counts start (memory_recursive_parameters (param_pointer_region_parameters package) temps)
    (memory_recursive_parameters (param_pointer_region_scalars package) temps) temps memory after final
    NEST CHILD_LENGTH CHILD_COUNTS ROOT_POSITIVE START_NONNEG START_RANGE UPPER_POSITIVE UPPER_RANGE SPAN LIMITS
    BINDINGS SOURCE_ROOT PARAMETERS PARAM_RANGES SCALARS SOURCE) as [LOOP EXIT].
  split; [exact PARAMETERS|]; split; [exact SCALARS|]; split.
  - rewrite VALUES in LOOP; rewrite NEST; cbn [memory_nest_iterators length].
    replace (length (memory_recursive_parameters (param_pointer_region_parameters package) temps++
      memory_recursive_parameters (param_pointer_region_scalars package) temps)) with
      (length (param_pointer_region_parameters package++param_pointer_region_scalars package)) in LOOP
      by (unfold memory_recursive_parameters; rewrite !length_app,!length_map; reflexivity).
    rewrite CHILD_LENGTH,NEST in LOOP; exact LOOP.
  - rewrite EXIT; apply memory_recursive_exit_counts; exact VALUES.
Qed.
Print Assumptions memory_started_pointer_source_under_ranges.
