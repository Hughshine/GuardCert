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
From GuardMemory Require Import GuardMemoryWindowSyntax GuardMemoryWindowPackage GuardMemoryWindowBody GuardMemoryWindowFirstLeaf GuardMemoryWindowCells GuardMemoryIntervalBox.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem window_source_under_ranges source (package : window_region_package source)
  iterator bound body child fe ge locals temps memory after final :
  window_region_nest package = MemorySourceAxis iterator bound body child ->
  window_region_root_lower package <= Int.signed (temp_word iterator temps) < Int.signed (temp_word bound temps) ->
  Forall2 (fun cap bound => register_range bound cap (Entry ge locals temps memory))
    (window_region_caps package) (memory_nest_bounds (window_region_nest package)) ->
  interval_ranges (window_region_parameter_bounds package)
    (memory_recursive_parameters (window_region_parameters package) temps) ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  memory_nest_bindings (window_region_parameters package)
      (memory_recursive_parameters (window_region_parameters package) temps) temps /\
  memory_nest_bindings (window_region_scalars package)
      (memory_recursive_parameters (window_region_scalars package) temps) temps /\
  L.loop_semantics (memory_started_scalar_loop (length (memory_nest_iterators (window_region_nest package)))
      (length (window_region_parameters package++window_region_scalars package))
      (window_region_instructions package))
      (memory_recursive_parameters (memory_nest_bounds (window_region_nest package)) temps++
        (memory_recursive_parameters (window_region_parameters package) temps++
         memory_recursive_parameters (window_region_scalars package) temps)++[Int.signed (temp_word iterator temps)])
      (RuntimeState (window_multi_pointer_locations temps (window_region_lower package) (window_region_upper package)) memory)
      (RuntimeState (window_multi_pointer_locations temps (window_region_lower package) (window_region_upper package)) final) /\
  after = memory_recursive_exit (window_region_nest package) temps.
Proof.
  intros NEST [START_LOWER ACTIVE] RANGES PARAM_RANGES SOURCE.
  assert (POSITIVE : Forall (fun key => 0 < Int.signed (temp_word key temps))
    (memory_nest_bounds (window_region_nest package))).
  { induction RANGES; constructor; [exact (proj1 (proj2 H))|exact IHRANGES]. }
  assert (CHILD_POSITIVE : Forall (fun key => 0 < Int.signed (temp_word key temps)) (memory_nest_bounds child)).
  { rewrite NEST in POSITIVE; inversion POSITIVE; assumption. }
  pose proof (@window_source_first_capability _ _ _ _ _ _ _ _ _ _ _ (window_region_certificate package) iterator bound body child fe ge locals
    temps memory after final NEST CHILD_POSITIVE ACTIVE SOURCE) as TYPED.
  assert (SCALARS : memory_nest_bindings (window_region_scalars package)
    (memory_recursive_parameters (window_region_scalars package) temps) temps)
    by (apply memory_scalar_register_bindings; intros identifier MEMBER; apply TYPED; apply in_or_app; right; exact MEMBER).
  assert (PARAMETERS : memory_nest_bindings (window_region_parameters package)
    (memory_recursive_parameters (window_region_parameters package) temps) temps)
    by (apply memory_scalar_register_bindings; intros identifier MEMBER; apply TYPED; apply in_or_app; left; exact MEMBER).
  destruct (@memory_vector_parameter_data (window_region_caps package) (memory_nest_bounds (window_region_nest package))
    ge locals temps memory RANGES) as [BINDINGS [VALUES [COUNTS LIMITS]]].
  assert (LENGTH : length (memory_recursive_counts (memory_nest_bounds (window_region_nest package)) temps) =
    S (length (memory_nest_iterators child))).
  { unfold memory_recursive_counts,memory_recursive_parameters; rewrite !length_map,<-memory_nest_lengths,NEST; reflexivity. }
  remember (memory_recursive_counts (memory_nest_bounds (window_region_nest package)) temps) as all_counts eqn:ALL_COUNTS.
  destruct all_counts as [|upper counts]; [discriminate LENGTH|].
  assert (CHILD_LENGTH : length counts = length (memory_nest_iterators child)) by (cbn in LENGTH; lia).
  inversion COUNTS as [|same rest [UPPER_NONZERO UPPER_RANGE] CHILD_COUNTS]; subst same rest.
  assert (UPPER_POSITIVE : 0 < Z.of_nat upper) by (destruct upper; [contradiction|cbn; lia]).
  assert (SOURCE_ROOT : temps ! iterator = Some (Vint (Int.repr (Int.signed (temp_word iterator temps))))).
  { assert (ROOT_DOMAIN : register_domain iterator (Entry ge locals temps memory)).
    { eapply memory_recursive_source_iterator_word.
      rewrite <-NEST,<- (window_source_exact (window_region_certificate package)); exact SOURCE. }
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
  destruct (@window_body_source_decode _ _ _ _ _ _ _ _ _ _ _ (window_region_certificate package) iterator bound body child fe ge locals
    upper count counts start (memory_recursive_parameters (window_region_parameters package) temps)
    (memory_recursive_parameters (window_region_scalars package) temps) temps memory after final
    NEST CHILD_LENGTH CHILD_COUNTS ROOT_POSITIVE START_LOWER START_RANGE UPPER_POSITIVE UPPER_RANGE SPAN LIMITS
    BINDINGS SOURCE_ROOT PARAMETERS PARAM_RANGES SCALARS SOURCE) as [LOOP EXIT].
  split; [exact PARAMETERS|]; split; [exact SCALARS|]; split.
  - rewrite VALUES in LOOP; rewrite NEST; cbn [memory_nest_iterators length].
    replace (length (memory_recursive_parameters (window_region_parameters package) temps++
      memory_recursive_parameters (window_region_scalars package) temps)) with
      (length (window_region_parameters package++window_region_scalars package)) in LOOP
      by (unfold memory_recursive_parameters; rewrite !length_app,!length_map; reflexivity).
    rewrite CHILD_LENGTH,NEST in LOOP; exact LOOP.
  - rewrite EXIT; apply memory_recursive_exit_counts; exact VALUES.
Qed.
Print Assumptions window_source_under_ranges.
