From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightTempFrame ClightCountedLoop
  ClightRedundantSet ClightStraightLine ClightRectangularGuard ClightRegionProgress ClightFiniteRegion ClightLoopSyntax.
From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryRecursiveGuard
  GuardMemoryRecursiveWords GuardMemoryRecursiveDomain.
From GuardMemory Require Import GuardMemoryVectorBounds.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_vector_parameter_data caps bounds ge locals temps memory :
  Forall2 (fun cap bound => register_range bound cap (Entry ge locals temps memory)) caps bounds ->
  memory_nest_bindings bounds (map Z.of_nat (memory_recursive_counts bounds temps)) temps /\
  map Z.of_nat (memory_recursive_counts bounds temps) = memory_recursive_parameters bounds temps /\
  Forall (fun count => count <> O /\ signed_range (Z.of_nat count)) (memory_recursive_counts bounds temps) /\
  Forall2 (fun count limit => Z.of_nat count <= limit) (memory_recursive_counts bounds temps) caps.
Proof.
  intro RANGES; induction RANGES as [|cap bound caps bounds [[word WORD] RANGE] RANGES IH];
    unfold memory_recursive_counts,memory_recursive_parameters in *; cbn [map length].
  - repeat split; constructor.
  - cbn [entry_temps] in WORD,RANGE; unfold temp_word in *; rewrite WORD in *.
    assert (COUNT : Z.of_nat (Z.to_nat (Int.signed word)) = Int.signed word) by (apply Z2Nat.id; lia).
    destruct IH as [BINDINGS [VALUES [COUNTS LIMITS]]]; repeat split.
    + constructor; [rewrite COUNT,Int.repr_signed; exact WORD|exact BINDINGS].
    + rewrite COUNT,VALUES; reflexivity.
    + constructor; [split; [intro ZERO; rewrite ZERO in COUNT; cbn in COUNT; lia|rewrite COUNT; apply Int.signed_range]|exact COUNTS].
    + constructor; [rewrite COUNT; exact (proj2 RANGE)|exact LIMITS].
Qed.

Theorem memory_vector_source_bound_words fe ge locals nest caps :
  length caps = length (memory_nest_bounds nest) -> Forall signed_range caps ->
  memory_nest_shapes nest -> memory_nest_fresh nest ->
  normal_statement (memory_nest_leaf nest) = true -> quiet_statement (memory_nest_leaf nest) = true ->
  writes_only [] (memory_nest_leaf nest) ->
  forall temps memory after final, memory_nest_initial nest temps ->
  exec_stmt fe ge locals temps memory (memory_nest_source nest) E0 after final Out_normal ->
  memory_vector_bounds_domain caps (memory_nest_bounds nest) (Entry ge locals temps memory).
Proof.
  intros LENGTH CAPS SHAPES FRESH NORMAL QUIET WRITES temps memory after final INITIAL SOURCE.
  eapply memory_vector_bounds_domain_from_uniform with (upper := Int.max_signed).
  - exact LENGTH.
  - eapply Forall_impl; [|exact CAPS]; intros cap SIGNED; split; [exact SIGNED|exact (proj2 SIGNED)].
  - unfold signed_range; split; [change (-2147483648 <= 2147483647); lia|lia].
  - eapply memory_recursive_source_bound_words; eauto.
    unfold signed_range; split; [change (-2147483648 <= 2147483647); lia|lia].
Qed.
Print Assumptions memory_vector_parameter_data.
Print Assumptions memory_vector_source_bound_words.
