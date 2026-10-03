From Stdlib Require Import List ZArith Lia.
From Guard Require Import ClightRectangularStore ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryArrayBackend GuardMemoryRegistryBackend GuardMemoryNamedRegistrySource
  GuardMemoryRaggedGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition compile_named_ragged_array_candidate base operations bound parameter live pool candidate :=
  compile_memory_registry_loop (named_array_descriptors base operations) [bound;parameter]
    (memory_ragged_positive_bounds base) live pool candidate.
Lemma memory_ragged_parameter_bounds base N M :
  0 < N <= rectangle_outer_limit base -> 0 < M <= rectangle_stride base ->
  MemoryNested.A.env_within (memory_ragged_positive_bounds base) [N;M].
Proof.
  intros NB MB [|[|index]] interval INDEX; cbn [memory_ragged_positive_bounds nth_error] in INDEX;
    try rewrite nth_error_nil in INDEX; try discriminate; inversion INDEX; subst interval;
    unfold MemoryNested.A.contains; cbn [MemoryNested.A.lower MemoryNested.A.upper nth]; lia.
Qed.
