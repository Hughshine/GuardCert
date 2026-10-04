From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From Guard Require Import ClightCountedLoop ClightRectangularGuard ClightNoWrap ClightCondition.
From GuardMemory Require Import GuardMemoryArrayBackend GuardMemoryPointerBackend GuardMemoryRecursiveSource
  GuardMemoryRecursiveDomain GuardMemoryScalarPointerBounds GuardMemoryParametricSourceDomain.
From GuardMemory Require Import GuardMemoryVectorChecker.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_vector_pointer_static_bounds caps scalars :=
  map (fun cap => MemoryFramedNested.N.A.Interval 1 cap) caps ++
  repeat (MemoryFramedNested.N.A.Interval Int.min_signed Int.max_signed) scalars.
Lemma memory_vector_validator_count_scalar_ranges caps bounds values ge locals temps memory :
  Forall2 (fun cap bound => register_range bound cap (Entry ge locals temps memory)) caps bounds ->
  Forall signed_range values ->
  MemoryNested.A.env_within (memory_vector_static_bounds caps (length values))
    (memory_recursive_parameters bounds temps++values).
Proof.
  intro RANGES; induction RANGES as [|cap bound caps bounds RANGE RANGES IH]; intro VALUES;
    cbn [length memory_recursive_parameters map memory_vector_static_bounds repeat app].
  - apply memory_scalar_validator_signed_values; exact VALUES.
  - apply MemoryNested.A.env_within_cons.
    + unfold MemoryNested.A.contains; cbn; pose proof (proj2 RANGE); cbn [entry_temps] in H; lia.
    + apply IH; exact VALUES.
Qed.
Lemma memory_vector_encoder_count_scalar_ranges caps bounds values ge locals temps memory :
  Forall2 (fun cap bound => register_range bound cap (Entry ge locals temps memory)) caps bounds ->
  Forall signed_range values ->
  MemoryFramedNested.N.A.env_within (memory_vector_pointer_static_bounds caps (length values))
    (memory_recursive_parameters bounds temps++values).
Proof.
  intro RANGES; induction RANGES as [|cap bound caps bounds RANGE RANGES IH]; intro VALUES;
    cbn [length memory_recursive_parameters map memory_vector_pointer_static_bounds repeat app].
  - apply memory_scalar_encoder_signed_values; exact VALUES.
  - apply MemoryFramedNested.N.A.env_within_cons.
    + unfold MemoryFramedNested.N.A.contains; cbn; pose proof (proj2 RANGE); cbn [entry_temps] in H; lia.
    + apply IH; exact VALUES.
Qed.
Print Assumptions memory_vector_validator_count_scalar_ranges.
Print Assumptions memory_vector_encoder_count_scalar_ranges.
