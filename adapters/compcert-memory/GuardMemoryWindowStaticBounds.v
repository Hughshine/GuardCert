From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From Guard Require Import ClightCountedLoop ClightRectangularGuard ClightNoWrap ClightCondition.
From GuardMemory Require Import GuardMemoryArrayBackend GuardMemoryPointerBackend GuardMemoryRecursiveSource
  GuardMemoryRecursiveDomain GuardMemoryScalarPointerBounds GuardMemoryParametricSourceDomain
  GuardMemoryVectorChecker GuardMemoryNaryRanges.
From GuardMemory Require Import GuardMemoryIntervalBox.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition window_static_base_bounds caps parameter_bounds scalars :=
  map (fun cap => MemoryNested.A.Interval 1 cap) caps ++
  map (fun bound => MemoryNested.A.Interval (fst bound) (snd bound-1)) parameter_bounds ++
  repeat (MemoryNested.A.Interval Int.min_signed Int.max_signed) scalars.
Definition window_pointer_static_base_bounds caps parameter_bounds scalars :=
  map (fun cap => MemoryFramedNested.N.A.Interval 1 cap) caps ++
  map (fun bound => MemoryFramedNested.N.A.Interval (fst bound) (snd bound-1)) parameter_bounds ++
  repeat (MemoryFramedNested.N.A.Interval Int.min_signed Int.max_signed) scalars.
Lemma window_validator_parameter_scalar_ranges parameter_bounds parameters values :
  interval_ranges parameter_bounds parameters -> Forall signed_range values ->
  MemoryNested.A.env_within
    (map (fun bound => MemoryNested.A.Interval (fst bound) (snd bound-1)) parameter_bounds ++
      repeat (MemoryNested.A.Interval Int.min_signed Int.max_signed) (length values)) (parameters++values).
Proof.
  intro RANGES; induction RANGES; intro VALUES; cbn [map app].
  - apply memory_scalar_validator_signed_values; exact VALUES.
  - apply MemoryNested.A.env_within_cons.
    + unfold MemoryNested.A.contains; cbn; lia.
    + apply IHRANGES; exact VALUES.
Qed.
Lemma window_encoder_parameter_scalar_ranges parameter_bounds parameters values :
  interval_ranges parameter_bounds parameters -> Forall signed_range values ->
  MemoryFramedNested.N.A.env_within
    (map (fun bound => MemoryFramedNested.N.A.Interval (fst bound) (snd bound-1)) parameter_bounds ++
      repeat (MemoryFramedNested.N.A.Interval Int.min_signed Int.max_signed) (length values)) (parameters++values).
Proof.
  intro RANGES; induction RANGES; intro VALUES; cbn [map app].
  - apply memory_scalar_encoder_signed_values; exact VALUES.
  - apply MemoryFramedNested.N.A.env_within_cons.
    + unfold MemoryFramedNested.N.A.contains; cbn; lia.
    + apply IHRANGES; exact VALUES.
Qed.
Lemma window_validator_count_parameter_scalar_ranges caps bounds parameter_bounds parameters values ge locals temps memory :
  Forall2 (fun cap bound => register_range bound cap (Entry ge locals temps memory)) caps bounds ->
  interval_ranges parameter_bounds parameters -> Forall signed_range values ->
  MemoryNested.A.env_within (window_static_base_bounds caps parameter_bounds (length values))
    (memory_recursive_parameters bounds temps++parameters++values).
Proof.
  intro RANGES; induction RANGES as [|cap bound caps bounds RANGE RANGES IH]; intros PARAMETERS VALUES;
    cbn [length memory_recursive_parameters map window_static_base_bounds repeat app].
  - apply window_validator_parameter_scalar_ranges; assumption.
  - apply MemoryNested.A.env_within_cons.
    + unfold MemoryNested.A.contains; cbn; pose proof (proj2 RANGE); cbn [entry_temps] in H; lia.
    + apply IH; assumption.
Qed.
Lemma window_encoder_count_parameter_scalar_ranges caps bounds parameter_bounds parameters values ge locals temps memory :
  Forall2 (fun cap bound => register_range bound cap (Entry ge locals temps memory)) caps bounds ->
  interval_ranges parameter_bounds parameters -> Forall signed_range values ->
  MemoryFramedNested.N.A.env_within (window_pointer_static_base_bounds caps parameter_bounds (length values))
    (memory_recursive_parameters bounds temps++parameters++values).
Proof.
  intro RANGES; induction RANGES as [|cap bound caps bounds RANGE RANGES IH]; intros PARAMETERS VALUES;
    cbn [length memory_recursive_parameters map window_pointer_static_base_bounds repeat app].
  - apply window_encoder_parameter_scalar_ranges; assumption.
  - apply MemoryFramedNested.N.A.env_within_cons.
    + unfold MemoryFramedNested.N.A.contains; cbn; pose proof (proj2 RANGE); cbn [entry_temps] in H; lia.
    + apply IH; assumption.
Qed.

Print Assumptions window_validator_count_parameter_scalar_ranges.
Print Assumptions window_encoder_count_parameter_scalar_ranges.
