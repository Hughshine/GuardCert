From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From Guard Require Import ClightCountedLoop ClightRectangularGuard ClightNoWrap ClightCondition.
From GuardMemory Require Import GuardMemoryArrayBackend GuardMemoryPointerBackend GuardMemoryRecursiveSource
  GuardMemoryRecursiveDomain GuardMemoryScalarChecker GuardMemoryParametricSourceDomain.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_scalar_pointer_static_bounds dimensions cap scalars :=
  repeat (MemoryFramedNested.N.A.Interval 1 cap) dimensions++
  repeat (MemoryFramedNested.N.A.Interval Int.min_signed Int.max_signed) scalars.
Lemma memory_scalar_validator_signed_values values : Forall signed_range values ->
  MemoryNested.A.env_within (repeat (MemoryNested.A.Interval Int.min_signed Int.max_signed) (length values)) values.
Proof.
  intro RANGES; induction RANGES; cbn [length repeat].
  - intros index interval ABSENT; rewrite nth_error_nil in ABSENT; discriminate.
  - apply MemoryNested.A.env_within_cons; [exact H|exact IHRANGES].
Qed.
Lemma memory_scalar_validator_count_scalar_ranges cap bounds values ge locals temps memory :
  Forall (fun bound => register_range bound cap (Entry ge locals temps memory)) bounds -> Forall signed_range values ->
  MemoryNested.A.env_within (memory_scalar_static_bounds (length bounds) cap (length values)) (memory_recursive_parameters bounds temps++values).
Proof.
  intro RANGES; induction RANGES as [|bound bounds RANGE RANGES IH]; intro VALUES;
    cbn [length memory_recursive_parameters map memory_scalar_static_bounds repeat app].
  - apply memory_scalar_validator_signed_values; exact VALUES.
  - apply MemoryNested.A.env_within_cons.
    + unfold MemoryNested.A.contains; cbn; pose proof (proj2 RANGE); cbn [entry_temps] in H; lia.
    + apply IH; exact VALUES.
Qed.
Lemma memory_scalar_encoder_signed_values values : Forall signed_range values ->
  MemoryFramedNested.N.A.env_within (repeat (MemoryFramedNested.N.A.Interval Int.min_signed Int.max_signed) (length values)) values.
Proof.
  intro RANGES; induction RANGES; cbn [length repeat].
  - intros index interval ABSENT; rewrite nth_error_nil in ABSENT; discriminate.
  - apply MemoryFramedNested.N.A.env_within_cons; [exact H|exact IHRANGES].
Qed.
Lemma memory_scalar_encoder_count_scalar_ranges cap bounds values ge locals temps memory :
  Forall (fun bound => register_range bound cap (Entry ge locals temps memory)) bounds -> Forall signed_range values ->
  MemoryFramedNested.N.A.env_within (memory_scalar_pointer_static_bounds (length bounds) cap (length values)) (memory_recursive_parameters bounds temps++values).
Proof.
  intro RANGES; induction RANGES as [|bound bounds RANGE RANGES IH]; intro VALUES;
    cbn [length memory_recursive_parameters map memory_scalar_pointer_static_bounds repeat app].
  - apply memory_scalar_encoder_signed_values; exact VALUES.
  - apply MemoryFramedNested.N.A.env_within_cons.
    + unfold MemoryFramedNested.N.A.contains; cbn; pose proof (proj2 RANGE); cbn [entry_temps] in H; lia.
    + apply IH; exact VALUES.
Qed.
Lemma memory_recursive_scalar_values_range identifiers temps : Forall signed_range (memory_recursive_parameters identifiers temps).
Proof. apply Forall_map,Forall_forall; intros; apply Int.signed_range. Qed.
Lemma memory_scalar_bindings_typed identifiers values temps : memory_nest_bindings identifiers values temps ->
  forall identifier, In identifier identifiers -> exists word, temps ! identifier = Some (Vint word).
Proof.
  intro WORDS; induction WORDS; intros identifier MEMBER; [contradiction|].
  cbn in MEMBER; destruct MEMBER as [SAME|MEMBER]; [subst; eauto|eapply IHWORDS; exact MEMBER].
Qed.
Print Assumptions memory_scalar_validator_count_scalar_ranges.
Print Assumptions memory_scalar_encoder_count_scalar_ranges.
