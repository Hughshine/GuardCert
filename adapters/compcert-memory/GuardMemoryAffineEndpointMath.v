From Stdlib Require Import ZArith Lia Bool List.
From GuardMemory Require Import GuardMemoryBooleanScan.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_affine_endpoint_offset modulus base slope bias index :=
  (base+4*(slope*index+bias)) mod modulus.

Lemma memory_affine_endpoint_translation modulus first second slope first_bias second_bias i j shift :
  modulus <> 0 ->
  memory_affine_endpoint_offset modulus first slope first_bias i =
    memory_affine_endpoint_offset modulus second slope second_bias j ->
  memory_affine_endpoint_offset modulus first slope first_bias (i-shift) =
    memory_affine_endpoint_offset modulus second slope second_bias (j-shift).
Proof.
  intros MOD SAME; unfold memory_affine_endpoint_offset in *.
  replace (first+4*(slope*(i-shift)+first_bias)) with
    ((first+4*(slope*i+first_bias))-4*slope*shift) by ring.
  replace (second+4*(slope*(j-shift)+second_bias)) with
    ((second+4*(slope*j+second_bias))-4*slope*shift) by ring.
  rewrite (Zminus_mod (first+4*(slope*i+first_bias)) (4*slope*shift) modulus),
    (Zminus_mod (second+4*(slope*j+second_bias)) (4*slope*shift) modulus), SAME; reflexivity.
Qed.

Theorem memory_affine_endpoint_overlap modulus first second slope first_bias second_bias count i j :
  modulus <> 0 -> 0 <= i < count -> 0 <= j < count ->
  memory_affine_endpoint_offset modulus first slope first_bias i =
    memory_affine_endpoint_offset modulus second slope second_bias j ->
  exists index, 0 <= index < count /\
    (memory_affine_endpoint_offset modulus first slope first_bias 0 =
       memory_affine_endpoint_offset modulus second slope second_bias index \/
     memory_affine_endpoint_offset modulus first slope first_bias index =
       memory_affine_endpoint_offset modulus second slope second_bias 0).
Proof.
  intros MOD I J SAME; destruct (Z_le_dec i j) as [ORDER|ORDER].
  - exists (j-i); split; [lia|left].
    pose proof (@memory_affine_endpoint_translation modulus first second slope first_bias second_bias i j i MOD SAME) as SHIFT.
    rewrite Z.sub_diag in SHIFT; exact SHIFT.
  - exists (i-j); split; [lia|right].
    pose proof (@memory_affine_endpoint_translation modulus first second slope first_bias second_bias i j j MOD SAME) as SHIFT.
    rewrite Z.sub_diag in SHIFT; exact SHIFT.
Qed.

Definition memory_affine_endpoint_check modulus first second slope first_bias second_bias count :=
  memory_boolean_scan_result (fun index =>
    negb (Z.eqb (memory_affine_endpoint_offset modulus first slope first_bias 0)
      (memory_affine_endpoint_offset modulus second slope second_bias index)) &&
    negb (Z.eqb (memory_affine_endpoint_offset modulus first slope first_bias index)
      (memory_affine_endpoint_offset modulus second slope second_bias 0))) 0 (Z.to_nat count).

Theorem memory_affine_endpoint_check_complete modulus first second slope first_bias second_bias count :
  modulus <> 0 -> 0 <= count ->
  memory_affine_endpoint_check modulus first second slope first_bias second_bias count = true ->
  forall i j, 0 <= i < count -> 0 <= j < count ->
    memory_affine_endpoint_offset modulus first slope first_bias i <>
      memory_affine_endpoint_offset modulus second slope second_bias j.
Proof.
  intros MOD COUNT CHECK i j I J SAME.
  destruct (@memory_affine_endpoint_overlap modulus first second slope first_bias second_bias count i j MOD I J SAME)
    as [index [INDEX [SAME_FIRST|SAME_SECOND]]].
  all: unfold memory_affine_endpoint_check in CHECK; rewrite memory_boolean_scan_member in CHECK;
    specialize (CHECK index ltac:(rewrite Z2Nat.id by exact COUNT; lia));
    apply andb_true_iff in CHECK as [FIRST SECOND].
  - rewrite SAME_FIRST,Z.eqb_refl in FIRST; discriminate.
  - rewrite SAME_SECOND,Z.eqb_refl in SECOND; discriminate.
Qed.
Print Assumptions memory_affine_endpoint_check_complete.
