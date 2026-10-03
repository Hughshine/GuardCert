From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Linalg.
From GuardMemory Require Import GuardMemoryBooleanRectangle.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint memory_axis_boundary_mask (first second : list Z) : list bool :=
  match first,second with
  | i::is,j::js => (j <=? i)::memory_axis_boundary_mask is js
  | _,_ => [] end.

Fixpoint memory_axis_boundary_distance (first second : list Z) : list Z :=
  match first,second with
  | i::is,j::js => Z.abs (i-j)::memory_axis_boundary_distance is js
  | _,_ => [] end.

Fixpoint memory_axis_boundary_pick (mask : list bool) (coordinates : list Z) : list Z :=
  match mask,coordinates with
  | side::rest,index::tail => (if side then index else 0)::memory_axis_boundary_pick rest tail
  | _,_ => [] end.

Definition memory_axis_boundary_left first second :=
  memory_axis_boundary_pick (memory_axis_boundary_mask first second)
    (memory_axis_boundary_distance first second).
Definition memory_axis_boundary_right first second :=
  memory_axis_boundary_pick (map negb (memory_axis_boundary_mask first second))
    (memory_axis_boundary_distance first second).

Lemma memory_axis_boundary_scalar i j :
  i-j = (if j <=? i then Z.abs(i-j) else 0) -
    (if negb (j <=? i) then Z.abs(i-j) else 0).
Proof.
  destruct (j <=? i) eqn:ORDER; cbn.
  - apply Z.leb_le in ORDER; rewrite Z.abs_eq by lia; lia.
  - apply Z.leb_gt in ORDER; rewrite Z.abs_neq by lia; lia.
Qed.

Lemma memory_axis_boundary_dot coefficients first second :
  length first = length second ->
  dot_product coefficients first - dot_product coefficients second =
    dot_product coefficients (memory_axis_boundary_left first second) -
    dot_product coefficients (memory_axis_boundary_right first second).
Proof.
  revert first second; induction coefficients as [|factor coefficients IH];
    intros [|i is] [|j js] LENGTH; cbn in LENGTH; try discriminate; cbn; try ring.
  unfold memory_axis_boundary_left,memory_axis_boundary_right; cbn.
  change (factor*i+dot_product coefficients is-(factor*j+dot_product coefficients js) =
    factor*(if j <=? i then Z.abs(i-j) else 0)+dot_product coefficients (memory_axis_boundary_left is js)-
    (factor*(if negb (j <=? i) then Z.abs(i-j) else 0)+dot_product coefficients (memory_axis_boundary_right is js))).
  pose proof (IH is js ltac:(lia)) as TAIL.
  pose proof (memory_axis_boundary_scalar i j) as HEAD; nia.
Qed.

Theorem memory_axis_boundary_distance_range counts first second :
  Forall2 (fun index count => 0 <= index < count) first counts ->
  Forall2 (fun index count => 0 <= index < count) second counts ->
  Forall2 (fun index count => 0 <= index < count)
    (memory_axis_boundary_distance first second) counts /\
  length (memory_axis_boundary_mask first second) = length counts.
Proof.
  intro FIRST; revert second; induction FIRST as [|i count is counts I FIRST IH]; intros second SECOND.
  - inversion SECOND; subst; cbn; split; constructor.
  - inversion SECOND as [|j count' js counts' J TAIL]; subst.
    destruct (IH js TAIL) as [DISTANCE LENGTH]; cbn; split; [constructor|lia].
    + destruct (Z_le_dec 0 (i-j)); [rewrite Z.abs_eq|rewrite Z.abs_neq]; lia.
    + exact DISTANCE.
Qed.

Definition memory_axis_boundary_offset modulus base coefficients bias coordinates :=
  (base+4*(dot_product coefficients coordinates+bias)) mod modulus.

Theorem memory_axis_boundary_overlap modulus first_base second_base coefficients first_bias second_bias first second :
  length first = length second ->
  memory_axis_boundary_offset modulus first_base coefficients first_bias first =
    memory_axis_boundary_offset modulus second_base coefficients second_bias second ->
  memory_axis_boundary_offset modulus first_base coefficients first_bias (memory_axis_boundary_left first second) =
    memory_axis_boundary_offset modulus second_base coefficients second_bias (memory_axis_boundary_right first second).
Proof.
  intros LENGTH SAME; unfold memory_axis_boundary_offset in *.
  pose proof (@memory_axis_boundary_dot coefficients first second LENGTH) as DOT.
  set (shift := 4*(dot_product coefficients first-dot_product coefficients (memory_axis_boundary_left first second))).
  replace (first_base+4*(dot_product coefficients (memory_axis_boundary_left first second)+first_bias))
    with ((first_base+4*(dot_product coefficients first+first_bias))-shift) by (unfold shift; ring).
  replace (second_base+4*(dot_product coefficients (memory_axis_boundary_right first second)+second_bias))
    with ((second_base+4*(dot_product coefficients second+second_bias))-shift) by (unfold shift; lia).
  rewrite (Zminus_mod _ shift modulus),(Zminus_mod _ shift modulus),SAME; reflexivity.
Qed.

Print Assumptions memory_axis_boundary_dot.
Print Assumptions memory_axis_boundary_distance_range.
Print Assumptions memory_axis_boundary_overlap.

Fixpoint memory_axis_boundary_masks dimensions : list (list bool) :=
  match dimensions with
  | O => [[]]
  | S rest => map (cons true) (memory_axis_boundary_masks rest) ++
      map (cons false) (memory_axis_boundary_masks rest) end.

Lemma memory_axis_boundary_mask_member dimensions mask :
  In mask (memory_axis_boundary_masks dimensions) <-> length mask = dimensions.
Proof.
  revert mask; induction dimensions as [|dimensions IH]; intros [|side rest]; cbn.
  - intuition.
  - split; [intros [BAD|[]]; discriminate|lia].
  - rewrite in_app_iff,!in_map_iff; split.
    + intros [[value [BAD _]]|[value [BAD _]]]; discriminate.
    + lia.
  - rewrite in_app_iff,!in_map_iff; split.
    + intros [[value [SAME MEMBER]]|[value [SAME MEMBER]]]; inversion SAME; subst;
        apply IH in MEMBER; lia.
    + intro LENGTH; destruct side; [left|right]; exists rest; split; try reflexivity; apply IH; lia.
Qed.

Lemma memory_axis_boundary_pick_range coordinates counts mask :
  Forall2 (fun index count => 0 <= index < count) coordinates counts ->
  length mask = length counts ->
  Forall2 (fun index count => 0 <= index < count) (memory_axis_boundary_pick mask coordinates) counts.
Proof.
  intro RANGE; revert mask; induction RANGE as [|index count coordinates counts INDEX RANGE IH];
    intros [|side mask] LENGTH; cbn in LENGTH; try discriminate; cbn; constructor.
  - destruct side; cbn; lia.
  - apply IH; lia.
Qed.

Definition memory_axis_boundary_check modulus first_base second_base coefficients first_bias second_bias counts :=
  forallb (fun mask => memory_boolean_rectangle_result (fun coordinates =>
    negb (Z.eqb
      (memory_axis_boundary_offset modulus first_base coefficients first_bias (memory_axis_boundary_pick mask coordinates))
      (memory_axis_boundary_offset modulus second_base coefficients second_bias (memory_axis_boundary_pick (map negb mask) coordinates))))
    counts []) (memory_axis_boundary_masks (length counts)).

Theorem memory_axis_boundary_check_complete modulus first_base second_base coefficients first_bias second_bias counts :
  Forall (fun count => 0 <= count) counts ->
  memory_axis_boundary_check modulus first_base second_base coefficients first_bias second_bias counts = true ->
  forall first second,
    Forall2 (fun index count => 0 <= index < count) first counts ->
    Forall2 (fun index count => 0 <= index < count) second counts ->
    memory_axis_boundary_offset modulus first_base coefficients first_bias first <>
      memory_axis_boundary_offset modulus second_base coefficients second_bias second.
Proof.
  intros COUNTS CHECK first second FIRST SECOND SAME.
  destruct (memory_axis_boundary_distance_range FIRST SECOND) as [DISTANCE MASK].
  assert (LENGTH : length first = length second).
  { apply Forall2_length in FIRST; apply Forall2_length in SECOND; lia. }
  pose proof (@memory_axis_boundary_overlap modulus first_base second_base coefficients first_bias second_bias
    first second LENGTH SAME) as BOUNDARY.
  unfold memory_axis_boundary_check in CHECK; apply forallb_forall with
    (x := memory_axis_boundary_mask first second) in CHECK;
    [|apply memory_axis_boundary_mask_member; exact MASK].
  rewrite memory_boolean_rectangle_member in CHECK by exact COUNTS.
  specialize (CHECK (memory_axis_boundary_distance first second) DISTANCE); cbn in CHECK.
  unfold memory_axis_boundary_left,memory_axis_boundary_right in BOUNDARY.
  rewrite BOUNDARY,Z.eqb_refl in CHECK; discriminate.
Qed.

Lemma memory_axis_boundary_masks_length dimensions :
  length (memory_axis_boundary_masks dimensions) = Nat.pow 2 dimensions.
Proof. induction dimensions; cbn; [reflexivity|rewrite length_app,!length_map,IHdimensions; lia]. Qed.

Print Assumptions memory_axis_boundary_check_complete.
Print Assumptions memory_axis_boundary_masks_length.
