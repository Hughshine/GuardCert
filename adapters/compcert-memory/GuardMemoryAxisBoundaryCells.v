From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From polcert.lib Require Import Linalg.
From polcert.src Require Import PolyBase.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryMultiPointerCells
  GuardMemoryFiniteFootprint GuardMemoryFiniteAliasCondition GuardMemoryFootprintCapabilities GuardMemoryBufferOffsets
  GuardMemoryNaryAffineExpressions GuardMemoryBooleanRectangle GuardMemoryAffineAxisPairScan
  GuardMemoryAffineEndpointCells.
From GuardMemory Require Import GuardMemoryAxisBoundaryMath.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_affine_axis_boundary_pair_check locations counts first second first_term second_term :=
  forallb (fun mask => memory_boolean_rectangle_result (fun coordinates =>
    memory_cell_pair_address_check locations
      (point_cell first (memory_nary_index_value first_term (memory_axis_boundary_pick mask coordinates)))
      (point_cell second (memory_nary_index_value second_term (memory_axis_boundary_pick (map negb mask) coordinates))))
    counts []) (memory_axis_boundary_masks (length counts)).

Theorem memory_affine_axis_boundary_pair_from_full locations counts first second first_term second_term :
  Forall (fun count => 0 <= count) counts ->
  memory_affine_axis_pair_check locations counts first second first_term second_term = true ->
  memory_affine_axis_boundary_pair_check locations counts first second first_term second_term = true.
Proof.
  intros COUNTS CHECK; unfold memory_affine_axis_boundary_pair_check; apply forallb_forall; intros mask MEMBER.
  apply memory_axis_boundary_mask_member in MEMBER.
  rewrite memory_boolean_rectangle_member by exact COUNTS; intros coordinates RANGE; cbn.
  unfold memory_affine_axis_pair_check in CHECK; rewrite memory_boolean_rectangle_member in CHECK by exact COUNTS.
  specialize (CHECK (memory_axis_boundary_pick mask coordinates) (@memory_axis_boundary_pick_range coordinates counts mask RANGE MEMBER)); cbn in CHECK.
  rewrite memory_boolean_rectangle_member in CHECK by exact COUNTS.
  apply CHECK; apply memory_axis_boundary_pick_range; [exact RANGE|rewrite length_map; exact MEMBER].
Qed.

Theorem memory_affine_axis_boundary_pair_complete temps extent memory counts first second first_term second_term :
  first <> second -> fst first_term = fst second_term ->
  Forall (fun count => 0 <= count) counts ->
  (forall coordinates, Forall2 (fun index count => 0 <= index < count) coordinates counts ->
    memory_cell_capable (memory_multi_pointer_locations temps extent) memory
      (point_cell first (memory_nary_index_value first_term coordinates)) /\
    memory_cell_capable (memory_multi_pointer_locations temps extent) memory
      (point_cell second (memory_nary_index_value second_term coordinates))) ->
  memory_affine_axis_boundary_pair_check (memory_multi_pointer_locations temps extent)
    counts first second first_term second_term = true ->
  memory_affine_axis_pair_check (memory_multi_pointer_locations temps extent)
    counts first second first_term second_term = true.
Proof.
  intros DISTINCT COEFFICIENTS COUNTS CAPS CHECK.
  unfold memory_affine_axis_pair_check; rewrite memory_boolean_rectangle_member by exact COUNTS.
  intros i I; cbn; rewrite memory_boolean_rectangle_member by exact COUNTS; intros j J; cbn.
  destruct (proj1 (CAPS i I)) as [left [LEFT MORE]].
  destruct (proj2 (CAPS j J)) as [right [RIGHT REST]].
  destruct (@memory_multi_pointer_location_inverse temps extent _ left LEFT)
    as [fb [fp [fi [FB [FI [FR FL]]]]]].
  destruct (@memory_multi_pointer_location_inverse temps extent _ right RIGHT)
    as [sb [sp [sj [SB [SJ [SR SL]]]]]].
  cbn [arr_id arr_index point_cell] in FB,FI,SB,SJ.
  rewrite (@memory_pointer_pair_physical_check temps extent memory first second
    (memory_nary_index_value first_term i) (memory_nary_index_value second_term j) fb fp sb sp
    DISTINCT FB SB (proj1 (CAPS i I)) (proj2 (CAPS j J))).
  apply negb_true_iff; destruct (Pos.eqb fb sb) eqn:BLOCK; [|reflexivity].
  apply Pos.eqb_eq in BLOCK; subst sb; cbn [andb]; apply Z.eqb_neq; intro SAME.
  unfold memory_pointer_buffer_offset,memory_buffer_offset,memory_nary_index_value in SAME.
  rewrite COEFFICIENTS in SAME.
  change (memory_axis_boundary_offset Ptrofs.modulus (Ptrofs.unsigned fp) (fst second_term) (snd first_term) i =
    memory_axis_boundary_offset Ptrofs.modulus (Ptrofs.unsigned sp) (fst second_term) (snd second_term) j) in SAME.
  assert (LENGTH : length i = length j).
  { pose proof (Forall2_length I); pose proof (Forall2_length J); lia. }
  pose proof (@memory_axis_boundary_overlap Ptrofs.modulus (Ptrofs.unsigned fp) (Ptrofs.unsigned sp)
    (fst second_term) (snd first_term) (snd second_term) i j LENGTH SAME) as BOUNDARY.
  destruct (memory_axis_boundary_distance_range I J) as [DISTANCE MASK].
  set (mask := memory_axis_boundary_mask i j) in *.
  set (coordinates := memory_axis_boundary_distance i j) in *.
  assert (LEFT_RANGE : Forall2 (fun index count => 0 <= index < count)
    (memory_axis_boundary_pick mask coordinates) counts) by (apply memory_axis_boundary_pick_range; assumption).
  assert (RIGHT_RANGE : Forall2 (fun index count => 0 <= index < count)
    (memory_axis_boundary_pick (map negb mask) coordinates) counts).
  { apply memory_axis_boundary_pick_range; [exact DISTANCE|rewrite length_map; exact MASK]. }
  unfold memory_affine_axis_boundary_pair_check in CHECK.
  apply forallb_forall with (x := mask) in CHECK; [|apply memory_axis_boundary_mask_member; exact MASK].
  rewrite memory_boolean_rectangle_member in CHECK by exact COUNTS; specialize (CHECK coordinates DISTANCE); cbn in CHECK.
  rewrite (@memory_pointer_pair_physical_check temps extent memory first second
    (memory_nary_index_value first_term (memory_axis_boundary_pick mask coordinates))
    (memory_nary_index_value second_term (memory_axis_boundary_pick (map negb mask) coordinates)) fb fp fb sp
    DISTINCT FB SB (proj1 (CAPS _ LEFT_RANGE)) (proj2 (CAPS _ RIGHT_RANGE))) in CHECK.
  rewrite Pos.eqb_refl in CHECK; cbn [andb] in CHECK.
  unfold memory_pointer_buffer_offset,memory_buffer_offset,memory_nary_index_value in CHECK.
  rewrite COEFFICIENTS in CHECK.
  change (negb (Z.eqb
    (memory_axis_boundary_offset Ptrofs.modulus (Ptrofs.unsigned fp) (fst second_term) (snd first_term)
      (memory_axis_boundary_pick mask coordinates))
    (memory_axis_boundary_offset Ptrofs.modulus (Ptrofs.unsigned sp) (fst second_term) (snd second_term)
      (memory_axis_boundary_pick (map negb mask) coordinates))) = true) in CHECK.
  unfold memory_axis_boundary_left,memory_axis_boundary_right in BOUNDARY; fold mask coordinates in BOUNDARY.
  rewrite BOUNDARY,Z.eqb_refl in CHECK; discriminate.
Qed.

Theorem memory_affine_axis_boundary_pair_exact temps extent memory counts first second first_term second_term :
  first <> second -> fst first_term = fst second_term ->
  Forall (fun count => 0 <= count) counts ->
  (forall coordinates, Forall2 (fun index count => 0 <= index < count) coordinates counts ->
    memory_cell_capable (memory_multi_pointer_locations temps extent) memory
      (point_cell first (memory_nary_index_value first_term coordinates)) /\
    memory_cell_capable (memory_multi_pointer_locations temps extent) memory
      (point_cell second (memory_nary_index_value second_term coordinates))) ->
  memory_affine_axis_boundary_pair_check (memory_multi_pointer_locations temps extent)
    counts first second first_term second_term =
  memory_affine_axis_pair_check (memory_multi_pointer_locations temps extent)
    counts first second first_term second_term.
Proof.
  intros DISTINCT SAME COUNTS CAPS; apply Bool.eq_true_iff_eq; split.
  - apply memory_affine_axis_boundary_pair_complete with (memory := memory); assumption.
  - apply memory_affine_axis_boundary_pair_from_full; exact COUNTS.
Qed.
Print Assumptions memory_affine_axis_boundary_pair_from_full.
Print Assumptions memory_affine_axis_boundary_pair_complete.
Print Assumptions memory_affine_axis_boundary_pair_exact.
