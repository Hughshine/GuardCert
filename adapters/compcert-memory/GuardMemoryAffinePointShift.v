From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Linalg.
From polcert.src Require Import PolyBase.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A point-coordinate translation changes domain bounds and affine biases
    with opposite signs. Parameter prefixes remain intact. This is mathematical
    representation reasoning; it does not justify machine arithmetic. *)
Fixpoint affine_point_shift position delta (coordinates : list Z) :=
  match position, coordinates with
  | _, [] => []
  | O, value::rest => (value+delta)::rest
  | S position, value::rest => value::affine_point_shift position delta rest
  end.

Lemma affine_point_shift_length position delta coordinates :
  length (affine_point_shift position delta coordinates) = length coordinates.
Proof.
  revert coordinates; induction position; intros [|value rest]; cbn; auto.
Qed.
Lemma affine_point_shift_inverse position delta coordinates :
  affine_point_shift position (-delta) (affine_point_shift position delta coordinates) = coordinates.
Proof.
  revert coordinates; induction position; intros [|value rest]; cbn; try reflexivity.
  - f_equal; lia.
  - rewrite IHposition; reflexivity.
Qed.
Lemma affine_point_shift_prefix count position delta coordinates :
  (count <= position)%nat ->
  firstn count (affine_point_shift position delta coordinates) = firstn count coordinates.
Proof.
  revert count coordinates; induction position; intros [|count] [|value rest] PREFIX;
    cbn; try reflexivity; try lia.
  f_equal; apply IHposition; lia.
Qed.
Lemma affine_point_shift_dot position delta coefficients coordinates :
  length coefficients = length coordinates ->
  dot_product coefficients (affine_point_shift position delta coordinates) =
  dot_product coefficients coordinates + delta * nth position coefficients 0.
Proof.
  revert coefficients coordinates.
  induction position; intros [|coefficient coefficients] [|value coordinates] WIDTH;
    cbn [affine_point_shift dot_product nth length] in *; try discriminate; try ring.
  rewrite IHposition by lia; ring.
Qed.

Definition affine_point_shift_row position delta (row : list Z * Z) :=
  (fst row, snd row - delta * nth position (fst row) 0).
Definition affine_point_shift_constraint position delta (row : list Z * Z) :=
  (fst row, snd row + delta * nth position (fst row) 0).

Lemma affine_point_shift_row_inverse position delta row :
  affine_point_shift_row position (-delta) (affine_point_shift_row position delta row) = row.
Proof. destruct row; unfold affine_point_shift_row; cbn; f_equal; ring. Qed.
Lemma affine_point_shift_constraint_inverse position delta row :
  affine_point_shift_constraint position (-delta) (affine_point_shift_constraint position delta row) = row.
Proof. destruct row; unfold affine_point_shift_constraint; cbn; f_equal; ring. Qed.

Theorem affine_point_shift_product position delta rows coordinates :
  Forall (fun row => length (fst row) = length coordinates) rows ->
  affine_product (map (affine_point_shift_row position delta) rows)
    (affine_point_shift position delta coordinates) = affine_product rows coordinates.
Proof.
  intro WIDTH; induction WIDTH as [|[coefficients bias] rows WIDTH REST IH]; [reflexivity|].
  change ((dot_product coefficients (affine_point_shift position delta coordinates) +
    (bias-delta*nth position coefficients 0)) ::
    affine_product (map (affine_point_shift_row position delta) rows)
      (affine_point_shift position delta coordinates) =
    (dot_product coefficients coordinates+bias)::affine_product rows coordinates).
  rewrite affine_point_shift_dot by exact WIDTH; rewrite IH; f_equal; ring.
Qed.
Theorem affine_point_shift_domain position delta rows coordinates :
  Forall (fun row => length (fst row) = length coordinates) rows ->
  in_poly (affine_point_shift position delta coordinates)
    (map (affine_point_shift_constraint position delta) rows) = in_poly coordinates rows.
Proof.
  intro WIDTH; induction WIDTH as [|[coefficients bias] rows WIDTH REST IH]; [reflexivity|].
  change (((dot_product (affine_point_shift position delta coordinates) coefficients <=?
      bias+delta*nth position coefficients 0) &&
    in_poly (affine_point_shift position delta coordinates)
      (map (affine_point_shift_constraint position delta) rows)) =
    ((dot_product coordinates coefficients <=? bias) && in_poly coordinates rows)).
  rewrite dot_product_commutative, affine_point_shift_dot by exact WIDTH.
  rewrite IH; rewrite (dot_product_commutative coordinates coefficients).
  f_equal; apply Bool.eq_true_iff_eq; rewrite !Z.leb_le; lia.
Qed.

Print Assumptions affine_point_shift_length.
Print Assumptions affine_point_shift_inverse.
Print Assumptions affine_point_shift_prefix.
Print Assumptions affine_point_shift_dot.
Print Assumptions affine_point_shift_row_inverse.
Print Assumptions affine_point_shift_constraint_inverse.
Print Assumptions affine_point_shift_product.
Print Assumptions affine_point_shift_domain.
