From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Linalg.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Pure integer-affine services for variable-depth piece witnesses. These
    functions construct constraints; they do not establish machine safety. *)
Definition piece_map_width width (mapping : list (list Z*Z)) :=
  forallb (fun row => Nat.eqb (length (fst row)) width) mapping.
Lemma piece_map_width_sound width mapping :
  piece_map_width width mapping=true -> exact_listzzs_cols width mapping.
Proof.
  unfold piece_map_width,exact_listzzs_cols; intros WIDTH coefficients bias row MEMBER ROW.
  apply forallb_forall with (x:=row) in WIDTH; [|exact MEMBER].
  subst row; cbn in WIDTH; apply Nat.eqb_eq; exact WIDTH.
Qed.

Definition piece_compose_row row mapping := hd ([],0) (matrix_product [row] mapping).
Lemma piece_compose_row_correct row mapping index width :
  exact_listzzs_cols width mapping ->
  dot_product (fst (piece_compose_row row mapping)) index + snd (piece_compose_row row mapping) =
  dot_product (fst row) (affine_product mapping index) + snd row.
Proof.
  intro WIDTH; pose proof (@matrix_product_assoc [row] mapping index width WIDTH) as COMPOSE.
  unfold piece_compose_row; destruct (matrix_product [row] mapping) as [|head rest];
    cbn in COMPOSE; [discriminate|].
  cbn; now injection COMPOSE.
Qed.

Definition piece_pullback_row mapping row :=
  let composed := piece_compose_row (fst row,0) mapping in
  (fst composed,snd row-snd composed).
Lemma piece_pullback_row_correct mapping row index width :
  exact_listzzs_cols width mapping ->
  satisfies_constraint index (piece_pullback_row mapping row) =
  satisfies_constraint (affine_product mapping index) row.
Proof.
  intro WIDTH; destruct row as [coefficients bound].
  pose proof (@piece_compose_row_correct (coefficients,0) mapping index width WIDTH) as VALUE.
  unfold piece_pullback_row,satisfies_constraint; cbn [fst snd] in *.
  rewrite (dot_product_commutative index (fst (piece_compose_row (coefficients,0) mapping))).
  rewrite (dot_product_commutative (affine_product mapping index) coefficients).
  apply eq_true_iff_eq; split; intro TEST; apply Z.leb_le in TEST; apply Z.leb_le; lia.
Qed.
Definition piece_pullback_poly mapping domain := map (piece_pullback_row mapping) domain.
Theorem piece_pullback_poly_correct mapping domain index width :
  exact_listzzs_cols width mapping ->
  in_poly index (piece_pullback_poly mapping domain)=in_poly (affine_product mapping index) domain.
Proof.
  intro WIDTH; induction domain as [|row rest IH]; [reflexivity|].
  change (satisfies_constraint index (piece_pullback_row mapping row) &&
    in_poly index (piece_pullback_poly mapping rest) =
    satisfies_constraint (affine_product mapping index) row &&
    in_poly (affine_product mapping index) rest).
  rewrite (@piece_pullback_row_correct mapping row index width WIDTH),IH; reflexivity.
Qed.

Definition piece_equal_row first second :=
  (add_vector (fst first) (mult_vector (-1) (fst second)),snd second-snd first).
Lemma piece_equal_row_correct first second index :
  satisfies_constraint index (piece_equal_row first second)=true <->
  dot_product (fst first) index+snd first <= dot_product (fst second) index+snd second.
Proof.
  unfold piece_equal_row,satisfies_constraint; cbn.
  rewrite add_vector_dot_product_distr_right,dot_product_mult_right.
  rewrite (dot_product_commutative index (fst first)),(dot_product_commutative index (fst second)).
  rewrite Z.leb_le; lia.
Qed.
Fixpoint piece_equal_maps first second := match first,second with
  | [],[]=>[]
  | x::xs,y::ys=>piece_equal_row x y::piece_equal_row y x::piece_equal_maps xs ys
  | _,_=>[([], -1)] end.
Theorem piece_equal_maps_correct first second index :
  in_poly index (piece_equal_maps first second)=true <->
  affine_product first index=affine_product second index.
Proof.
  revert second; induction first as [|x xs IH]; intros [|y ys]; cbn [piece_equal_maps].
  - split; reflexivity.
  - unfold in_poly,satisfies_constraint; cbn; rewrite dot_product_nil_right; cbn; split; discriminate.
  - unfold in_poly,satisfies_constraint; cbn; rewrite dot_product_nil_right; cbn; split; discriminate.
  - change (satisfies_constraint index (piece_equal_row x y) &&
      (satisfies_constraint index (piece_equal_row y x) &&
        in_poly index (piece_equal_maps xs ys))=true <->
      (dot_product (fst x) index+snd x)::affine_product xs index =
      (dot_product (fst y) index+snd y)::affine_product ys index).
    rewrite !andb_true_iff,!piece_equal_row_correct,IH; split.
    + intros [XY [YX TAIL]]; f_equal; [lia|exact TAIL].
    + intro EQUAL; injection EQUAL as HEAD TAIL; repeat split; [lia|lia|exact TAIL].
Qed.

Print Assumptions piece_map_width_sound.
Print Assumptions piece_compose_row_correct.
Print Assumptions piece_pullback_poly_correct.
Print Assumptions piece_equal_maps_correct.
