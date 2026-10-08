From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Linalg.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Positions enumerate an unsigned box. Each position denotes a coordinate
    difference and a canonical pair of points in the original source box.
    The zero bound stays empty; no negative machine loop bound is required. *)
Definition canonical_difference_bound count := Z.max 0 (2 * count - 1).
Definition canonical_difference_left count position := Z.max 0 (position - (count - 1)).
Definition canonical_difference_right count position := Z.max 0 ((count - 1) - position).
Definition canonical_difference_bounds counts := map canonical_difference_bound counts.

Fixpoint canonical_difference_positions counts first second : list Z :=
  match counts, first, second with
  | count::rest, a::xs, b::ys =>
      (a-b+(count-1)) :: canonical_difference_positions rest xs ys
  | _,_,_ => []
  end.
Fixpoint canonical_difference_first counts positions : list Z :=
  match counts, positions with
  | count::rest, position::tail =>
      canonical_difference_left count position :: canonical_difference_first rest tail
  | _,_ => []
  end.
Fixpoint canonical_difference_second counts positions : list Z :=
  match counts, positions with
  | count::rest, position::tail =>
      canonical_difference_right count position :: canonical_difference_second rest tail
  | _,_ => []
  end.
Fixpoint canonical_coordinate_difference first second : list Z :=
  match first,second with
  | a::xs,b::ys => (a-b)::canonical_coordinate_difference xs ys
  | _,_ => []
  end.

Lemma canonical_difference_bound_nonnegative count :
  0 <= canonical_difference_bound count.
Proof. apply Z.le_max_l. Qed.

Lemma canonical_difference_axis count position :
  0 <= count -> 0 <= position < canonical_difference_bound count ->
  0 <= canonical_difference_left count position < count /\
  0 <= canonical_difference_right count position < count /\
  canonical_difference_left count position - canonical_difference_right count position =
    position-(count-1).
Proof.
  intros COUNT POSITION; unfold canonical_difference_bound in POSITION.
  assert (POSITIVE : 0 < count).
  { destruct (Z_le_dec count 0); [rewrite Z.max_l in POSITION by lia; lia|lia]. }
  rewrite Z.max_r in POSITION by lia.
  unfold canonical_difference_left,canonical_difference_right.
  destruct (Z_le_dec 0 (position-(count-1))).
  - rewrite Z.max_r by lia; rewrite Z.max_l by lia; lia.
  - rewrite Z.max_l by lia; rewrite Z.max_r by lia; lia.
Qed.

Lemma canonical_difference_axis_position count first second :
  0 <= first < count -> 0 <= second < count ->
  0 <= first-second+(count-1) < canonical_difference_bound count.
Proof.
  intros FIRST SECOND; unfold canonical_difference_bound; rewrite Z.max_r by lia; lia.
Qed.

Theorem canonical_difference_points counts positions :
  Forall (fun count => 0 <= count) counts ->
  Forall2 (fun position bound => 0 <= position < bound)
    positions (canonical_difference_bounds counts) ->
  Forall2 (fun coordinate count => 0 <= coordinate < count)
    (canonical_difference_first counts positions) counts /\
  Forall2 (fun coordinate count => 0 <= coordinate < count)
    (canonical_difference_second counts positions) counts.
Proof.
  intro COUNTS; revert positions; induction COUNTS as [|count rest NONNEG COUNTS IH];
    intros positions RANGE; inversion RANGE as [|position bound tail bounds HEAD TAIL]; subst.
  - split; constructor.
  - destruct (canonical_difference_axis NONNEG HEAD) as [LEFT [RIGHT _]].
    destruct (IH _ TAIL) as [FIRST SECOND]; split; constructor; assumption.
Qed.

Theorem canonical_difference_coverage counts first second :
  Forall2 (fun coordinate count => 0 <= coordinate < count) first counts ->
  Forall2 (fun coordinate count => 0 <= coordinate < count) second counts ->
  let positions := canonical_difference_positions counts first second in
  Forall2 (fun position bound => 0 <= position < bound)
    positions (canonical_difference_bounds counts) /\
  canonical_coordinate_difference first second =
    canonical_coordinate_difference (canonical_difference_first counts positions)
      (canonical_difference_second counts positions).
Proof.
  intro FIRST; revert second; induction FIRST as [|a count xs rest A FIRST IH];
    intros second SECOND positions; inversion SECOND as [|b upper ys bounds B TAIL]; subst.
  - split; [constructor|reflexivity].
  - destruct (IH _ TAIL) as [POSITION DIFFERENCE].
    pose proof (canonical_difference_axis_position A B) as HEAD.
    destruct (@canonical_difference_axis count (a-b+(count-1)) ltac:(lia) HEAD) as [_ [_ EXACT]].
    split.
    + constructor; assumption.
    + unfold positions; cbn [canonical_coordinate_difference canonical_difference_first
        canonical_difference_second canonical_difference_positions].
      rewrite <- DIFFERENCE; f_equal; lia.
Qed.

Lemma canonical_coordinate_difference_same values :
  canonical_coordinate_difference values values = repeat 0 (length values).
Proof. induction values; cbn; [reflexivity|rewrite Z.sub_diag,IHvalues; reflexivity]. Qed.

Lemma canonical_coordinate_difference_app first second values :
  length first = length second ->
  canonical_coordinate_difference (first++values) (second++values) =
    canonical_coordinate_difference first second ++ repeat 0 (length values).
Proof.
  revert second; induction first; intros [|b ys] LENGTH; cbn in LENGTH; try discriminate.
  - apply canonical_coordinate_difference_same.
  - cbn; rewrite IHfirst by lia; reflexivity.
Qed.

Lemma canonical_dot_difference coefficients first second :
  length first = length second ->
  dot_product coefficients first - dot_product coefficients second =
    dot_product coefficients (canonical_coordinate_difference first second).
Proof.
  revert coefficients second; induction first; intros coefficients [|b ys] LENGTH;
    cbn in LENGTH; try discriminate; destruct coefficients; cbn; try ring.
  rewrite <- IHfirst by lia; ring.
Qed.

Lemma canonical_affine_difference terms first second other_first other_second :
  length first = length second -> length other_first = length other_second ->
  canonical_coordinate_difference first second =
    canonical_coordinate_difference other_first other_second ->
  canonical_coordinate_difference (affine_product terms first) (affine_product terms second) =
    canonical_coordinate_difference (affine_product terms other_first) (affine_product terms other_second).
Proof.
  intros LENGTH OTHER_LENGTH DIFFERENCE; induction terms as [|[coefficients constant] rest IH];
    cbn [affine_product map canonical_coordinate_difference fst snd]; [reflexivity|].
  f_equal; [|exact IH].
  replace (dot_product coefficients first + constant - (dot_product coefficients second + constant))
    with (dot_product coefficients first - dot_product coefficients second) by ring.
  replace (dot_product coefficients other_first + constant - (dot_product coefficients other_second + constant))
    with (dot_product coefficients other_first - dot_product coefficients other_second) by ring.
  rewrite !canonical_dot_difference by assumption; rewrite DIFFERENCE; reflexivity.
Qed.

Print Assumptions canonical_difference_bound_nonnegative.
Print Assumptions canonical_difference_axis.
Print Assumptions canonical_difference_axis_position.
Print Assumptions canonical_difference_points.
Print Assumptions canonical_difference_coverage.
Print Assumptions canonical_coordinate_difference_same.
Print Assumptions canonical_coordinate_difference_app.
Print Assumptions canonical_dot_difference.
Print Assumptions canonical_affine_difference.
