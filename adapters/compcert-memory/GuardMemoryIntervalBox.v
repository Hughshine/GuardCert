From Stdlib Require Import List ZArith Lia Bool.
From polcert.lib Require Import Linalg.
From GuardMemory Require Import GuardMemoryNaryAffineExpressions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition interval_ranges (bounds : list (Z*Z)) (values : list Z) :=
  Forall2 (fun bound value => fst bound <= value < snd bound) bounds values.
Fixpoint interval_dot_lower coefficients bounds :=
  match coefficients,bounds with
  | coefficient::rest,(lower,upper)::tail =>
      Z.min (coefficient*lower) (coefficient*(upper-1))+interval_dot_lower rest tail
  | _,_ => 0 end.
Fixpoint interval_dot_upper coefficients bounds :=
  match coefficients,bounds with
  | coefficient::rest,(lower,upper)::tail =>
      Z.max (coefficient*lower) (coefficient*(upper-1))+interval_dot_upper rest tail
  | _,_ => 0 end.
Lemma interval_product_box coefficient lower upper value :
  lower <= value < upper ->
  Z.min (coefficient*lower) (coefficient*(upper-1)) <= coefficient*value <=
    Z.max (coefficient*lower) (coefficient*(upper-1)).
Proof.
  intro RANGE; destruct (Z_le_dec 0 coefficient) as [POSITIVE|NEGATIVE].
  - rewrite Z.min_l,Z.max_r by nia; nia.
  - rewrite Z.min_r,Z.max_l by nia; nia.
Qed.
Theorem interval_dot_box coefficients bounds values :
  length coefficients = length bounds -> interval_ranges bounds values ->
  interval_dot_lower coefficients bounds <= dot_product coefficients values <=
    interval_dot_upper coefficients bounds.
Proof.
  revert bounds values; induction coefficients as [|coefficient rest IH];
    intros [|[lower upper] bounds] values LENGTH RANGES; cbn in LENGTH; try discriminate.
  - inversion RANGES; subst; cbn; lia.
  - inversion RANGES; subst; cbn in *.
    pose proof (@interval_product_box coefficient lower upper _ H1) as HEAD.
    specialize (IH bounds _ ltac:(lia) H3); lia.
Qed.
Definition interval_box_check bounds extent term :=
  Nat.eqb (length (fst term)) (length bounds) &&
  (0 <=? interval_dot_lower (fst term) bounds+snd term) &&
  (interval_dot_upper (fst term) bounds+snd term <? extent).
Theorem interval_box_sound bounds extent term values :
  interval_box_check bounds extent term = true -> interval_ranges bounds values ->
  0 <= memory_nary_index_value term values < extent.
Proof.
  unfold interval_box_check; rewrite !andb_true_iff,Nat.eqb_eq,Z.leb_le,Z.ltb_lt.
  intros [[LENGTH LOWER] UPPER] RANGES.
  pose proof (@interval_dot_box (fst term) bounds values LENGTH RANGES).
  unfold memory_nary_index_value; lia.
Qed.
Example started_negative_offset : interval_box_check [(1,8)] 8 ([1],-1) = true.
Proof. reflexivity. Qed.
Example signed_parameter : interval_box_check [(0,4);(-3,4)] 32 ([4;1],3) = true.
Proof. reflexivity. Qed.
Print Assumptions interval_box_sound.

Fixpoint interval_lower_corner coefficients bounds :=
  match coefficients,bounds with
  | coefficient::rest,(lower,upper)::tail =>
      (if 0 <=? coefficient then lower else upper-1)::interval_lower_corner rest tail
  | _,_ => [] end.
Fixpoint interval_upper_corner coefficients bounds :=
  match coefficients,bounds with
  | coefficient::rest,(lower,upper)::tail =>
      (if 0 <=? coefficient then upper-1 else lower)::interval_upper_corner rest tail
  | _,_ => [] end.
Theorem interval_lower_corner_exact coefficients bounds :
  length coefficients = length bounds -> Forall (fun bound => fst bound < snd bound) bounds ->
  interval_ranges bounds (interval_lower_corner coefficients bounds) /\
  dot_product coefficients (interval_lower_corner coefficients bounds) = interval_dot_lower coefficients bounds.
Proof.
  revert bounds; induction coefficients as [|coefficient rest IH];
    intros [|[lower upper] bounds] LENGTH VALID; cbn in LENGTH; try discriminate.
  - split; [constructor|reflexivity].
  - inversion VALID; subst; cbn in *.
    destruct (IH bounds ltac:(lia) H2) as [RANGE EXACT].
    destruct (0 <=? coefficient) eqn:SIGN.
    + apply Z.leb_le in SIGN; rewrite Z.min_l by nia.
      split; [constructor; [cbn; lia|exact RANGE]|rewrite EXACT; reflexivity].
    + apply Z.leb_gt in SIGN; rewrite Z.min_r by nia.
      split; [constructor; [cbn; lia|exact RANGE]|rewrite EXACT; reflexivity].
Qed.
Theorem interval_upper_corner_exact coefficients bounds :
  length coefficients = length bounds -> Forall (fun bound => fst bound < snd bound) bounds ->
  interval_ranges bounds (interval_upper_corner coefficients bounds) /\
  dot_product coefficients (interval_upper_corner coefficients bounds) = interval_dot_upper coefficients bounds.
Proof.
  revert bounds; induction coefficients as [|coefficient rest IH];
    intros [|[lower upper] bounds] LENGTH VALID; cbn in LENGTH; try discriminate.
  - split; [constructor|reflexivity].
  - inversion VALID; subst; cbn in *.
    destruct (IH bounds ltac:(lia) H2) as [RANGE EXACT].
    destruct (0 <=? coefficient) eqn:SIGN.
    + apply Z.leb_le in SIGN; rewrite Z.max_r by nia.
      split; [constructor; [cbn; lia|exact RANGE]|rewrite EXACT; reflexivity].
    + apply Z.leb_gt in SIGN; rewrite Z.max_l by nia.
      split; [constructor; [cbn; lia|exact RANGE]|rewrite EXACT; reflexivity].
Qed.
Theorem interval_box_exact bounds extent term :
  length (fst term) = length bounds -> Forall (fun bound => fst bound < snd bound) bounds ->
  (interval_box_check bounds extent term = true <->
    forall values, interval_ranges bounds values -> 0 <= memory_nary_index_value term values < extent).
Proof.
  intros LENGTH VALID; split.
  - intros CHECK values RANGE; eapply interval_box_sound; eauto.
  - intro ALL.
    destruct (@interval_lower_corner_exact (fst term) bounds LENGTH VALID) as [LR LE].
    destruct (@interval_upper_corner_exact (fst term) bounds LENGTH VALID) as [UR UE].
    pose proof (ALL _ LR) as LOWER; pose proof (ALL _ UR) as UPPER.
    unfold memory_nary_index_value in LOWER,UPPER; rewrite LE in LOWER; rewrite UE in UPPER.
    unfold interval_box_check; rewrite !andb_true_iff,Nat.eqb_eq,Z.leb_le,Z.ltb_lt; tauto.
Qed.
Print Assumptions interval_box_exact.

Definition interval_window_box_check bounds lower upper term :=
  Nat.eqb (length (fst term)) (length bounds) &&
  (lower <=? interval_dot_lower (fst term) bounds+snd term) &&
  (interval_dot_upper (fst term) bounds+snd term <? upper).
Theorem interval_window_box_sound bounds lower upper term values :
  interval_window_box_check bounds lower upper term = true -> interval_ranges bounds values ->
  lower <= memory_nary_index_value term values < upper.
Proof.
  unfold interval_window_box_check; rewrite !andb_true_iff,Nat.eqb_eq,Z.leb_le,Z.ltb_lt.
  intros [[LENGTH LOWER] UPPER] RANGES.
  pose proof (@interval_dot_box (fst term) bounds values LENGTH RANGES).
  unfold memory_nary_index_value; lia.
Qed.
Theorem interval_window_box_exact bounds lower upper term :
  length (fst term) = length bounds -> Forall (fun bound => fst bound < snd bound) bounds ->
  (interval_window_box_check bounds lower upper term = true <->
    forall values, interval_ranges bounds values -> lower <= memory_nary_index_value term values < upper).
Proof.
  intros LENGTH VALID; split.
  - intros CHECK values RANGE; eapply interval_window_box_sound; eauto.
  - intro ALL.
    destruct (@interval_lower_corner_exact (fst term) bounds LENGTH VALID) as [LR LE].
    destruct (@interval_upper_corner_exact (fst term) bounds LENGTH VALID) as [UR UE].
    pose proof (ALL _ LR) as LOWER; pose proof (ALL _ UR) as UPPER.
    unfold memory_nary_index_value in LOWER,UPPER; rewrite LE in LOWER; rewrite UE in UPPER.
    unfold interval_window_box_check; rewrite !andb_true_iff,Nat.eqb_eq,Z.leb_le,Z.ltb_lt; tauto.
Qed.
Example negative_pointer_offsets : interval_window_box_check [(0,4)] (-4) 4 ([1],-1) = true.
Proof. reflexivity. Qed.
Print Assumptions interval_window_box_exact.
