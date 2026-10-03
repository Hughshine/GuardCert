From Stdlib Require Import List ZArith Lia Bool.
From polcert.lib Require Import Linalg.
From GuardMemory Require Import GuardMemoryNaryAffineExpressions GuardMemoryNaryRanges.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Bounds for a finite coordinate box permit signed coefficients. They do
    not assume that the original source expression has no intermediate wrap;
    its separate machine evaluation theorem interprets the final affine value. *)
Fixpoint memory_signed_dot_lower coefficients limits :=
  match coefficients,limits with
  | coefficient::rest,limit::tail =>
      Z.min 0 (coefficient*(limit-1))+memory_signed_dot_lower rest tail
  | _,_ => 0 end.
Fixpoint memory_signed_dot_upper coefficients limits :=
  match coefficients,limits with
  | coefficient::rest,limit::tail =>
      Z.max 0 (coefficient*(limit-1))+memory_signed_dot_upper rest tail
  | _,_ => 0 end.
Lemma memory_signed_product_box coefficient limit value :
  0 <= value < limit ->
  Z.min 0 (coefficient*(limit-1)) <= coefficient*value <=
    Z.max 0 (coefficient*(limit-1)).
Proof.
  intro RANGE; destruct (Z_le_dec 0 coefficient) as [POSITIVE|NEGATIVE].
  - rewrite Z.min_l,Z.max_r by nia; nia.
  - rewrite Z.min_r,Z.max_l by nia; nia.
Qed.
Theorem memory_signed_dot_box coefficients limits values :
  length coefficients = length limits -> memory_nary_ranges limits values ->
  memory_signed_dot_lower coefficients limits <= dot_product coefficients values <=
    memory_signed_dot_upper coefficients limits.
Proof.
  revert limits values; induction coefficients as [|coefficient rest IH];
    intros [|limit limits] values LENGTH RANGES; cbn in LENGTH; try discriminate.
  - inversion RANGES; subst; cbn; lia.
  - inversion RANGES; subst; cbn.
    pose proof (@memory_signed_product_box coefficient limit _ H1) as HEAD.
    specialize (IH limits _ ltac:(lia) H3); lia.
Qed.
Definition memory_signed_box_check limits extent term :=
  Nat.eqb (length (fst term)) (length limits) &&
  (0 <=? memory_signed_dot_lower (fst term) limits+snd term) &&
  (memory_signed_dot_upper (fst term) limits+snd term <? extent).
Theorem memory_signed_box_sound limits extent term values :
  memory_signed_box_check limits extent term = true ->
  memory_nary_ranges limits values ->
  0 <= memory_nary_index_value term values < extent.
Proof.
  unfold memory_signed_box_check; rewrite !andb_true_iff,Nat.eqb_eq,Z.leb_le,Z.ltb_lt.
  intros [[LENGTH LOWER] UPPER] RANGES.
  pose proof (@memory_signed_dot_box (fst term) limits values LENGTH RANGES).
  unfold memory_nary_index_value; lia.
Qed.
Lemma memory_positive_dot_bounds coefficients limits :
  Forall2 (fun coefficient limit => 0 <= coefficient /\ 0 < limit) coefficients limits ->
  memory_signed_dot_lower coefficients limits = 0 /\
  memory_signed_dot_upper coefficients limits = dot_product coefficients (map (fun limit => limit-1) limits).
Proof.
  intro RANGES; induction RANGES as [|coefficient limit coefficients limits [C L] RANGES [LOWER UPPER]]; cbn.
  - split; reflexivity.
  - rewrite Z.min_l,Z.max_r by nia; rewrite LOWER,UPPER; split; lia.
Qed.
Theorem memory_signed_box_accepts_nonnegative limits extent term :
  memory_nary_box_check limits extent term = true -> memory_signed_box_check limits extent term = true.
Proof.
  unfold memory_nary_box_check; rewrite !andb_true_iff.
  intros [[RANGES BIAS] END].
  pose proof (@memory_nary_range_check_sound (fst term) limits RANGES) as RELATED.
  destruct (@memory_positive_dot_bounds (fst term) limits RELATED) as [LOWER UPPER].
  unfold memory_nary_range_check in RANGES; rewrite andb_true_iff in RANGES.
  unfold memory_signed_box_check; rewrite LOWER,UPPER; cbn [Z.add].
  rewrite (proj1 RANGES),BIAS; cbn.
  unfold memory_nary_index_value in END; exact END.
Qed.
Example memory_signed_box_negative_coefficients :
  memory_signed_box_check [8;8] 256 ([-8;-1],63) = true.
Proof. reflexivity. Qed.
Print Assumptions memory_signed_box_sound.
Print Assumptions memory_signed_box_accepts_nonnegative.
