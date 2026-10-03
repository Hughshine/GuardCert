From Stdlib Require Import List ZArith Lia Bool.
From polcert.lib Require Import Linalg.
From GuardMemory Require Import GuardMemoryNaryAffineExpressions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_nary_ranges limits values := Forall2 (fun limit value => 0 <= value < limit) limits values.
Lemma memory_nary_dot_box coefficients limits values :
  Forall2 (fun coefficient limit => 0 <= coefficient /\ 0 < limit) coefficients limits ->
  memory_nary_ranges limits values ->
  0 <= dot_product coefficients values <= dot_product coefficients (map (fun limit => limit-1) limits).
Proof.
  intro LIMITS; revert values; induction LIMITS as [|coefficient limit coefficients limits [C L] LIMITS IH];
    intros values RANGE; inversion RANGE; subst; cbn.
  - lia.
  - match goal with REST : Forall2 _ limits _ |- _ => specialize (IH _ REST) end; nia.
Qed.
Definition memory_nary_range_check coefficients limits :=
  Nat.eqb (length coefficients) (length limits) &&
  forallb (fun pair => (0 <=? fst pair) && (0 <? snd pair)) (combine coefficients limits).
Lemma memory_nary_range_check_sound coefficients limits :
  memory_nary_range_check coefficients limits = true ->
  Forall2 (fun coefficient limit => 0 <= coefficient /\ 0 < limit) coefficients limits.
Proof.
  unfold memory_nary_range_check; rewrite andb_true_iff,Nat.eqb_eq.
  intros [LENGTH VALID]; revert limits LENGTH VALID; induction coefficients as [|coefficient coefficients IH];
    intros [|limit limits] LENGTH VALID; cbn in LENGTH,VALID; try discriminate.
  - constructor.
  - rewrite !andb_true_iff,Z.leb_le,Z.ltb_lt in VALID; destruct VALID as [[C L] REST].
    constructor; [auto|apply IH; [lia|exact REST]].
Qed.
Definition memory_nary_box_check limits extent term :=
  memory_nary_range_check (fst term) limits && (0 <=? snd term) &&
    (memory_nary_index_value term (map (fun limit => limit-1) limits) <? extent).
Theorem memory_nary_box_sound limits extent term values :
  memory_nary_box_check limits extent term = true -> memory_nary_ranges limits values ->
  0 <= memory_nary_index_value term values < extent.
Proof.
  unfold memory_nary_box_check; rewrite !andb_true_iff,Z.leb_le,Z.ltb_lt.
  intros [[VALID BIAS] END] RANGE; apply memory_nary_range_check_sound in VALID.
  pose proof (memory_nary_dot_box VALID RANGE); unfold memory_nary_index_value in *; lia.
Qed.
Print Assumptions memory_nary_box_sound.
