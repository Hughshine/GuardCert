From Stdlib Require Import ZArith Bool Lia.
From compcert.lib Require Import Integers Coqlib.
From Guard Require Import Presumption Synthesis.
Open Scope Z_scope.

(** A first connection to the pinned CompCert release: implement the checked
    unsigned addition contract using actual Int operations. This is a primitive
    semantics theorem, not yet a Clight/RTL condition-generation theorem. *)
Definition machine_checked_add (a b : Int.int) : Synthesis.arithmetic_result :=
  Synthesis.ArithmeticResult (Int.unsigned (Int.add a b))
    (negb (Int.ltu (Int.sub Int.mone b) a)).

Lemma threshold_is_exact : forall b,
  Int.unsigned (Int.sub Int.mone b) = Int.modulus - 1 - Int.unsigned b.
Proof.
  intro b. unfold Int.sub. rewrite Int.unsigned_mone.
  apply Int.unsigned_repr.
  pose proof (Int.unsigned_range b).
  unfold Int.max_unsigned. lia.
Qed.

Theorem machine_add_flag_correct : forall a b,
  negb (Int.ltu (Int.sub Int.mone b) a) =
  Presumption.word_range Int.modulus (Int.unsigned a + Int.unsigned b).
Proof.
  intros a b. unfold Int.ltu. rewrite threshold_is_exact.
  pose proof (Int.unsigned_range a). pose proof (Int.unsigned_range b).
  destruct (zlt (Int.modulus - 1 - Int.unsigned b) (Int.unsigned a)); simpl.
  - symmetry. apply not_true_iff_false. intro Hrange.
    apply Presumption.word_range_spec in Hrange. lia.
  - symmetry. apply Presumption.word_range_spec. lia.
Qed.

Theorem machine_checked_add_correct : forall a b,
  machine_checked_add a b =
  Synthesis.combine Int.modulus Z.add
    (Synthesis.checked_word Int.modulus (Int.unsigned a))
    (Synthesis.checked_word Int.modulus (Int.unsigned b)).
Proof.
  intros a b.
  assert (Ha : Presumption.word_range Int.modulus (Int.unsigned a) = true).
  { apply Presumption.word_range_spec. apply Int.unsigned_range. }
  assert (Hb : Presumption.word_range Int.modulus (Int.unsigned b) = true).
  { apply Presumption.word_range_spec. apply Int.unsigned_range. }
  assert (Hma : Int.unsigned a mod Int.modulus = Int.unsigned a).
  { apply Z.mod_small. apply Int.unsigned_range. }
  assert (Hmb : Int.unsigned b mod Int.modulus = Int.unsigned b).
  { apply Z.mod_small. apply Int.unsigned_range. }
  unfold machine_checked_add. rewrite machine_add_flag_correct.
  unfold Synthesis.combine, Synthesis.checked_word. simpl.
  rewrite Hma, Hmb, Ha, Hb. simpl.
  unfold Int.add. rewrite Int.unsigned_repr_eq. reflexivity.
Qed.

Example compcert_wrapping_input_sets_failure_flag :
  machine_checked_add Int.mone Int.one = Synthesis.ArithmeticResult 0 false.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions machine_add_flag_correct.
Print Assumptions machine_checked_add_correct.
