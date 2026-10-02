From Stdlib Require Import ZArith Bool Lia.
Open Scope Z_scope.
Set Implicit Arguments.

(** A concrete arithmetic guard specification for unsigned 8-bit words.
    Addition returns a wrapped word only after the operands pass a safe
    threshold test. No unchecked addition is used to decide overflow.
    This is an executable model, not a proof of CompCert code generation. *)
Definition word_range (z : Z) : bool := (0 <=? z) && (z <? 256).

Lemma word_range_spec : forall z,
  word_range z = true <-> 0 <= z < 256.
Proof.
  intro z. unfold word_range.
  rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.

Definition checked_add (a b : Z) : option Z :=
  if word_range a && word_range b && (a <=? 255 - b)
  then Some ((a + b) mod 256) else None.

Lemma checked_add_sound : forall a b z,
  checked_add a b = Some z -> z = a + b /\ 0 <= z < 256.
Proof.
  intros a b z H. unfold checked_add in H.
  destruct (word_range a && word_range b && (a <=? 255 - b))
    eqn:Hsafe; try discriminate.
  inversion H; subst z; clear H.
  apply andb_true_iff in Hsafe as [Hab Hsum].
  apply andb_true_iff in Hab as [Ha Hb].
  apply word_range_spec in Ha. apply word_range_spec in Hb.
  apply Z.leb_le in Hsum.
  assert (Hrange : 0 <= a + b < 256) by lia.
  rewrite Z.mod_small by exact Hrange. auto.
Qed.

Lemma checked_add_threshold_safe : forall a b,
  word_range a = true -> word_range b = true -> 0 <= 255 - b < 256.
Proof.
  intros a b Ha Hb. apply word_range_spec in Hb. lia.
Qed.

Inductive aexpr :=
| Constant (value : Z)
| Input (index : nat)
| Add (left right : aexpr).

Fixpoint mathematical_eval (env : nat -> Z) (e : aexpr) : Z :=
  match e with
  | Constant z => z
  | Input i => env i
  | Add l r => mathematical_eval env l + mathematical_eval env r
  end.

Fixpoint checked_eval (env : nat -> Z) (e : aexpr) : option Z :=
  match e with
  | Constant z => if word_range z then Some z else None
  | Input i => if word_range (env i) then Some (env i) else None
  | Add l r =>
      match checked_eval env l, checked_eval env r with
      | Some a, Some b => checked_add a b
      | _, _ => None
      end
  end.

Lemma checked_eval_sound : forall e env z,
  checked_eval env e = Some z -> z = mathematical_eval env e.
Proof.
  induction e as [c | i | l IHl r IHr]; intros env z H; simpl in *.
  - destruct (word_range c); inversion H; reflexivity.
  - destruct (word_range (env i)); inversion H; reflexivity.
  - destruct (checked_eval env l) as [a |] eqn:Hl; try discriminate.
    destruct (checked_eval env r) as [b |] eqn:Hr; try discriminate.
    apply checked_add_sound in H as [H _].
    rewrite H, (IHl _ _ Hl), (IHr _ _ Hr). reflexivity.
Qed.

Inductive predicate :=
| LessEqual (left right : aexpr)
| Conjunction (left right : predicate).

Fixpoint mathematical_test (env : nat -> Z) (b : predicate) : bool :=
  match b with
  | LessEqual l r => mathematical_eval env l <=? mathematical_eval env r
  | Conjunction l r => mathematical_test env l && mathematical_test env r
  end.

Fixpoint checked_test (env : nat -> Z) (b : predicate) : option bool :=
  match b with
  | LessEqual l r =>
      match checked_eval env l, checked_eval env r with
      | Some a, Some b => Some (a <=? b)
      | _, _ => None
      end
  | Conjunction l r =>
      match checked_test env l with
      | Some true => checked_test env r
      | Some false => Some false
      | None => None
      end
  end.

Lemma checked_test_sound : forall b env answer,
  checked_test env b = Some answer ->
  answer = mathematical_test env b.
Proof.
  induction b as [l r | l IHl r IHr]; intros env answer H; simpl in *.
  - destruct (checked_eval env l) as [a |] eqn:Hl; try discriminate.
    destruct (checked_eval env r) as [b |] eqn:Hr; try discriminate.
    inversion H; subst answer.
    rewrite (checked_eval_sound _ _ Hl), (checked_eval_sound _ _ Hr).
    reflexivity.
  - destruct (checked_test env l) as [v |] eqn:Hl; try discriminate.
    destruct v.
    + rewrite <- (IHl _ _ Hl). simpl. apply IHr. exact H.
    + inversion H; subst answer. rewrite <- (IHl _ _ Hl). reflexivity.
Qed.

Definition accepts (env : nat -> Z) (b : predicate) : bool :=
  match checked_test env b with Some true => true | _ => false end.

Theorem accepts_sound : forall env b,
  accepts env b = true -> mathematical_test env b = true.
Proof.
  intros env b H. unfold accepts in H.
  destruct (checked_test env b) as [v |] eqn:Htest; try discriminate.
  destruct v; try discriminate.
  symmetry. eapply checked_test_sound. exact Htest.
Qed.

Example addition_at_word_limit_rejects : checked_add 255 1 = None.
Proof. reflexivity. Qed.

Example addition_below_word_limit_accepts : checked_add 254 1 = Some 255.
Proof. reflexivity. Qed.
