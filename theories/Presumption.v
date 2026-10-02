From Stdlib Require Import ZArith Bool Lia.
Open Scope Z_scope.
Set Implicit Arguments.

(** A deliberately finite presumption language. Arithmetic is mathematical in
    its specification; synthesis must implement it using checked machine words.
    Pointer metadata here describes a toy block/offset model, not permission
    queries in CompCert. No arbitrary Prop, load, quantifier or call is encoded. *)
Inductive expression :=
| Literal (value : Z)
| Scalar (index : nat)
| Sum (left right : expression)
| Difference (left right : expression).

Record pointer := Pointer { block : nat; offset : Z }.
Record state := State {
  scalars : nat -> Z;
  pointers : nat -> pointer;
  extent : nat -> Z
}.

Fixpoint mathematical_value (s : state) (e : expression) : Z :=
  match e with
  | Literal z => z
  | Scalar i => scalars s i
  | Sum l r => mathematical_value s l + mathematical_value s r
  | Difference l r => mathematical_value s l - mathematical_value s r
  end.

Definition word_range (modulus z : Z) : bool :=
  (0 <=? z) && (z <? modulus).

Lemma word_range_spec : forall modulus z,
  word_range modulus z = true <-> 0 <= z < modulus.
Proof.
  intros. unfold word_range.
  rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.

Fixpoint mathematical_safe (modulus : Z) (s : state)
  (e : expression) : bool :=
  match e with
  | Literal z => word_range modulus z
  | Scalar i => word_range modulus (scalars s i)
  | Sum l r | Difference l r =>
      mathematical_safe modulus s l && mathematical_safe modulus s r &&
      word_range modulus (mathematical_value s e)
  end.

Definition bounds_meaning (s : state) (p : nat) (length : Z) : bool :=
  let address := pointers s p in
  (0 <=? offset address) && (0 <=? length) &&
  (offset address + length <=? extent s (block address)).

Definition disjoint_meaning (s : state) (p : nat) (left_length : Z)
  (q : nat) (right_length : Z) : bool :=
  let a := pointers s p in let b := pointers s q in
  (0 <=? left_length) && (0 <=? right_length) &&
  ((left_length =? 0) || (right_length =? 0) ||
   negb (Nat.eqb (block a) (block b)) ||
   (offset a + left_length <=? offset b) ||
   (offset b + right_length <=? offset a)).

Inductive atom :=
| LessEqual (left right : expression)
| Equal (left right : expression)
| NoOverflow (value : expression)
| InBounds (address : nat) (length : expression)
| Disjoint (left : nat) (left_length : expression)
           (right : nat) (right_length : expression).

Definition atom_meaning (modulus : Z) (s : state) (a : atom) : bool :=
  match a with
  | LessEqual l r => mathematical_value s l <=? mathematical_value s r
  | Equal l r => mathematical_value s l =? mathematical_value s r
  | NoOverflow e => mathematical_safe modulus s e
  | InBounds p length => bounds_meaning s p (mathematical_value s length)
  | Disjoint p l q r =>
      disjoint_meaning s p (mathematical_value s l) q (mathematical_value s r)
  end.

Inductive presumption :=
| Truth
| Falsity
| Atomic (a : atom)
| Both (left right : presumption)
| Either (left right : presumption)
| Negation (body : presumption).

Fixpoint meaning (modulus : Z) (s : state) (a : presumption) : bool :=
  match a with
  | Truth => true
  | Falsity => false
  | Atomic a => atom_meaning modulus s a
  | Both l r => meaning modulus s l && meaning modulus s r
  | Either l r => meaning modulus s l || meaning modulus s r
  | Negation p => negb (meaning modulus s p)
  end.

Definition holds (modulus : Z) (s : state) (a : presumption) : Prop :=
  meaning modulus s a = true.

(** Interval separation is distinct from access validity. Disjoint alone does
    not imply InBounds, allocation liveness, read/write permission or stability. *)
Lemma separated_intervals : forall s p l q r i,
  disjoint_meaning s p l q r = true ->
  block (pointers s p) = block (pointers s q) ->
  offset (pointers s p) <= i < offset (pointers s p) + l ->
  ~ (offset (pointers s q) <= i < offset (pointers s q) + r).
Proof.
  intros s p l q r i Hsep Hblock Hi Hj.
  unfold disjoint_meaning in Hsep.
  apply andb_true_iff in Hsep as [_ Hsep].
  repeat rewrite orb_true_iff in Hsep.
  destruct Hsep as [[[[Hl | Hr] | Hb] | Hab] | Hba].
  - apply Z.eqb_eq in Hl. lia.
  - apply Z.eqb_eq in Hr. lia.
  - apply negb_true_iff in Hb. apply Nat.eqb_neq in Hb. contradiction.
  - apply Z.leb_le in Hab. lia.
  - apply Z.leb_le in Hba. lia.
Qed.
