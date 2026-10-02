From Stdlib Require Import ZArith Bool Lia.
From Guard Require Import Presumption GuardedRegion.
Open Scope Z_scope.
Set Implicit Arguments.

(** Checked primitives return both the wrapped value and an explicit validity
    flag. This specifies a primitive; a CompCert lowering proof remains needed.
    The flag is not an implicit CPU register or a global sticky source flag. *)
Record arithmetic_result := ArithmeticResult {
  word_value : Z;
  arithmetic_ok : bool
}.

Definition checked_word (modulus z : Z) : arithmetic_result :=
  ArithmeticResult (z mod modulus) (word_range modulus z).

Definition combine (modulus : Z) (operation : Z -> Z -> Z)
  (a b : arithmetic_result) : arithmetic_result :=
  let exact := operation (word_value a) (word_value b) in
  ArithmeticResult (exact mod modulus)
    (arithmetic_ok a && arithmetic_ok b && word_range modulus exact).

Fixpoint evaluate (modulus : Z) (s : state) (e : expression)
  : arithmetic_result :=
  match e with
  | Literal z => checked_word modulus z
  | Scalar i => checked_word modulus (scalars s i)
  | Sum l r => combine modulus Z.add (evaluate modulus s l) (evaluate modulus s r)
  | Difference l r =>
      combine modulus Z.sub (evaluate modulus s l) (evaluate modulus s r)
  end.

Lemma checked_word_exact : forall modulus z,
  arithmetic_ok (checked_word modulus z) = true ->
  word_value (checked_word modulus z) = z.
Proof.
  intros modulus z H. unfold checked_word in *. simpl in *.
  apply word_range_spec in H. apply Z.mod_small. exact H.
Qed.

Lemma evaluate_exact : forall e modulus s,
  arithmetic_ok (evaluate modulus s e) = true ->
  word_value (evaluate modulus s e) = mathematical_value s e.
Proof.
  induction e as [z | i | l IHl r IHr | l IHl r IHr];
    intros modulus s H; simpl in *.
  - apply checked_word_exact. exact H.
  - apply checked_word_exact. exact H.
  - unfold combine in H. simpl in H.
    apply andb_true_iff in H as [Hab Hrange].
    apply andb_true_iff in Hab as [Ha Hb].
    unfold combine. simpl.
    apply word_range_spec in Hrange.
    rewrite Z.mod_small by exact Hrange.
    rewrite (IHl _ _ Ha), (IHr _ _ Hb). reflexivity.
  - unfold combine in H. simpl in H.
    apply andb_true_iff in H as [Hab Hrange].
    apply andb_true_iff in Hab as [Ha Hb].
    unfold combine. simpl.
    apply word_range_spec in Hrange.
    rewrite Z.mod_small by exact Hrange.
    rewrite (IHl _ _ Ha), (IHr _ _ Hb). reflexivity.
Qed.

Theorem evaluate_flag_correct : forall e modulus s,
  arithmetic_ok (evaluate modulus s e) = mathematical_safe modulus s e.
Proof.
  induction e as [z | i | l IHl r IHr | l IHl r IHr];
    intros modulus s; simpl; try reflexivity;
    unfold combine; simpl;
    rewrite <- (IHl modulus s), <- (IHr modulus s);
    destruct (arithmetic_ok (evaluate modulus s l)) eqn:Hl;
    destruct (arithmetic_ok (evaluate modulus s r)) eqn:Hr;
    simpl; try reflexivity;
    rewrite (evaluate_exact l modulus s Hl), (evaluate_exact r modulus s Hr);
    reflexivity.
Qed.

(** A generated Boolean program has explicit short-circuit control flow.
    None means that a needed computation could not be safely checked.
    In particular it must not be converted to false beneath Negation. *)
Inductive condition :=
| Boolean (value : bool)
| CheckAtom (a : atom)
| IfCondition (test yes no : condition)
| NotCondition (body : condition).

Fixpoint synthesize (p : presumption) : condition :=
  match p with
  | Truth => Boolean true
  | Falsity => Boolean false
  | Atomic a => CheckAtom a
  | Both l r => IfCondition (synthesize l) (synthesize r) (Boolean false)
  | Either l r => IfCondition (synthesize l) (Boolean true) (synthesize r)
  | Negation p => NotCondition (synthesize p)
  end.

Definition checked_endpoint (modulus : Z) (s : state) (p : nat)
  (length : arithmetic_result) : arithmetic_result :=
  combine modulus Z.add (checked_word modulus (offset (pointers s p))) length.

Definition execute_atom (modulus : Z) (s : state) (a : atom) : option bool :=
  match a with
  | LessEqual l r =>
      let vl := evaluate modulus s l in let vr := evaluate modulus s r in
      if arithmetic_ok vl && arithmetic_ok vr
      then Some (word_value vl <=? word_value vr) else None
  | Equal l r =>
      let vl := evaluate modulus s l in let vr := evaluate modulus s r in
      if arithmetic_ok vl && arithmetic_ok vr
      then Some (word_value vl =? word_value vr) else None
  | NoOverflow e => Some (arithmetic_ok (evaluate modulus s e))
  | InBounds p length =>
      let v := evaluate modulus s length in
      if arithmetic_ok v && arithmetic_ok (checked_endpoint modulus s p v)
      then Some (bounds_meaning s p (word_value v)) else None
  | Disjoint p l q r =>
      let vl := evaluate modulus s l in let vr := evaluate modulus s r in
      if arithmetic_ok vl && arithmetic_ok vr &&
         arithmetic_ok (checked_endpoint modulus s p vl) &&
         arithmetic_ok (checked_endpoint modulus s q vr)
      then Some (disjoint_meaning s p (word_value vl) q (word_value vr)) else None
  end.

Lemma execute_atom_correct : forall a modulus s b,
  execute_atom modulus s a = Some b -> b = atom_meaning modulus s a.
Proof.
  intros a modulus s b H. destruct a; cbn [execute_atom atom_meaning] in H |- *.
  - destruct (arithmetic_ok (evaluate modulus s left) &&
              arithmetic_ok (evaluate modulus s right)) eqn:Hok; try discriminate.
    apply andb_true_iff in Hok as [Hl Hr]. inversion H; subst b.
    rewrite (evaluate_exact _ _ _ Hl), (evaluate_exact _ _ _ Hr). reflexivity.
  - destruct (arithmetic_ok (evaluate modulus s left) &&
              arithmetic_ok (evaluate modulus s right)) eqn:Hok; try discriminate.
    apply andb_true_iff in Hok as [Hl Hr]. inversion H; subst b.
    rewrite (evaluate_exact _ _ _ Hl), (evaluate_exact _ _ _ Hr). reflexivity.
  - inversion H; subst b. apply evaluate_flag_correct.
  - destruct (arithmetic_ok (evaluate modulus s length) &&
              arithmetic_ok (checked_endpoint modulus s address
                (evaluate modulus s length))) eqn:Hok; try discriminate.
    apply andb_true_iff in Hok as [Hl _]. inversion H; subst b.
    rewrite (evaluate_exact _ _ _ Hl). reflexivity.
  - destruct (arithmetic_ok (evaluate modulus s left_length) &&
              arithmetic_ok (evaluate modulus s right_length) &&
              arithmetic_ok (checked_endpoint modulus s left
                (evaluate modulus s left_length)) &&
              arithmetic_ok (checked_endpoint modulus s right
                (evaluate modulus s right_length))) eqn:Hok; try discriminate.
    apply andb_true_iff in Hok as [Hok _].
    apply andb_true_iff in Hok as [Hok _].
    apply andb_true_iff in Hok as [Hl Hr]. inversion H; subst b.
    rewrite (evaluate_exact _ _ _ Hl), (evaluate_exact _ _ _ Hr). reflexivity.
Qed.

Fixpoint execute (modulus : Z) (s : state) (c : condition) : option bool :=
  match c with
  | Boolean b => Some b
  | CheckAtom a => execute_atom modulus s a
  | IfCondition test yes no =>
      match execute modulus s test with
      | Some true => execute modulus s yes
      | Some false => execute modulus s no
      | None => None
      end
  | NotCondition p =>
      match execute modulus s p with Some b => Some (negb b) | None => None end
  end.

Theorem synthesis_correct : forall p modulus s b,
  execute modulus s (synthesize p) = Some b -> b = meaning modulus s p.
Proof.
  induction p as [| | a | l IHl r IHr | l IHl r IHr | p IH];
    intros modulus s b H; simpl in *.
  - inversion H. reflexivity.
  - inversion H. reflexivity.
  - eapply execute_atom_correct. exact H.
  - destruct (execute modulus s (synthesize l)) as [v |] eqn:Hl; try discriminate.
    rewrite <- (IHl _ _ _ Hl). destruct v; simpl.
    + apply IHr. exact H.
    + inversion H. reflexivity.
  - destruct (execute modulus s (synthesize l)) as [v |] eqn:Hl; try discriminate.
    rewrite <- (IHl _ _ _ Hl). destruct v; simpl.
    + inversion H. reflexivity.
    + apply IHr. exact H.
  - destruct (execute modulus s (synthesize p)) as [v |] eqn:Hp; try discriminate.
    inversion H; subst b. rewrite (IH _ _ _ Hp). reflexivity.
Qed.

Definition accepts (modulus : Z) (s : state) (c : condition) : bool :=
  match execute modulus s c with Some true => true | _ => false end.

Theorem synthesized_accepts_sound : forall p modulus s,
  accepts modulus s (synthesize p) = true -> holds modulus s p.
Proof.
  intros p modulus s H. unfold accepts in H.
  destruct (execute modulus s (synthesize p)) as [b |] eqn:Hexec; try discriminate.
  destruct b; try discriminate. unfold holds.
  symmetry. eapply synthesis_correct. exact Hexec.
Qed.

(** Encoding a semantic obligation is a separate proof from compiling syntax.
    Arbitrary predicates are not constructors of the DSL: an encoder must
    establish this correspondence for the particular obligation it supports.
    Conservative entrance inference can precede this exact encoding step. *)
Record presumption_encoding {S : Type} (modulus : Z) (view : S -> state)
  (obligation : S -> Prop) := Encoding {
  encoded_presumption : presumption;
  encoding_correct : forall s,
    holds modulus (view s) encoded_presumption <-> obligation s
}.

Theorem encoded_condition_correct : forall S modulus (view : S -> state)
  obligation (encoding : presumption_encoding modulus view obligation) s b,
  execute modulus (view s) (synthesize (encoded_presumption encoding)) = Some b ->
  (b = true <-> obligation s).
Proof.
  intros S modulus view obligation encoding s b H.
  rewrite (@synthesis_correct _ _ _ _ H).
  apply encoding_correct.
Qed.

(** Every plugin using this constructor obtains its guard from encoded syntax.
    The view and local correctness proof remain plugin-specific obligations. *)
Definition synthesized_rewrite {S E : Type} (modulus : Z)
  (view : S -> state) (p : presumption) (source candidate : @region S E)
  (Hlocal : forall s, holds modulus (view s) p -> candidate s = source s)
  : @guarded_rewrite S E.
Proof.
  refine {| original := source; optimized := candidate;
            assumption := fun s => holds modulus (view s) p;
            check := fun s => accepts modulus (view s) (synthesize p) |}.
  - intros. apply synthesized_accepts_sound. assumption.
  - exact Hlocal.
Defined.

Definition encoded_rewrite {S E : Type} (modulus : Z) (view : S -> state)
  (obligation : S -> Prop)
  (encoding : presumption_encoding modulus view obligation)
  (source candidate : @region S E)
  (Hlocal : forall s, obligation s -> candidate s = source s)
  : @guarded_rewrite S E.
Proof.
  refine (@synthesized_rewrite S E modulus view (encoded_presumption encoding)
    source candidate _).
  intros s H. apply Hlocal. apply (proj1 (encoding_correct encoding s)). exact H.
Defined.

Print Assumptions evaluate_flag_correct.
Print Assumptions synthesis_correct.
Print Assumptions synthesized_accepts_sound.
Print Assumptions encoded_condition_correct.
