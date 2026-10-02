From Stdlib Require Import Bool.
From Guard Require Import AbstractGuard.
Set Implicit Arguments.

(** A property dimension can expose propositions, not a built-in state model.
    Some false is a negative proof. A conservative refusal which does not prove
    the negation must return None. This distinction matters under Complement. *)
Fixpoint formula_property {S A} (property : A -> S -> Prop)
  (p : formula A) (s : S) : Prop :=
  match p with
  | Constant true => True
  | Constant false => False
  | Fact a => property a s
  | Conjunction l r => formula_property property l s /\ formula_property property r s
  | Disjunction l r => formula_property property l s \/ formula_property property r s
  | Complement q => ~ formula_property property q s
  end.

Definition decision_evidence (P : Prop) (b : bool) : Prop :=
  if b then P else ~ P.

Record property_dimension (S A : Type) (I : S -> Prop) := PropertyDimension {
  atom_property : A -> S -> Prop;
  decide_atom : A -> S -> option bool;
  decide_atom_correct : forall a s b, I s -> decide_atom a s = Some b ->
    decision_evidence (atom_property a s) b
}.
Arguments property_dimension S A I : clear implicits.

Theorem formula_property_decision : forall S A I
  (D : property_dimension S A I) p s b,
  I s -> formula_execute (decide_atom D) p s = Some b ->
  decision_evidence (formula_property (atom_property D) p s) b.
Proof.
  intros S A I D p; induction p; intros s b INV EX;
    cbn [formula_execute formula_property] in *.
  - destruct value; inversion EX; cbn [decision_evidence]; tauto.
  - eapply decide_atom_correct; eauto.
  - destruct (formula_execute (decide_atom D) p1 s) as [v|] eqn:LEFT;
      try discriminate.
    specialize (IHp1 s v INV LEFT). destruct v.
    + specialize (IHp2 s b INV EX).
      destruct b; cbn [decision_evidence] in *; tauto.
    + inversion EX; subst; cbn [decision_evidence] in *; tauto.
  - destruct (formula_execute (decide_atom D) p1 s) as [v|] eqn:LEFT;
      try discriminate.
    specialize (IHp1 s v INV LEFT). destruct v.
    + inversion EX; subst; cbn [decision_evidence] in *; tauto.
    + specialize (IHp2 s b INV EX).
      destruct b; cbn [decision_evidence] in *; tauto.
  - destruct (formula_execute (decide_atom D) p s) as [v|] eqn:BODY;
      try discriminate.
    specialize (IHp s v INV BODY). inversion EX; subst.
    destruct v; cbn [decision_evidence negb] in *; tauto.
Qed.

Theorem property_guard_refinement : forall S A I
  (L : language S) (D : property_dimension S A I)
  (primitives : check_primitives L I (decide_atom D)) p R source candidate,
  (forall o, R o o) ->
  conditional_refinement L I (formula_property (atom_property D) p)
    R source candidate ->
  forall s target, I s ->
  command_run L (compile_condition primitives p candidate source source) s target ->
  exists original, command_run L source s original /\ R target original.
Proof.
  intros S A I L D primitives p R source candidate REFL LOCAL s target INV RUN.
  apply (proj1 (@compile_condition_correct S A L I (decide_atom D) primitives p
    candidate source source s target INV)) in RUN.
  destruct (formula_execute (decide_atom D) p s) as [b|] eqn:EX;
    cbn [selected_command] in RUN.
  - destruct b.
    + apply LOCAL; auto.
      exact (@formula_property_decision S A I D p s true INV EX).
    + exists target; split; auto.
  - exists target; split; auto.
Qed.

(** Dimensions are combined without the kernel inspecting either property.
    They share only a language and a justified entry domain. *)
Definition combine_dimensions {S A B I}
  (D1 : property_dimension S A I) (D2 : property_dimension S B I)
  : property_dimension S (A + B) I.
Proof.
  refine {| atom_property := fun a =>
              match a with inl x => atom_property D1 x | inr x => atom_property D2 x end;
            decide_atom := fun a =>
              match a with inl x => decide_atom D1 x | inr x => decide_atom D2 x end |}.
  intros [a|b] s v INV EX; cbn in *; eapply decide_atom_correct; eauto.
Defined.

Definition combine_primitives {S A B} {L : language S} {I}
  {E1 : A -> S -> option bool} {E2 : B -> S -> option bool}
  (P1 : check_primitives L I E1) (P2 : check_primitives L I E2)
  : check_primitives L I
      (fun a => match a with inl x => E1 x | inr x => E2 x end).
Proof.
  refine {| validity_test := fun a =>
              match a with inl x => validity_test P1 x | inr x => validity_test P2 x end;
            value_test := fun a =>
              match a with inl x => value_test P1 x | inr x => value_test P2 x end |}.
  - intros [a|b] s v INV; cbn; eapply validity_test_correct; eauto.
  - intros [a|b] s v w INV EX; cbn in *; eapply value_test_correct; eauto.
Defined.

(** Adapts a certified one-sided acceptance test. Refusal carries no negative
    evidence, and consequently becomes None rather than Some false. *)
Definition positive_dimension {S A I}
  (property : A -> S -> Prop) (accept : A -> S -> bool)
  (SOUND : forall a s, I s -> accept a s = true -> property a s)
  : property_dimension S A I.
Proof.
  refine {| atom_property := property;
            decide_atom := fun a s => if accept a s then Some true else None |}.
  intros a s b INV EX. destruct (accept a s) eqn:ACCEPT; try discriminate.
  inversion EX; subst; cbn [decision_evidence]; eapply SOUND; eauto.
Defined.

Print Assumptions formula_property_decision.
Print Assumptions property_guard_refinement.
Print Assumptions combine_dimensions.
Print Assumptions positive_dimension.

Theorem property_guard_preservation : forall S A I
  (L : language S) (D : property_dimension S A I)
  (primitives : check_primitives L I (decide_atom D)) p R source candidate,
  (forall o, R o o) ->
  conditional_preservation L I (formula_property (atom_property D) p)
    R source candidate ->
  forall s original, I s -> command_run L source s original ->
  exists target,
    command_run L (compile_condition primitives p candidate source source) s target /\
    R original target.
Proof.
  intros S A I L D primitives p R source candidate REFL LOCAL s original INV RUN.
  destruct (formula_execute (decide_atom D) p s) as [b|] eqn:EX.
  - destruct b.
    + destruct (LOCAL s original INV
        (@formula_property_decision S A I D p s true INV EX) RUN)
        as [target [CAND REL]].
      exists target; split; auto.
      apply (proj2 (@compile_condition_correct S A L I (decide_atom D) primitives p
        candidate source source s target INV)). rewrite EX; exact CAND.
    + exists original; split; auto.
      apply (proj2 (@compile_condition_correct S A L I (decide_atom D) primitives p
        candidate source source s original INV)). rewrite EX; exact RUN.
  - exists original; split; auto.
    apply (proj2 (@compile_condition_correct S A L I (decide_atom D) primitives p
      candidate source source s original INV)). rewrite EX; exact RUN.
Qed.

Print Assumptions property_guard_preservation.
