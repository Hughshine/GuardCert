From Stdlib Require Import Bool.
From Guard Require Import AbstractGuard SemanticFacts.
Set Implicit Arguments.

Definition smart_and {A} (p q : formula A) : formula A :=
  match p, q with
  | Constant true, _ => q
  | Constant false, _ => Constant false
  | _, Constant true => p
  | _, Constant false => Constant false
  | _, _ => Conjunction p q
  end.
Definition smart_or {A} (p q : formula A) : formula A :=
  match p, q with
  | Constant true, _ => Constant true
  | Constant false, _ => q
  | _, Constant true => Constant true
  | _, Constant false => p
  | _, _ => Disjunction p q
  end.
Definition smart_not {A} (p : formula A) : formula A :=
  match p with Constant b => Constant (negb b) | _ => Complement p end.

(** Facts are scoped to the insertion domain, and can be supplied by a verified
    static analysis or a separately checked certificate. This pass preserves
    semantic properties, not the runtime check's refusal behavior. In particular
    a certified true fact may be removed even if its dynamic check returns None. *)
Fixpoint residualize {A} (known : A -> option bool) (p : formula A) : formula A :=
  match p with
  | Constant b => Constant b
  | Fact a => match known a with Some b => Constant b | None => Fact a end
  | Conjunction l r => smart_and (residualize known l) (residualize known r)
  | Disjunction l r => smart_or (residualize known l) (residualize known r)
  | Complement q => smart_not (residualize known q)
  end.

Lemma smart_and_property : forall S A (P : A -> S -> Prop) p q s,
  formula_property P (smart_and p q) s <->
  formula_property P p s /\ formula_property P q s.
Proof.
  intros S A P p q s; destruct p; destruct q;
    cbn [smart_and formula_property]; try tauto;
    repeat match goal with b : bool |- _ => destruct b end;
    cbn [formula_property]; tauto.
Qed.

Lemma smart_or_property : forall S A (P : A -> S -> Prop) p q s,
  formula_property P (smart_or p q) s <->
  formula_property P p s \/ formula_property P q s.
Proof.
  intros S A P p q s; destruct p; destruct q;
    cbn [smart_or formula_property]; try tauto;
    repeat match goal with b : bool |- _ => destruct b end;
    cbn [formula_property]; tauto.
Qed.

Lemma smart_not_property : forall S A (P : A -> S -> Prop) p s,
  formula_property P (smart_not p) s <-> ~ formula_property P p s.
Proof.
  intros S A P p s; destruct p; cbn [smart_not formula_property]; try tauto.
  destruct value; cbn; tauto.
Qed.

Theorem residualize_property : forall S A I (P : A -> S -> Prop) known,
  (forall a s b, I s -> known a = Some b -> decision_evidence (P a s) b) ->
  forall p s, I s ->
  (formula_property P (residualize known p) s <-> formula_property P p s).
Proof.
  intros S A I P known CERT p; induction p; intros s INV; cbn [residualize].
  - reflexivity.
  - destruct (known atom) as [b|] eqn:KNOWN; [|reflexivity].
    pose proof (CERT atom s b INV KNOWN) as EVIDENCE.
    destruct b; cbn [formula_property decision_evidence] in *; tauto.
  - rewrite smart_and_property, IHp1, IHp2 by exact INV; reflexivity.
  - rewrite smart_or_property, IHp1, IHp2 by exact INV; reflexivity.
  - rewrite smart_not_property, IHp by exact INV; reflexivity.
Qed.

Theorem residual_guard_preservation : forall S A I
  (L : language S) (D : property_dimension S A I)
  (primitives : check_primitives L I (decide_atom D)) known p R source candidate,
  (forall a s b, I s -> known a = Some b ->
    decision_evidence (atom_property D a s) b) ->
  (forall o, R o o) ->
  conditional_preservation L I (formula_property (atom_property D) p)
    R source candidate ->
  forall s original, I s -> command_run L source s original ->
  exists target,
    command_run L (compile_condition primitives (residualize known p)
      candidate source source) s target /\ R original target.
Proof.
  intros S A I L D primitives known p R source candidate CERT REFL LOCAL.
  apply property_guard_preservation; auto.
  intros s original INV PROP RUN. apply LOCAL; auto.
  apply (proj1 (@residualize_property S A I (atom_property D) known CERT p s INV));
    exact PROP.
Qed.

Theorem contradiction_rejects : forall S A (E : A -> S -> option bool) a s,
  formula_accepts E (Conjunction (Fact a) (Complement (Fact a))) s = false.
Proof. intros; unfold formula_accepts; cbn; destruct (E a s) as [[]|]; reflexivity. Qed.

Theorem unknown_negation_rejects : forall S A (E : A -> S -> option bool) a s,
  E a s = None -> formula_accepts E (Complement (Fact a)) s = false.
Proof. intros; unfold formula_accepts; cbn; rewrite H; reflexivity. Qed.

Print Assumptions residualize_property.
Print Assumptions residual_guard_preservation.
