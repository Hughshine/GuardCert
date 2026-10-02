From Stdlib Require Import Bool List ZArith.
From Guard Require Import AbstractGuard SemanticFacts.
From polcert.polygen Require Import InstrTy Loop.
Import ListNotations.
Set Implicit Arguments.

(** Loop tests read mathematical iterator parameters. Memory-dependent checks
    require a surrounding language adapter; they cannot be encoded here merely
    by adding a new proposition to a guard formula. *)
Module PolCertLoopGuard (I : INSTR).
Module L := Loop I.

Record entry := Entry {
  parameters : list Z;
  memory : I.State.t
}.

Definition choose (t : L.test) (yes no : L.stmt) : L.stmt :=
  L.Seq (L.SCons (L.Guard t yes)
    (L.SCons (L.Guard (L.Not t) no) L.SNil)).

Lemma guard_execution t c env m m' :
  L.loop_semantics (L.Guard t c) env m m' <->
  if L.eval_test env t then L.loop_semantics c env m m' else m = m'.
Proof.
  destruct (L.eval_test env t) eqn:CHECK; split; intro RUN.
  - inversion RUN; subst; auto; congruence.
  - apply L.LGuardTrue; auto.
  - inversion RUN; subst; auto; congruence.
  - subst m'. apply L.LGuardFalse; auto.
Qed.

Lemma pair_execution a b env m m' :
  L.loop_semantics (L.Seq (L.SCons a (L.SCons b L.SNil))) env m m' <->
  exists middle, L.loop_semantics a env m middle /\
                 L.loop_semantics b env middle m'.
Proof.
  split.
  - intro RUN. inversion RUN; subst.
    match goal with TAIL: L.loop_semantics (L.Seq (L.SCons b L.SNil)) _ _ _ |- _ =>
      inversion TAIL; subst end.
    match goal with NIL: L.loop_semantics (L.Seq L.SNil) _ _ _ |- _ =>
      inversion NIL; subst end.
    eauto.
  - intros [middle [HEAD TAIL]].
    eapply L.LSeq; eauto. eapply L.LSeq; eauto. constructor.
Qed.

Lemma choose_execution t yes no env m m' :
  L.loop_semantics (choose t yes no) env m m' <->
  L.loop_semantics (if L.eval_test env t then yes else no) env m m'.
Proof.
  unfold choose. rewrite pair_execution.
  setoid_rewrite guard_execution. simpl.
  destruct (L.eval_test env t); simpl; split.
  - intros [middle [RUN EQ]]. subst; auto.
  - intro RUN. exists m'; auto.
  - intros [middle [EQ RUN]]. subst; auto.
  - intro RUN. exists m; auto.
Qed.

Definition loop_language : language entry.
Proof.
  refine {| command := L.stmt; test := L.test; observation := I.State.t;
    command_run := fun c s o => L.loop_semantics c (parameters s) (memory s) o;
    test_run := fun t s b => L.eval_test (parameters s) t = b;
    conditional := choose |}.
  intros t yes no s o. rewrite choose_execution. split.
  - intro RUN. exists (L.eval_test (parameters s) t); auto.
  - intros [b [CHECK RUN]]. subst b; auto.
Defined.

(** Parameters establish a property of the entry, and the language instance
    supplies executable Loop tests together with their encoding proofs. *)
Record encoded_atom (domain P : entry -> Prop) := EncodedAtom {
  validity : L.test;
  value : L.test;
  atom_evidence : forall s, domain s ->
    L.eval_test (parameters s) validity = true ->
    decision_evidence (P s) (L.eval_test (parameters s) value)
}.

Definition decide {domain P} (a : encoded_atom domain P) (s : entry) : option bool :=
  if L.eval_test (parameters s) (validity a)
  then Some (L.eval_test (parameters s) (value a)) else None.

Definition dimension {A} (domain : entry -> Prop) (P : A -> entry -> Prop)
  (atoms : forall a, encoded_atom domain (P a)) : property_dimension entry A domain.
Proof.
  refine {| atom_property := P; decide_atom := fun a s => decide (atoms a) s |}.
  intros a s b INV CHECK. unfold decide in CHECK.
  destruct (L.eval_test (parameters s) (validity (atoms a))) eqn:VALID;
    try discriminate.
  inversion CHECK; subst. eapply atom_evidence; eauto.
Defined.

Arguments dimension {A} domain P atoms.

Definition primitives {A} (domain : entry -> Prop) (P : A -> entry -> Prop)
  (atoms : forall a, encoded_atom domain (P a)) :
  check_primitives loop_language domain (decide_atom (dimension domain P atoms)).
Proof.
  refine (@CheckPrimitives entry A loop_language domain
    (decide_atom (dimension domain P atoms))
    (fun a => validity (atoms a)) (fun a => value (atoms a)) _ _).
  - intros a s b _. cbn. unfold decide.
    destruct (L.eval_test (parameters s) (validity (atoms a))) eqn:VALID;
      destruct b; simpl; split; congruence.
  - intros a s b v _ EX. cbn in *. unfold decide in EX.
    destruct (L.eval_test (parameters s) (validity (atoms a))) eqn:VALID;
      try discriminate. inversion EX; subst. split; congruence.
Defined.

Arguments primitives {A} domain P atoms.

Definition version {A} (domain : entry -> Prop) (P : A -> entry -> Prop)
  (atoms : forall a, encoded_atom domain (P a)) (condition : formula A)
  (source candidate : L.stmt) : L.stmt :=
  compile_condition (primitives domain P atoms) condition candidate source source.

Arguments version {A} domain P atoms condition source candidate.

Theorem version_preserves {A} (domain : entry -> Prop) (P : A -> entry -> Prop)
  (atoms : forall a, encoded_atom domain (P a)) condition source candidate
  (R : I.State.t -> I.State.t -> Prop) :
  (forall result, R result result) ->
  (forall s result, domain s -> formula_property P condition s ->
    L.loop_semantics source (parameters s) (memory s) result ->
    exists result', L.loop_semantics candidate (parameters s) (memory s) result' /\
                    R result result') ->
  forall s result, domain s -> L.loop_semantics source (parameters s) (memory s) result ->
  exists result', L.loop_semantics (version domain P atoms condition source candidate)
                    (parameters s) (memory s) result' /\ R result result'.
Proof.
  intros REFL LOCAL s result INV RUN.
  exact (@property_guard_preservation entry A domain
    loop_language (dimension domain P atoms) (primitives domain P atoms)
    condition R source candidate REFL
    (fun s result INV PRE RUN => LOCAL s result INV PRE RUN)
    s result INV RUN).
Qed.

Theorem version_refines {A} (domain : entry -> Prop) (P : A -> entry -> Prop)
  (atoms : forall a, encoded_atom domain (P a)) condition source candidate
  (R : I.State.t -> I.State.t -> Prop) :
  (forall result, R result result) ->
  (forall s result, domain s -> formula_property P condition s ->
    L.loop_semantics candidate (parameters s) (memory s) result ->
    exists result', L.loop_semantics source (parameters s) (memory s) result' /\
                    R result result') ->
  forall s result, domain s ->
  L.loop_semantics (version domain P atoms condition source candidate)
    (parameters s) (memory s) result ->
  exists result', L.loop_semantics source (parameters s) (memory s) result' /\
                  R result result'.
Proof.
  intros REFL LOCAL s result INV RUN.
  exact (@property_guard_refinement entry A domain
    loop_language (dimension domain P atoms) (primitives domain P atoms)
    condition R source candidate REFL
    (fun s result INV PRE RUN => LOCAL s result INV PRE RUN)
    s result INV RUN).
Qed.

(** A decidable parameter property, including negative evidence. *)
Definition zero_property (_ : unit) (s : entry) : Prop :=
  List.nth 0 (parameters s) 0%Z = 0%Z.

Definition zero_atom (_ : unit) : encoded_atom (fun _ => True) (zero_property tt).
Proof.
  refine {| validity := L.TConstantTest true;
            value := L.EQ (L.Var 0) (L.Constant 0) |}.
  intros s _ _. cbn [L.eval_test L.eval_expr zero_property].
  destruct (Z.eqb (List.nth 0 (parameters s) 0%Z) 0%Z) eqn:ZERO;
    cbn [decision_evidence].
  - apply Z.eqb_eq; auto.
  - apply Z.eqb_neq; auto.
Defined.

Definition impossible : formula unit :=
  Conjunction (Fact tt) (Complement (Fact tt)).

Theorem impossible_version source candidate s result :
  L.loop_semantics (version (fun _ => True) zero_property zero_atom
    impossible source candidate) (parameters s) (memory s) result <->
  L.loop_semantics source (parameters s) (memory s) result.
Proof.
  change (command_run loop_language
    (compile_condition (primitives (fun _ => True) zero_property zero_atom)
      impossible candidate source source) s result <->
    command_run loop_language source s result).
  rewrite compile_condition_correct by exact Logic.I.
  cbn [impossible formula_execute dimension decide_atom].
  unfold decide. cbn [zero_atom validity value L.eval_test L.eval_expr].
  destruct (Z.eqb (List.nth 0 (parameters s) 0%Z) 0%Z);
    cbn [selected_command]; tauto.
Qed.

Print Assumptions choose_execution.
Print Assumptions version_preserves.
Print Assumptions version_refines.
Print Assumptions impossible_version.

End PolCertLoopGuard.
