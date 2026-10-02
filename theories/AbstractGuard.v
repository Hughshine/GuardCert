From Stdlib Require Import Bool List.
Set Implicit Arguments.

(** The kernel knows no integers, addresses, machine flags or memory model.
    Atomic facts and their checked interpretation belong to a language instance.
    None is failure to check, and remains distinct from a checked false value. *)
Inductive formula (Atom : Type) :=
| Constant (value : bool)
| Fact (atom : Atom)
| Conjunction (left right : formula Atom)
| Disjunction (left right : formula Atom)
| Complement (body : formula Atom).

Arguments Constant {Atom} _.
Arguments Fact {Atom} _.
Arguments Conjunction {Atom} _ _.
Arguments Disjunction {Atom} _ _.
Arguments Complement {Atom} _.

Fixpoint formula_meaning {S A} (meaning : A -> S -> bool)
  (p : formula A) (s : S) : bool :=
  match p with
  | Constant b => b
  | Fact a => meaning a s
  | Conjunction l r => formula_meaning meaning l s && formula_meaning meaning r s
  | Disjunction l r => formula_meaning meaning l s || formula_meaning meaning r s
  | Complement q => negb (formula_meaning meaning q s)
  end.

Fixpoint formula_execute {S A} (evaluate : A -> S -> option bool)
  (p : formula A) (s : S) : option bool :=
  match p with
  | Constant b => Some b
  | Fact a => evaluate a s
  | Conjunction l r =>
      match formula_execute evaluate l s with
      | Some true => formula_execute evaluate r s
      | Some false => Some false
      | None => None
      end
  | Disjunction l r =>
      match formula_execute evaluate l s with
      | Some true => Some true
      | Some false => formula_execute evaluate r s
      | None => None
      end
  | Complement q =>
      match formula_execute evaluate q s with
      | Some b => Some (negb b)
      | None => None
      end
  end.

Definition formula_accepts {S A} evaluate (p : formula A) (s : S) : bool :=
  match formula_execute evaluate p s with Some true => true | _ => false end.

Theorem formula_execute_sound : forall (S A : Type) (I : S -> Prop)
  (meaning : A -> S -> bool) (evaluate : A -> S -> option bool),
  (forall a s b, I s -> evaluate a s = Some b -> b = meaning a s) ->
  forall p s b, I s -> formula_execute evaluate p s = Some b ->
    b = formula_meaning meaning p s.
Proof.
  intros S A I meaning evaluate ATOM p; induction p;
    intros s b INV EX; cbn [formula_execute formula_meaning] in *.
  - inversion EX; reflexivity.
  - eapply ATOM; eauto.
  - destruct (formula_execute evaluate p1 s) as [v|] eqn:LEFT; try discriminate.
    rewrite <- (IHp1 s v INV LEFT). destruct v; cbn in *.
    + eapply IHp2; eauto.
    + inversion EX; reflexivity.
  - destruct (formula_execute evaluate p1 s) as [v|] eqn:LEFT; try discriminate.
    rewrite <- (IHp1 s v INV LEFT). destruct v; cbn in *.
    + inversion EX; reflexivity.
    + eapply IHp2; eauto.
  - destruct (formula_execute evaluate p s) as [v|] eqn:BODY; try discriminate.
    inversion EX; subst. rewrite (IHp s v INV BODY); reflexivity.
Qed.

Theorem formula_accepts_sound : forall (S A : Type) (I : S -> Prop)
  (meaning : A -> S -> bool) (evaluate : A -> S -> option bool),
  (forall a s b, I s -> evaluate a s = Some b -> b = meaning a s) ->
  forall p s, I s -> formula_accepts evaluate p s = true ->
    formula_meaning meaning p s = true.
Proof.
  intros S A I meaning evaluate ATOM p s INV ACCEPT.
  unfold formula_accepts in ACCEPT.
  destruct (formula_execute evaluate p s) as [b|] eqn:EX; try discriminate.
  destruct b; try discriminate.
  symmetry; eapply formula_execute_sound; eauto.
Qed.

(** [command_run] is an instance-defined observation relation. It may describe
    complete behaviors, traces and exits, or a terminating fragment relation.
    The meaning of its observations must be stated by the instance.
    [conditional_spec] explicitly says tests preserve the entry state and do
    not add observations. This is a proof obligation, not an implicit claim
    about arbitrary effectful conditions. *)
Record language (S : Type) := Language {
  command : Type;
  test : Type;
  observation : Type;
  command_run : command -> S -> observation -> Prop;
  test_run : test -> S -> bool -> Prop;
  conditional : test -> command -> command -> command;
  conditional_spec : forall t yes no s o,
    command_run (conditional t yes no) s o <->
    exists b, test_run t s b /\ command_run (if b then yes else no) s o
}.

Arguments command_run {S} l _ _ _.
Arguments test_run {S} l _ _ _.
Arguments conditional {S} l _ _ _.

Lemma conditional_known : forall S (L : language S) t yes no s o b,
  (forall v, test_run L t s v <-> v = b) ->
  (command_run L (conditional L t yes no) s o <->
   command_run L (if b then yes else no) s o).
Proof.
  intros S L t yes no s o b KNOWN.
  rewrite conditional_spec. split.
  - intros [v [EV RUN]]. apply KNOWN in EV; subst; exact RUN.
  - intro RUN. exists b. split; [apply KNOWN; reflexivity|exact RUN].
Qed.

Definition checked_valid (v : option bool) : bool :=
  match v with Some _ => true | None => false end.

(** The language lowers an atomic check to two tests. The value test is only
    required to be defined after validity succeeds. A failed check need not
    execute any potentially undefined value test. Entry domain [I] is supplied
    by the host/instance and must be justified at the actual insertion point. *)
Record check_primitives {S A} (L : language S) (I : S -> Prop)
  (evaluate : A -> S -> option bool) := CheckPrimitives {
  validity_test : A -> test L;
  value_test : A -> test L;
  validity_test_correct : forall a s b, I s ->
    (test_run L (validity_test a) s b <-> b = checked_valid (evaluate a s));
  value_test_correct : forall a s b v, I s -> evaluate a s = Some v ->
    (test_run L (value_test a) s b <-> b = v)
}.

Fixpoint compile_condition {S A} {L : language S} {I evaluate}
  (primitives : check_primitives L I evaluate) (p : formula A)
  (yes no unknown : command L) : command L :=
  match p with
  | Constant b => if b then yes else no
  | Fact a => conditional L (validity_test primitives a)
      (conditional L (value_test primitives a) yes no) unknown
  | Conjunction l r => compile_condition primitives l
      (compile_condition primitives r yes no unknown) no unknown
  | Disjunction l r => compile_condition primitives l
      yes (compile_condition primitives r yes no unknown) unknown
  | Complement q => compile_condition primitives q no yes unknown
  end.

Definition selected_command {S} {L : language S}
  (result : option bool) (yes no unknown : command L) : command L :=
  match result with Some true => yes | Some false => no | None => unknown end.

(** The executable compiler uses only the supplied if constructor and atomic
    tests. This exact dispatch result includes failure, rather than proving only
    that a check which happens to accept is sound. *)
Theorem compile_condition_correct : forall S A (L : language S) I evaluate
  (primitives : @check_primitives S A L I evaluate) p yes no unknown s o,
  I s ->
  (command_run L (compile_condition primitives p yes no unknown) s o <->
   command_run L (selected_command (formula_execute evaluate p s) yes no unknown) s o).
Proof.
  intros S A L I evaluate primitives p; induction p;
    intros yes no unknown s o INV;
    cbn [compile_condition formula_execute selected_command].
  - destruct value; reflexivity.
  - destruct (evaluate atom s) as [v|] eqn:EX.
    + rewrite (@conditional_known S L (validity_test primitives atom)
        (conditional L (value_test primitives atom) yes no) unknown s o true).
      2:{ intro b. rewrite (validity_test_correct primitives atom s b INV), EX.
          reflexivity. }
      rewrite (@conditional_known S L (value_test primitives atom) yes no s o v).
      2:{ intro b. eapply value_test_correct; eauto. }
      destruct v; reflexivity.
    + rewrite (@conditional_known S L (validity_test primitives atom)
        (conditional L (value_test primitives atom) yes no) unknown s o false).
      2:{ intro b. rewrite (validity_test_correct primitives atom s b INV), EX.
          reflexivity. }
      reflexivity.
  - rewrite IHp1 by exact INV.
    destruct (formula_execute evaluate p1 s) as [v|]; [destruct v|];
      cbn [selected_command]; try reflexivity. apply IHp2; exact INV.
  - rewrite IHp1 by exact INV.
    destruct (formula_execute evaluate p1 s) as [v|]; [destruct v|];
      cbn [selected_command]; try reflexivity. apply IHp2; exact INV.
  - rewrite IHp by exact INV.
    destruct (formula_execute evaluate p s) as [v|]; [destruct v|]; reflexivity.
Qed.

(** The output relation also belongs to the host. Equality, live-out relations,
    memory equivalences and trace/exit relations can be different instances. *)
Definition conditional_refinement {S} (L : language S)
  (I premise : S -> Prop) (R : observation L -> observation L -> Prop)
  (source candidate : command L) : Prop :=
  forall s target, I s -> premise s -> command_run L candidate s target ->
  exists original, command_run L source s original /\ R target original.

Theorem compiled_guard_refinement : forall (S A : Type) (L : language S) I
  (meaning : A -> S -> bool) evaluate
  (primitives : @check_primitives S A L I evaluate) p R source candidate,
  (forall a s b, I s -> evaluate a s = Some b -> b = meaning a s) ->
  (forall o, R o o) ->
  conditional_refinement L I (fun s => formula_meaning meaning p s = true)
    R source candidate ->
  forall s target, I s ->
  command_run L (compile_condition primitives p candidate source source) s target ->
  exists original, command_run L source s original /\ R target original.
Proof.
  intros S A L I meaning evaluate primitives p R source candidate
    ATOM REFL LOCAL s target INV RUN.
  apply (proj1 (@compile_condition_correct S A L I evaluate primitives p
    candidate source source s target INV)) in RUN.
  destruct (formula_execute evaluate p s) as [b|] eqn:EX;
    cbn [selected_command] in RUN.
  - destruct b.
    + apply LOCAL; auto. symmetry; eapply formula_execute_sound; eauto.
    + exists target; split; auto.
  - exists target; split; auto.
Qed.

(** A source execution can reach the generated code when its selected leaf
    can execute. In particular, the compiler cannot cause a missing guard
    execution on an entry satisfying I. The candidate's progress remains a
    separate local obligation. *)
Theorem compile_condition_reachable : forall S A (L : language S) I evaluate
  (primitives : @check_primitives S A L I evaluate) p yes no unknown s o,
  I s ->
  command_run L (selected_command (formula_execute evaluate p s) yes no unknown) s o ->
  command_run L (compile_condition primitives p yes no unknown) s o.
Proof.
  intros; apply (proj2 (@compile_condition_correct S A L I evaluate primitives p
    yes no unknown s o H)); assumption.
Qed.

Print Assumptions formula_execute_sound.
Print Assumptions compile_condition_correct.
Print Assumptions compiled_guard_refinement.

(** The dual local obligation supplies candidate progress for every source
    execution. It is kept separate from backward refinement: a candidate with
    no executions trivially satisfies backward refinement but is not a usable
    compiler pass. Hosts such as CompCert consume forward preservation. *)
Definition conditional_preservation {S} (L : language S)
  (I premise : S -> Prop) (R : observation L -> observation L -> Prop)
  (source candidate : command L) : Prop :=
  forall s original, I s -> premise s -> command_run L source s original ->
  exists target, command_run L candidate s target /\ R original target.
