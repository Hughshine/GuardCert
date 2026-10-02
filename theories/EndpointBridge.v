From Guard Require Import AbstractGuard.
Set Implicit Arguments.

(** PolCert's exposed theorem currently has the backward endpoint shape:
    an optimized terminating execution has a matching source execution modulo
    State.eq. A forward host also needs optimized progress. This theorem records
    precisely the additional obligations; it does not assert them for PolCert. *)
Theorem endpoint_refinement_to_preservation : forall S (L : language S)
  I premise R source candidate,
  (forall x y, R x y -> R y x) ->
  (forall x y z, R x y -> R y z -> R x z) ->
  (forall s x y, I s -> premise s ->
    command_run L source s x -> command_run L source s y -> R x y) ->
  (forall s original, I s -> premise s -> command_run L source s original ->
    exists target, command_run L candidate s target) ->
  conditional_refinement L I premise R source candidate ->
  conditional_preservation L I premise R source candidate.
Proof.
  intros S L I premise R source candidate SYMM TRANS DETERMINATE PROGRESS BACKWARD
    s original INV PROP SOURCE.
  destruct (PROGRESS s original INV PROP SOURCE) as [target TARGET].
  destruct (BACKWARD s target INV PROP TARGET) as [other [OTHER REL]].
  exists target; split; auto.
  eapply TRANS; [eapply DETERMINATE; eauto|apply SYMM; exact REL].
Qed.

(** A counterexample to silently dropping the progress obligation. *)
Definition progress_example_language : language unit.
Proof.
  refine {| command := bool; test := bool; observation := unit;
    command_run := fun c _ _ => c = true;
    test_run := fun t _ b => b = t;
    conditional := fun t yes no => if t then yes else no |}.
  intros t yes no s o; split.
  - intro H; exists t; auto.
  - intros [b [EQ RUN]]; subst b; exact RUN.
Defined.

Example empty_candidate_refines :
  conditional_refinement progress_example_language (fun _ => True) (fun _ => True)
    eq true false.
Proof. intros s target INV PROP RUN; discriminate RUN. Qed.

Example empty_candidate_has_no_preservation :
  ~ conditional_preservation progress_example_language (fun _ => True) (fun _ => True)
    eq true false.
Proof.
  intro H. destruct (H tt tt I I eq_refl) as [target [RUN EQ]]. discriminate RUN.
Qed.

Print Assumptions endpoint_refinement_to_preservation.
