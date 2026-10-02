From Guard Require Import AbstractGuard SemanticFacts.
Set Implicit Arguments.

(** A language bridge can require more entry facts than its check library.
    Restricting the justified domain preserves the existing code and evidence. *)
Definition restrict_dimension {S A} {I J : S -> Prop}
  (IMPLIES : forall s, J s -> I s) (D : property_dimension S A I) :
  property_dimension S A J.
Proof.
  refine {| atom_property := atom_property D; decide_atom := decide_atom D |}.
  intros a s b DOMAIN CHECK; eapply decide_atom_correct; [apply IMPLIES; exact DOMAIN | exact CHECK].
Defined.

Definition restrict_primitives {S A} {L : language S} {I J : S -> Prop}
  (IMPLIES : forall s, J s -> I s) (D : property_dimension S A I)
  (P : check_primitives L I (decide_atom D)) :
  check_primitives L J (decide_atom (restrict_dimension IMPLIES D)).
Proof.
  refine {| validity_test := validity_test P; value_test := value_test P |}.
  - intros a s b DOMAIN; apply validity_test_correct; apply IMPLIES; exact DOMAIN.
  - intros a s b expected DOMAIN CHECK; eapply value_test_correct;
      [apply IMPLIES; exact DOMAIN | exact CHECK].
Defined.

Lemma restriction_preserves_compiled_condition {S A} {L : language S} {I J : S -> Prop}
  (IMPLIES : forall s, J s -> I s) (D : property_dimension S A I)
  (P : check_primitives L I (decide_atom D)) formula yes no unknown :
  compile_condition (restrict_primitives IMPLIES D P) formula yes no unknown =
    compile_condition P formula yes no unknown.
Proof.
  revert yes no unknown; induction formula; intros;
    cbn [compile_condition restrict_primitives]; f_equal; auto.
  all: rewrite IHformula1, IHformula2; reflexivity.
Qed.

Print Assumptions restrict_dimension.
Print Assumptions restrict_primitives.
Print Assumptions restriction_preserves_compiled_condition.
