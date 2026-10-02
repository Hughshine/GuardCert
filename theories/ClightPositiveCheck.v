From Stdlib Require Import Bool.
From Guard Require Import AbstractGuard SemanticFacts ClightCondition ClightPureExpr.
Set Implicit Arguments.

(** Package a certified positive check. Refusal is unknown, so clients may
    safely use this dimension in formulas containing complements. *)
Definition positive_tree_primitives {A I} property accept
  (SOUND : forall a s, I s -> accept a s = true -> property a s)
  (trees : A -> decision_tree)
  (PURE : forall a, pure_tree (trees a))
  (TOTAL : forall a s, I s -> decision_run s (trees a) (accept a s)) :
  check_primitives decision_test_language I
    (decide_atom (@positive_dimension clight_entry A I property accept SOUND)).
Proof.
  refine (@CheckPrimitives clight_entry A decision_test_language I
    (decide_atom (@positive_dimension clight_entry A I property accept SOUND)) trees
    (fun _ => Decision true) _ _).
  - intros a s b DOMAIN; cbn [decision_test_language].
    assert (EXACT : decision_run s (trees a) b <-> b = accept a s).
    { split; [intro RUN; eapply pure_tree_determinate; eauto|intro SAME; subst; auto]. }
    rewrite EXACT; cbn [positive_dimension decide_atom]. destruct (accept a s); reflexivity.
  - intros a s b expected DOMAIN ACCEPTED; cbn [decision_test_language].
    cbn [positive_dimension decide_atom] in ACCEPTED.
    destruct (accept a s); try discriminate; injection ACCEPTED as SAME; subst expected.
    split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
Defined.

Print Assumptions positive_tree_primitives.
