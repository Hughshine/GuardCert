From Guard Require Import AbstractGuard SemanticFacts ClightCondition ClightDecisionRule ClightPureExpr.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite ClightQuietDeterminacy.
Set Implicit Arguments.

(** Ordinary loads in Clight expressions are read-only, but may be undefined.
    A completed path and expression determinacy prove safety for every reachable
    test. Certificates still owe a completed check on every entry in their domain. *)
Lemma readonly_test_determinate expression entry first second :
  expression_test expression entry first -> expression_test expression entry second -> first = second.
Proof.
  intros [v [EVAL BOOL]] [other [OTHER OTHER_BOOL]].
  pose proof (proj1 (expressions_determinate (entry_ge entry) (entry_env entry)
    (entry_temps entry) (entry_memory entry)) _ _ EVAL _ OTHER) as SAME; subst other; congruence.
Qed.
Lemma readonly_decision_determinate tree : forall entry first second,
  decision_run entry tree first -> decision_run entry tree second -> first = second.
Proof.
  induction tree as [answer|expression yes YES no NO]; intros entry first second RUN OTHER;
    inversion RUN; inversion OTHER; subst; [reflexivity|].
  match goal with A : expression_test expression entry ?a,
    B : expression_test expression entry ?b |- _ =>
    pose proof (readonly_test_determinate A B) as SAME; subst b;
    destruct a; [eapply YES|eapply NO]; eassumption end.
Qed.
Lemma readonly_decision_run_safe tree : forall entry answer,
  decision_run entry tree answer -> readonly_tree_safe entry tree.
Proof.
  intros entry answer RUN; induction RUN; cbn [readonly_tree_safe]; [exact I|split].
  - eexists; eassumption.
  - intros other TEST; assert (SAME : other = b) by (eapply readonly_test_determinate; eassumption).
    subst other; exact IHRUN.

Qed.

(** Positive check packaging also applies to trees containing ordinary loads.
    A completed path on every domain entry replaces the scalar-purity premise;
    a refused check remains unknown rather than certifying a complement. *)
Definition positive_readonly_tree_primitives {A I} property accept
  (SOUND : forall a s, I s -> accept a s = true -> property a s)
  (trees : A -> decision_tree)
  (TOTAL : forall a s, I s -> decision_run s (trees a) (accept a s)) :
  check_primitives decision_test_language I
    (decide_atom (@positive_dimension clight_entry A I property accept SOUND)).
Proof.
  refine (@CheckPrimitives clight_entry A decision_test_language I
    (decide_atom (@positive_dimension clight_entry A I property accept SOUND)) trees
    (fun _ => Decision true) _ _).
  - intros a s b DOMAIN; cbn [decision_test_language].
    assert (EXACT : decision_run s (trees a) b <-> b = accept a s).
    { split; [intro RUN; eapply readonly_decision_determinate; [exact RUN|apply TOTAL; exact DOMAIN]|
        intro SAME; subst; apply TOTAL; exact DOMAIN]. }
    rewrite EXACT; cbn [positive_dimension decide_atom]; destruct (accept a s); reflexivity.
  - intros a s b expected DOMAIN ACCEPTED; cbn [decision_test_language].
    cbn [positive_dimension decide_atom] in ACCEPTED.
    destruct (accept a s); try discriminate; injection ACCEPTED as SAME; subst expected.
    split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
Defined.

Definition synthesized_loaded_tree_condition fe O (observe : fragment_observation -> O -> Prop) A I
  (D : property_dimension clight_entry A I)
  (P : check_primitives decision_test_language I (decide_atom D)) premise :
  readonly_condition (readonly_clight_host fe observe) I
    (fun entry => formula_property (atom_property D) premise entry)
    (synthesize_decision_tree P premise).
Proof.
  constructor.
  - intros entry DOMAIN; apply readonly_decision_run_safe with
      (answer := formula_accepts (decide_atom D) premise entry).
    apply (proj2 (synthesized_decision_tree_correct P premise entry _ DOMAIN)); reflexivity.
  - intros entry DOMAIN; exists (formula_accepts (decide_atom D) premise entry), entry; split; [|reflexivity].
    apply (proj2 (synthesized_decision_tree_correct P premise entry _ DOMAIN)); reflexivity.
  - intros entry accepted checked DOMAIN [RUN SAME]; split; [exact SAME|].
    intro ACCEPT; subst accepted; eapply synthesized_decision_tree_property; eassumption.
Defined.
Print Assumptions readonly_decision_run_safe.
Print Assumptions synthesized_loaded_tree_condition.
Print Assumptions positive_readonly_tree_primitives.
