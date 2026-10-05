From Guard Require Import AbstractGuard SemanticFacts ClightCondition ClightPureExpr ClightDecisionRule.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite ClightReadonlyTreeFacts.
Set Implicit Arguments.

(** Some atoms need several short-circuit tests. Reuse the certified formula
    compiler with tree-valued tests, and additionally certify the safety of
    every reachable expression. Both validity and value trees are scalar here;
    atoms containing loads must supply stronger path-sensitive safety proofs. *)
Lemma compiled_scalar_tree_pure A I E
  (P : @check_primitives clight_entry A decision_test_language I E)
  (VALIDITY : forall atom, pure_tree (validity_test P atom))
  (VALUE : forall atom, pure_tree (value_test P atom)) premise :
  forall yes no unknown, pure_tree yes -> pure_tree no -> pure_tree unknown ->
  pure_tree (compile_condition P premise yes no unknown).
Proof.
  induction premise; intros yes no unknown YES NO UNKNOWN;
    cbn [compile_condition decision_test_language conditional].
  - destruct value; assumption.
  - apply pure_decision_bind; [apply VALIDITY| |exact UNKNOWN].
    apply pure_decision_bind; auto.
  - apply IHpremise1; auto; apply IHpremise2; assumption.
  - apply IHpremise1; auto; apply IHpremise2; assumption.
  - apply IHpremise; assumption.
Qed.

Lemma synthesized_scalar_tree_safe A I E
  (P : @check_primitives clight_entry A decision_test_language I E)
  (VALIDITY : forall atom, pure_tree (validity_test P atom))
  (VALUE : forall atom, pure_tree (value_test P atom)) premise entry :
  I entry -> readonly_tree_safe entry (synthesize_decision_tree P premise).
Proof.
  intro DOMAIN; eapply pure_decision_run_safe.
  - unfold synthesize_decision_tree; apply compiled_scalar_tree_pure; auto; constructor.
  - apply (proj2 (synthesized_decision_tree_correct P premise entry
      (formula_accepts E premise entry) DOMAIN)); reflexivity.
Qed.

Definition synthesized_scalar_tree_condition fe O
  (observe : ClightCondition.fragment_observation -> O -> Prop) A I
  (D : property_dimension clight_entry A I)
  (P : check_primitives decision_test_language I (decide_atom D))
  (VALIDITY : forall atom, pure_tree (validity_test P atom))
  (VALUE : forall atom, pure_tree (value_test P atom)) premise :
  readonly_condition (readonly_clight_host fe observe) I
    (fun entry => formula_property (atom_property D) premise entry)
    (synthesize_decision_tree P premise).
Proof.
  constructor.
  - intros entry DOMAIN; apply synthesized_scalar_tree_safe; assumption.
  - intros entry DOMAIN; exists (formula_accepts (decide_atom D) premise entry), entry.
    split; [|reflexivity].
    apply (proj2 (synthesized_decision_tree_correct P premise entry _ DOMAIN)); reflexivity.
  - intros entry accepted checked DOMAIN [RUN SAME]; split; [exact SAME|].
    intro ACCEPT; subst accepted; eapply synthesized_decision_tree_property; eassumption.
Defined.

Print Assumptions compiled_scalar_tree_pure.
Print Assumptions synthesized_scalar_tree_safe.
Print Assumptions synthesized_scalar_tree_condition.
