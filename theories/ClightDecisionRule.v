From Stdlib Require Import Bool.
From compcert.cfrontend Require Import Clight.
From Guard Require Import AbstractGuard SemanticFacts ClightCondition ClightPureExpr
  ClightTreeRule ClightTreeRewrite.
Set Implicit Arguments.

(** An atomic check may itself be a certified conditional tree. This is useful
    when evaluating one presumption needs short-circuiting safety checks. *)
Definition synthesize_decision_tree {A I E}
  (P : @check_primitives clight_entry A decision_test_language I E)
  (p : formula A) : decision_tree :=
  compile_condition P p (Decision true) (Decision false) (Decision false).

Theorem synthesized_decision_tree_correct : forall A I E
  (P : @check_primitives clight_entry A decision_test_language I E) p s b,
  I s -> (decision_run s (synthesize_decision_tree P p) b <->
    b = formula_accepts E p s).
Proof.
  intros A I E P p s b INV.
  change (command_run decision_test_language
    (compile_condition P p (Decision true) (Decision false) (Decision false)) s b
    <-> b = formula_accepts E p s).
  rewrite compile_condition_correct by exact INV.
  unfold formula_accepts.
  destruct (formula_execute E p s) as [v|]; [destruct v|];
    cbn [selected_command decision_test_language]; split; intro RUN;
    try (inversion RUN; reflexivity); subst; constructor.
Qed.

Theorem synthesized_decision_tree_property : forall A I
  (D : property_dimension clight_entry A I)
  (P : check_primitives decision_test_language I (decide_atom D)) p s,
  I s -> decision_run s (synthesize_decision_tree P p) true ->
  formula_property (atom_property D) p s.
Proof.
  intros A I D P p s INV RUN.
  apply synthesized_decision_tree_correct in RUN; auto.
  unfold formula_accepts in RUN.
  destruct (formula_execute (decide_atom D) p s) as [v|] eqn:EX;
    try discriminate. destruct v; try discriminate.
  exact (@formula_property_decision clight_entry A I D p s true INV EX).
Qed.

Record encoded_decision_rule (source candidate : expr) := EncodedDecisionRule {
  decision_rule_atoms : Type;
  decision_rule_domain : clight_entry -> Prop;
  decision_rule_dimension : property_dimension clight_entry decision_rule_atoms decision_rule_domain;
  decision_rule_primitives : check_primitives decision_test_language decision_rule_domain
    (decide_atom decision_rule_dimension);
  decision_rule_formula : formula decision_rule_atoms;
  decision_rule_type : typeof candidate = typeof source;
  decision_rule_entry : forall s, source_defined source s -> decision_rule_domain s;
  decision_rule_local : forall s v,
    eval_expr (entry_ge s) (entry_env s) (entry_temps s) (entry_memory s) source v ->
    formula_property (atom_property decision_rule_dimension) decision_rule_formula s ->
    eval_expr (entry_ge s) (entry_env s) (entry_temps s) (entry_memory s) candidate v
}.

Definition generated_decision_tree {source candidate}
  (r : encoded_decision_rule source candidate) :=
  synthesize_decision_tree (decision_rule_primitives r) (decision_rule_formula r).

Theorem encoded_decision_rule_sound : forall source candidate
  (r : encoded_decision_rule source candidate),
  ClightTreeRewrite.expression_contract source (generated_decision_tree r) candidate.
Proof.
  intros source candidate r. split; [exact (decision_rule_type r)|].
  intros ge e le m v EV.
  assert (INV : decision_rule_domain r (Entry ge e le m)).
  { apply decision_rule_entry. exists v; exact EV. }
  exists (formula_accepts (decide_atom (decision_rule_dimension r))
    (decision_rule_formula r) (Entry ge e le m)); split.
  - apply (proj2 (@synthesized_decision_tree_correct (decision_rule_atoms r)
      (decision_rule_domain r) (decide_atom (decision_rule_dimension r))
      (decision_rule_primitives r) (decision_rule_formula r) (Entry ge e le m) _ INV));
      reflexivity.
  - intro ACCEPT. eapply (decision_rule_local r (Entry ge e le m) (v := v)); [exact EV|].
    eapply synthesized_decision_tree_property; [exact INV|].
    apply (proj2 (@synthesized_decision_tree_correct (decision_rule_atoms r)
      (decision_rule_domain r) (decide_atom (decision_rule_dimension r))
      (decision_rule_primitives r) (decision_rule_formula r) (Entry ge e le m) true INV)).
    symmetry; exact ACCEPT.
Qed.

Print Assumptions encoded_decision_rule_sound.
