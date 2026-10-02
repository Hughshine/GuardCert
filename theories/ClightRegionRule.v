From compcert.common Require Import Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import AbstractGuard SemanticFacts ClightGuard ClightCondition
  ClightPureExpr ClightDecisionRule ClightRegionRewrite CompCertMemoryEquivalence.
Set Implicit Arguments.

(** This is the author-facing interface for a conditional statement rewrite.
    Properties and check implementations belong to the language instance. *)
Record encoded_region_rule (source candidate : statement) := EncodedRegionRule {
  region_rule_atoms : Type;
  region_rule_domain : clight_entry -> Prop;
  region_rule_dimension : property_dimension clight_entry region_rule_atoms region_rule_domain;
  region_rule_primitives : check_primitives decision_test_language region_rule_domain
    (decide_atom region_rule_dimension);
  region_rule_formula : formula region_rule_atoms;
  region_rule_entry : forall temps p e le m le' m',
    exec_stmt (adapter_entry temps) (globalenv p) e le m source E0 le' m' Out_normal ->
    region_rule_domain (Entry (globalenv p) e le m);
  region_rule_local : forall temps p e le m le' m',
    exec_stmt (adapter_entry temps) (globalenv p) e le m source E0 le' m' Out_normal ->
    formula_property (atom_property region_rule_dimension) region_rule_formula
      (Entry (globalenv p) e le m) ->
    exists target_memory,
      exec_stmt (adapter_entry temps) (globalenv p) e le m candidate E0 le' target_memory Out_normal /\
      memory_equivalent m' target_memory
}.

Definition generated_region_tree {source candidate} (r : encoded_region_rule source candidate) :=
  synthesize_decision_tree (region_rule_primitives r) (region_rule_formula r).
Definition generated_region {source candidate} (r : encoded_region_rule source candidate) :=
  tree_statement (generated_region_tree r) candidate source.

Theorem encoded_region_rule_guarded : forall source candidate
  (r : encoded_region_rule source candidate),
  guarded_fragment_contract source (generated_region_tree r) candidate.
Proof.
  intros source candidate r temps p e le m le' m' SOURCE.
  assert (INV : region_rule_domain r (Entry (globalenv p) e le m)).
  { eapply region_rule_entry; eauto. }
  exists (formula_accepts (decide_atom (region_rule_dimension r))
    (region_rule_formula r) (Entry (globalenv p) e le m)); split.
  - apply (proj2 (@synthesized_decision_tree_correct (region_rule_atoms r)
      (region_rule_domain r) (decide_atom (region_rule_dimension r))
      (region_rule_primitives r) (region_rule_formula r) _ _ INV)); reflexivity.
  - intro ACCEPT. eapply region_rule_local; [exact SOURCE |].
    eapply synthesized_decision_tree_property; [exact INV |].
    apply (proj2 (@synthesized_decision_tree_correct (region_rule_atoms r)
      (region_rule_domain r) (decide_atom (region_rule_dimension r))
      (region_rule_primitives r) (region_rule_formula r) _ true INV)).
    symmetry; exact ACCEPT.
Qed.

Theorem encoded_region_rule_sound : forall source candidate
  (r : encoded_region_rule source candidate), region_contract source (generated_region r).
Proof. intros; apply guarded_fragment_region_contract, encoded_region_rule_guarded. Qed.

Print Assumptions encoded_region_rule_sound.
