From Stdlib Require Import List.
From compcert.common Require Import AST Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import AbstractGuard SemanticFacts ClightGuard ClightCondition ClightPureExpr
  ClightDecisionRule ClightPrivateRegion ClightTempFrame ClightTempFootprint ClightProjectedExecution
  ClightSharedRegion CompCertMemoryEquivalence.
Set Implicit Arguments.
Import PrivateRegion.

Record encoded_private_rule (live : list ident) (source candidate : statement) := EncodedPrivateRule {
  private_rule_writes : list ident;
  private_rule_source_writes : writes_only private_rule_writes source;
  private_rule_atoms : Type;
  private_rule_domain : clight_entry -> Prop;
  private_rule_dimension : property_dimension clight_entry private_rule_atoms private_rule_domain;
  private_rule_primitives : check_primitives decision_test_language private_rule_domain
    (decide_atom private_rule_dimension);
  private_rule_formula : formula private_rule_atoms;
  private_rule_entry : forall temps p e le m le' m',
    exec_stmt (adapter_entry temps) (globalenv p) e le m source E0 le' m' Out_normal ->
    private_rule_domain (Entry (globalenv p) e le m);
  private_rule_local : forall temps p e le m le' m', statement_scope live source ->
    exec_stmt (adapter_entry temps) (globalenv p) e le m source E0 le' m' Out_normal ->
    formula_property (atom_property private_rule_dimension) private_rule_formula (Entry (globalenv p) e le m) ->
    exists target_temps target_memory,
      exec_stmt (adapter_entry temps) (globalenv p) e le m candidate E0 target_temps target_memory Out_normal /\
      temp_agree live le' target_temps /\ memory_equivalent m' target_memory
}.
Definition generated_private_tree {live source candidate} (rule : encoded_private_rule live source candidate) :=
  synthesize_decision_tree (private_rule_primitives rule) (private_rule_formula rule).
Definition generated_private_region {live source candidate} (rule : encoded_private_rule live source candidate) :=
  shared_guarded_statement (generated_private_tree rule) candidate source.

Theorem encoded_private_rule_sound live source candidate (rule : encoded_private_rule live source candidate) :
  projected_region_contract live source (generated_private_region rule).
Proof.
  intros temps p locals le target m le' m' SCOPE AGREE SOURCE f k.
  destruct (@structured_execution_temp_transport (adapter_entry temps) (globalenv p) locals le m source E0 le' m'
    Out_normal SOURCE live target (private_rule_writes rule) (private_rule_source_writes rule) SCOPE AGREE)
    as [source_exit [TARGET_SOURCE SOURCE_AGREE]].
  assert (DOMAIN : private_rule_domain rule (Entry (globalenv p) locals target m)) by (eapply private_rule_entry; eauto).
  set (flag := formula_accepts (decide_atom (private_rule_dimension rule))
    (private_rule_formula rule) (Entry (globalenv p) locals target m)).
  assert (CHECK : decision_run (Entry (globalenv p) locals target m) (generated_private_tree rule) flag).
  { apply (proj2 (@synthesized_decision_tree_correct (private_rule_atoms rule) (private_rule_domain rule)
      (decide_atom (private_rule_dimension rule)) (private_rule_primitives rule) (private_rule_formula rule) _ _ DOMAIN)); reflexivity. }
  assert (SELECTED : exists final memory,
    exec_stmt (adapter_entry temps) (globalenv p) locals target m (if flag then candidate else source) E0 final memory Out_normal /\
    temp_agree live le' final /\ memory_equivalent m' memory).
  { destruct flag eqn:ACCEPT.
    - assert (PROPERTY : formula_property (atom_property (private_rule_dimension rule))
        (private_rule_formula rule) (Entry (globalenv p) locals target m)).
      { eapply synthesized_decision_tree_property; [exact DOMAIN|exact CHECK]. }
      destruct (private_rule_local rule SCOPE TARGET_SOURCE PROPERTY) as [final [memory [RUN [FRAME EQ]]]].
      exists final,memory; split; [exact RUN|split; [eapply temp_agree_trans; eauto|exact EQ]].
    - exists source_exit,m'; split; [exact TARGET_SOURCE|split; [exact SOURCE_AGREE|apply memory_equivalent_refl]]. }
  destruct SELECTED as [final [memory [RUN [FRAME EQ]]]].
  pose proof (@shared_guarded_statement_execution (adapter_entry temps) (globalenv p) locals target m
    (generated_private_tree rule) flag candidate source final memory CHECK RUN) as EXEC.
  destruct (exec_stmt_steps (adapter_entry temps) p _ _ _ _ _ _ _ _ EXEC f k) as [next [STEPS EXIT]].
  inversion EXIT; subst next; exists final,memory; auto.
Qed.
Print Assumptions encoded_private_rule_sound.
