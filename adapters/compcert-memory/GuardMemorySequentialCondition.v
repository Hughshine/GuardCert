From Stdlib Require Import List Bool.
From compcert.common Require Import AST Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import AbstractGuard SemanticFacts ClightGuard ClightCondition ClightPureExpr
  ClightPrivateRule ClightPrivateRegion ClightTempFrame ClightProjectedExecution ClightSharedRegion
  ClightDecisionRule CompCertMemoryEquivalence.
Import PrivateRegion.
Set Implicit Arguments.

(** A check statement leaves the entry state unchanged and returns normal on
    acceptance, break on refusal. Sequential composition shares continuations
    instead of distributing them through a conditional tree. *)
Definition memory_check_outcome (accepted : bool) : outcome := if accepted then Out_normal else Out_break.
Definition memory_check_statement_execution fe s code accepted :=
  exec_stmt fe (entry_ge s) (entry_env s) (entry_temps s) (entry_memory s) code E0
    (entry_temps s) (entry_memory s) (memory_check_outcome accepted).
Lemma memory_decision_check_statement fe s tree accepted :
  decision_run s tree accepted ->
  memory_check_statement_execution fe s (tree_statement tree Sskip Sbreak) accepted.
Proof.
  destruct s; cbn; intro RUN; unfold memory_check_outcome.
  apply decision_fragment_run with (b := accepted); [exact RUN|destruct accepted; constructor].
Qed.
Lemma memory_sequence_check_statement fe s first second accepted rest :
  memory_check_statement_execution fe s first accepted ->
  (accepted = true -> memory_check_statement_execution fe s second rest) ->
  memory_check_statement_execution fe s (Ssequence first second) (accepted && rest).
Proof.
  intros FIRST SECOND; destruct s; destruct accepted; cbn in *.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact FIRST|apply SECOND; reflexivity].
  - eapply exec_Sseq_2; [exact FIRST|discriminate].
Qed.
Definition memory_sequential_guarded_statement check candidate source :=
  Sloop (Ssequence (singleton_switch (Ssequence check (Ssequence candidate Scontinue))) source) Sbreak.
Theorem memory_sequential_guarded_statement_execution fe ge locals temps memory check accepted candidate source after final :
  memory_check_statement_execution fe (Entry ge locals temps memory) check accepted ->
  exec_stmt fe ge locals temps memory (if accepted then candidate else source) E0 after final Out_normal ->
  exec_stmt fe ge locals temps memory (memory_sequential_guarded_statement check candidate source) E0 after final Out_normal.
Proof.
  intros CHECK RUN; unfold memory_sequential_guarded_statement; destruct accepted; cbn [memory_check_statement_execution memory_check_outcome] in CHECK.
  - eapply exec_Sloop_stop2 with (t1 := E0) (t2 := E0) (out1 := Out_continue) (out2 := Out_break).
    + eapply exec_Sseq_2; [|discriminate].
      change Out_continue with (outcome_switch Out_continue); apply singleton_switch_execution.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact CHECK|].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact RUN|constructor].
    + constructor.
    + constructor.
    + constructor.
  - eapply exec_Sloop_stop2 with (t1 := E0) (t2 := E0) (out1 := Out_normal) (out2 := Out_break).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := temps) (m1 := memory); [|exact RUN].
      change Out_normal with (outcome_switch Out_break); apply singleton_switch_execution.
      eapply exec_Sseq_2; [exact CHECK|discriminate].
    + constructor.
    + constructor.
    + constructor.
Qed.
Theorem memory_private_rule_sequential_sound live source candidate (rule : encoded_private_rule live source candidate) check :
  (forall fe s, private_rule_domain rule s -> memory_check_statement_execution fe s check
    (formula_accepts (decide_atom (private_rule_dimension rule)) (private_rule_formula rule) s)) ->
  projected_region_contract live source (memory_sequential_guarded_statement check candidate source).
Proof.
  intros ENCODE temps p locals le target memory after final SCOPE AGREE SOURCE fn continuation.
  destruct (@structured_execution_temp_transport (adapter_entry temps) (globalenv p) locals le memory source E0 after final
    Out_normal SOURCE live target (private_rule_writes rule) (private_rule_source_writes rule) SCOPE AGREE)
    as [source_exit [TARGET_SOURCE SOURCE_AGREE]].
  assert (DOMAIN : private_rule_domain rule (Entry (globalenv p) locals target memory)) by (eapply private_rule_entry; eauto).
  set (flag := formula_accepts (decide_atom (private_rule_dimension rule)) (private_rule_formula rule) (Entry (globalenv p) locals target memory)).
  assert (CHECK : memory_check_statement_execution (adapter_entry temps) (Entry (globalenv p) locals target memory) check flag)
    by (apply ENCODE; exact DOMAIN).
  assert (SELECTED : exists next result,
    exec_stmt (adapter_entry temps) (globalenv p) locals target memory (if flag then candidate else source) E0 next result Out_normal /\
    temp_agree live after next /\ memory_equivalent final result).
  { destruct flag eqn:ACCEPT.
    - assert (PROPERTY : formula_property (atom_property (private_rule_dimension rule)) (private_rule_formula rule)
        (Entry (globalenv p) locals target memory)).
      { eapply synthesized_decision_tree_property; [exact DOMAIN|].
        apply (proj2 (@synthesized_decision_tree_correct (private_rule_atoms rule) (private_rule_domain rule)
          (decide_atom (private_rule_dimension rule)) (private_rule_primitives rule) (private_rule_formula rule)
          (Entry (globalenv p) locals target memory) true DOMAIN)).
        unfold flag in ACCEPT; symmetry; exact ACCEPT. }
      destruct (private_rule_local rule SCOPE TARGET_SOURCE PROPERTY) as [next [result [RUN [FRAME EQUAL]]]].
      exists next,result; split; [exact RUN|split; [eapply temp_agree_trans; eauto|exact EQUAL]].
    - exists source_exit,final; split; [exact TARGET_SOURCE|split; [exact SOURCE_AGREE|apply memory_equivalent_refl]]. }
  destruct SELECTED as [next [result [RUN [FRAME EQUAL]]]].
  pose proof (@memory_sequential_guarded_statement_execution (adapter_entry temps) (globalenv p) locals target memory
    check flag candidate source next result CHECK RUN) as EXEC.
  destruct (exec_stmt_steps (adapter_entry temps) p _ _ _ _ _ _ _ _ EXEC fn continuation) as [finish [STEPS EXIT]].
  inversion EXIT; subst finish; exists next,result; auto.
Qed.
Print Assumptions memory_sequence_check_statement.
Print Assumptions memory_private_rule_sequential_sound.
