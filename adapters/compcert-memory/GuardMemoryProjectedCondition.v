From Stdlib Require Import List Bool.
From compcert.common Require Import AST Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import AbstractGuard SemanticFacts ClightGuard ClightCondition
  ClightPrivateRule ClightPrivateRegion ClightTempFrame ClightProjectedExecution
  ClightSharedRegion ClightTempFootprint CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemorySequentialCondition.
Import PrivateRegion.
Set Implicit Arguments.

Definition memory_projected_check_execution fe s live code accepted after :=
  exec_stmt fe (entry_ge s) (entry_env s) (entry_temps s) (entry_memory s) code E0
    after (entry_memory s) (memory_check_outcome accepted) /\
  temp_agree live (entry_temps s) after.

Lemma memory_projected_check_sequence fe s live first second accepted rest middle final :
  memory_projected_check_execution fe s live first accepted middle ->
  (accepted = true -> memory_projected_check_execution fe
    (Entry (entry_ge s) (entry_env s) middle (entry_memory s)) live second rest final) ->
  memory_projected_check_execution fe s live (Ssequence first second) (accepted && rest)
    (if accepted then final else middle).
Proof.
  intros [FIRST FRAME] SECOND; destruct s; destruct accepted; cbn in *.
  - destruct (SECOND eq_refl) as [RUN NEXT_FRAME]; split.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); eassumption.
    + eapply temp_agree_trans; eassumption.
  - split; [eapply exec_Sseq_2; [exact FIRST|discriminate]|exact FRAME].
Qed.

Lemma memory_projected_check_from_exact fe s live code accepted :
  memory_check_statement_execution fe s code accepted ->
  memory_projected_check_execution fe s live code accepted (entry_temps s).
Proof. intro RUN; split; [exact RUN|apply temp_agree_refl]. Qed.

Theorem memory_sequential_guarded_projected_execution fe ge locals temps memory
  checked check accepted candidate source after final :
  exec_stmt fe ge locals temps memory check E0 checked memory (memory_check_outcome accepted) ->
  exec_stmt fe ge locals checked memory (if accepted then candidate else source) E0 after final Out_normal ->
  exec_stmt fe ge locals temps memory (memory_sequential_guarded_statement check candidate source) E0 after final Out_normal.
Proof.
  intros CHECK RUN; unfold memory_sequential_guarded_statement; destruct accepted; cbn [memory_check_outcome] in CHECK.
  - eapply exec_Sloop_stop2 with (t1 := E0) (t2 := E0) (out1 := Out_continue) (out2 := Out_break).
    + eapply exec_Sseq_2; [|discriminate].
      change Out_continue with (outcome_switch Out_continue); apply singleton_switch_execution.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact CHECK|].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact RUN|constructor].
    + constructor.
    + constructor.
    + constructor.
  - eapply exec_Sloop_stop2 with (t1 := E0) (t2 := E0) (out1 := Out_normal) (out2 := Out_break).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := checked) (m1 := memory); [|exact RUN].
      change Out_normal with (outcome_switch Out_break); apply singleton_switch_execution.
      eapply exec_Sseq_2; [exact CHECK|discriminate].
    + constructor.
    + constructor.
    + constructor.
Qed.

(** A private check is executable code; its presumption is a semantic property.
    A language instance proves the property sufficient for its candidate and
    derives the check domain from successful source execution. *)
Record memory_projected_private_rule (live : list ident) (source candidate : statement) := MemoryProjectedPrivateRule {
  projected_rule_writes : list ident;
  projected_rule_source_writes : writes_only projected_rule_writes source;
  projected_rule_domain : clight_entry -> Prop;
  projected_rule_presumption : clight_entry -> Prop;
  projected_rule_entry : forall temps p locals le memory after final,
    exec_stmt (adapter_entry temps) (globalenv p) locals le memory source E0 after final Out_normal ->
    projected_rule_domain (Entry (globalenv p) locals le memory);
  projected_rule_local : forall temps p locals le memory after final,
    statement_scope live source ->
    exec_stmt (adapter_entry temps) (globalenv p) locals le memory source E0 after final Out_normal ->
    projected_rule_presumption (Entry (globalenv p) locals le memory) ->
    exists target result,
      exec_stmt (adapter_entry temps) (globalenv p) locals le memory candidate E0 target result Out_normal /\
      temp_agree live after target /\ memory_equivalent final result
}.

Theorem memory_projected_private_rule_sound live source candidate
  (rule : memory_projected_private_rule live source candidate) check :
  (forall fe s, projected_rule_domain rule s -> exists accepted checked,
    memory_projected_check_execution fe s live check accepted checked /\
    (accepted = true -> projected_rule_presumption rule (Entry (entry_ge s) (entry_env s) checked (entry_memory s)))) ->
  projected_region_contract live source (memory_sequential_guarded_statement check candidate source).
Proof.
  intros ENCODE temps p locals le target memory after final SCOPE AGREE SOURCE fn continuation.
  destruct (@structured_execution_temp_transport (adapter_entry temps) (globalenv p) locals le memory source E0 after final
    Out_normal SOURCE live target (projected_rule_writes rule) (projected_rule_source_writes rule) SCOPE AGREE)
    as [source_exit [TARGET_SOURCE SOURCE_AGREE]].
  assert (DOMAIN : projected_rule_domain rule (Entry (globalenv p) locals target memory)) by (eapply projected_rule_entry; eauto).
  destruct (ENCODE (adapter_entry temps) (Entry (globalenv p) locals target memory) DOMAIN)
    as [accepted [checked [[CHECK CHECK_FRAME] PROPERTY]]].
  assert (ENTRY_AGREE : temp_agree live le checked) by (eapply temp_agree_trans; eauto).
  destruct (@structured_execution_temp_transport (adapter_entry temps) (globalenv p) locals le memory source E0 after final
    Out_normal SOURCE live checked (projected_rule_writes rule) (projected_rule_source_writes rule) SCOPE ENTRY_AGREE)
    as [checked_source_exit [CHECKED_SOURCE EXIT_AGREE]].
  assert (SELECTED : exists next result,
    exec_stmt (adapter_entry temps) (globalenv p) locals checked memory (if accepted then candidate else source) E0 next result Out_normal /\
    temp_agree live after next /\ memory_equivalent final result).
  { destruct accepted eqn:ACCEPT.
    - destruct (projected_rule_local rule SCOPE CHECKED_SOURCE (PROPERTY eq_refl))
        as [next [result [RUN [FRAME EQUAL]]]].
      exists next,result; split; [exact RUN|split; [eapply temp_agree_trans; eauto|exact EQUAL]].
    - exists checked_source_exit,final; split; [exact CHECKED_SOURCE|split; [exact EXIT_AGREE|apply memory_equivalent_refl]]. }
  destruct SELECTED as [next [result [RUN [FRAME EQUAL]]]].
  pose proof (@memory_sequential_guarded_projected_execution (adapter_entry temps) (globalenv p) locals target memory
    checked check accepted candidate source next result CHECK RUN) as EXEC.
  destruct (exec_stmt_steps (adapter_entry temps) p _ _ _ _ _ _ _ _ EXEC fn continuation) as [finish [STEPS EXIT]].
  inversion EXIT; subst finish; exists next,result; auto.
Qed.
Theorem memory_private_rule_projected_check_sound live source candidate
  (rule : encoded_private_rule live source candidate) check :
  (forall fe s, private_rule_domain rule s -> exists accepted checked,
    memory_projected_check_execution fe s live check accepted checked /\
    (accepted = true -> formula_property (atom_property (private_rule_dimension rule))
      (private_rule_formula rule) (Entry (entry_ge s) (entry_env s) checked (entry_memory s)))) ->
  projected_region_contract live source (memory_sequential_guarded_statement check candidate source).
Proof.
  intro ENCODE.
  eapply memory_projected_private_rule_sound with
    (rule := @MemoryProjectedPrivateRule live source candidate
      (private_rule_writes rule) (private_rule_source_writes rule)
      (private_rule_domain rule)
      (formula_property (atom_property (private_rule_dimension rule)) (private_rule_formula rule))
      (private_rule_entry rule) (private_rule_local rule)).
  exact ENCODE.
Qed.
Print Assumptions memory_projected_private_rule_sound.
Print Assumptions memory_private_rule_projected_check_sound.
