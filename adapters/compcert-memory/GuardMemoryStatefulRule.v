From Stdlib Require Import List Bool.
From compcert.common Require Import AST Events Memory.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightGuard ClightPrivateRegion ClightTempFrame ClightProjectedExecution
  ClightSharedRegion ClightTempFootprint CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemoryProjectedCondition GuardMemorySequentialCondition.
From Guard Require Import StatefulGuard.
From GuardMemory Require Import GuardMemoryStatefulLanguage GuardMemoryStatefulEntry.
Import PrivateRegion.
Set Implicit Arguments.

Theorem memory_projected_private_rule_stateful_execution live source candidate
  (rule : memory_projected_private_rule live source candidate) check :
  (forall fe s, projected_rule_domain rule s -> exists accepted checked,
    memory_projected_check_execution fe s live check accepted checked /\
    (accepted = true -> projected_rule_presumption rule (Entry (entry_ge s) (entry_env s) checked (entry_memory s)))) ->
  forall setup p s observed,
    statement_scope live source -> entry_ge s = globalenv p ->
    memory_stateful_command_run (adapter_entry setup) live source s observed ->
    memory_stateful_command_run (adapter_entry setup) live
      (memory_sequential_guarded_statement check candidate source) s observed.
Proof.
  intros ENCODE setup p s observed SCOPE GLOBAL SOURCE.
  set (language := memory_stateful_entry_language (adapter_entry setup) (globalenv p) live).
  assert (SOURCE_RUN : stateful_command_run language source s observed) by (split; assumption).
  pose proof (@stateful_guard_preservation clight_entry language
    (projected_rule_domain rule) (projected_rule_presumption rule) (memory_stateful_public_frame live) source candidate
    (@memory_stateful_entry_encoding (adapter_entry setup) (globalenv p) live
      (projected_rule_domain rule) (projected_rule_presumption rule) check (ENCODE (adapter_entry setup)))) as CORE.
  apply (proj2 (CORE ltac:(
    intros state observation [GE [after [final [RUN REST]]]];
    destruct state as [ge locals temps memory]; cbn in GE,RUN |- *; subst ge;
    eapply projected_rule_entry; exact RUN) ltac:(
    intros state checked observation [GE [ENV [MEM FRAME]]] [GLOBAL_RUN [after [final [RUN [PUBLIC MEMORY]]]]];
    destruct state as [ge locals temps memory],checked as [next_ge next_env next_temps next_memory];
    cbn in GE,ENV,MEM,FRAME,GLOBAL_RUN,RUN,PUBLIC,MEMORY |- *; subst next_ge next_env next_memory;
    split; [exact GLOBAL_RUN|];
    destruct (@structured_execution_temp_transport (adapter_entry setup) ge locals temps memory source E0 after final
      Out_normal RUN live next_temps (projected_rule_writes rule) (projected_rule_source_writes rule) SCOPE FRAME)
      as [next [EXEC AGREE]];
    exists next,final; split; [exact EXEC|split; [eapply temp_agree_trans; eassumption|exact MEMORY]]) ltac:(
    intros checked observation PROPERTY [GLOBAL_RUN [after [final [RUN [PUBLIC MEMORY]]]]];
    destruct checked as [ge locals temps memory]; cbn in GLOBAL_RUN,RUN,PROPERTY,PUBLIC,MEMORY |- *; subst ge;
    destruct (projected_rule_local rule SCOPE RUN PROPERTY) as [next [result [EXEC [AGREE EQUAL]]]];
    split; [reflexivity|]; exists next,result; split; [exact EXEC|split];
    [eapply temp_agree_trans; eassumption|eapply memory_equivalent_trans; eassumption])
    s observed SOURCE_RUN)).
Qed.

Theorem memory_projected_private_rule_stateful_sound live source candidate
  (rule : memory_projected_private_rule live source candidate) check :
  (forall fe s, projected_rule_domain rule s -> exists accepted checked,
    memory_projected_check_execution fe s live check accepted checked /\
    (accepted = true -> projected_rule_presumption rule (Entry (entry_ge s) (entry_env s) checked (entry_memory s)))) ->
  projected_region_contract live source (memory_sequential_guarded_statement check candidate source).
Proof.
  intros ENCODE setup p locals temps target memory after final SCOPE FRAME SOURCE fn continuation.
  destruct (@structured_execution_temp_transport (adapter_entry setup) (globalenv p) locals temps memory source E0 after final
    Out_normal SOURCE live target (projected_rule_writes rule) (projected_rule_source_writes rule) SCOPE FRAME)
    as [source_exit [TARGET_SOURCE SOURCE_AGREE]].
  assert (SOURCE_OBSERVATION : memory_stateful_command_run (adapter_entry setup) live source
    (Entry (globalenv p) locals target memory) (source_exit,final)).
  { exists source_exit,final; split; [exact TARGET_SOURCE|split; [apply temp_agree_refl|apply memory_equivalent_refl]]. }
  destruct (@memory_projected_private_rule_stateful_execution live source candidate rule check ENCODE setup p
    (Entry (globalenv p) locals target memory) (source_exit,final) SCOPE eq_refl SOURCE_OBSERVATION)
    as [next [result [EXEC [PUBLIC EQUAL]]]].
  destruct (exec_stmt_steps (adapter_entry setup) p _ _ _ _ _ _ _ _ EXEC fn continuation) as [finish [STEPS EXIT]].
  inversion EXIT; subst finish; exists next,result; split; [exact STEPS|split; [eapply temp_agree_trans; eassumption|exact EQUAL]].
Qed.
Print Assumptions memory_projected_private_rule_stateful_execution.
Print Assumptions memory_projected_private_rule_stateful_sound.
