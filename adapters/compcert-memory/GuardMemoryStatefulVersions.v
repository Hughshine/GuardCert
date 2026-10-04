From Stdlib Require Import List Bool.
From compcert.common Require Import AST Events Memory.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightGuard ClightPrivateRegion ClightTempFrame ClightProjectedExecution
  ClightSharedRegion ClightTempFootprint CompCertMemoryEquivalence StatefulGuard.
From GuardMemory Require Import GuardMemoryProjectedCondition GuardMemorySequentialCondition
  GuardMemoryStatefulLanguage GuardMemoryStatefulEntry GuardMemoryStatefulRule.
From Guard Require Import StatefulGuardVersions.
Import PrivateRegion.
Set Implicit Arguments.

Definition memory_projected_verified_version live source candidate
  (rule : memory_projected_private_rule live source candidate) check
  (ENCODE : forall fe s, projected_rule_domain rule s -> exists accepted checked,
    memory_projected_check_execution fe s live check accepted checked /\
    (accepted = true -> projected_rule_presumption rule (Entry (entry_ge s) (entry_env s) checked (entry_memory s))))
  setup p (SCOPE : statement_scope live source) :
  stateful_verified_version (memory_stateful_entry_language (adapter_entry setup) (globalenv p) live) source.
Proof.
  refine {| version_domain := projected_rule_domain rule;
    version_presumption := projected_rule_presumption rule;
    version_frame := memory_stateful_public_frame live;
    version_encoding := @memory_stateful_entry_encoding (adapter_entry setup) (globalenv p) live
      (projected_rule_domain rule) (projected_rule_presumption rule) check (ENCODE (adapter_entry setup));
    version_candidate := candidate |}.
  - intros state observation [GE [after [final [RUN REST]]]].
    destruct state as [ge locals temps memory]; cbn in GE,RUN |- *; subst ge.
    eapply projected_rule_entry; exact RUN.
  - intros state checked observation [GE [ENV [MEM FRAME]]] [GLOBAL_RUN [after [final [RUN [PUBLIC MEMORY]]]]].
    destruct state as [ge locals temps memory],checked as [next_ge next_env next_temps next_memory].
    cbn in GE,ENV,MEM,FRAME,GLOBAL_RUN,RUN,PUBLIC,MEMORY |- *; subst next_ge next_env next_memory.
    split; [exact GLOBAL_RUN|].
    destruct (@structured_execution_temp_transport (adapter_entry setup) ge locals temps memory source E0 after final
      Out_normal RUN live next_temps (projected_rule_writes rule) (projected_rule_source_writes rule) SCOPE FRAME)
      as [next [EXEC AGREE]].
    exists next,final; split; [exact EXEC|split; [eapply temp_agree_trans; eassumption|exact MEMORY]].
  - intros checked observation PROPERTY [GLOBAL_RUN [after [final [RUN [PUBLIC MEMORY]]]]].
    destruct checked as [ge locals temps memory]; cbn in GLOBAL_RUN,RUN,PROPERTY,PUBLIC,MEMORY |- *; subst ge.
    destruct (projected_rule_local rule SCOPE RUN PROPERTY) as [next [result [EXEC [AGREE EQUAL]]]].
    split; [reflexivity|]; exists next,result; split; [exact EXEC|split].
    + eapply temp_agree_trans; eassumption.
    + eapply memory_equivalent_trans; eassumption.
Defined.
Print Assumptions memory_projected_verified_version.
