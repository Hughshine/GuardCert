From Stdlib Require Import List Bool.
From compcert.common Require Import AST Events Memory.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightGuard ClightPrivateRegion ClightTempFrame
  CompCertMemoryEquivalence StatefulGuard StatefulGuardVersions.
From GuardMemory Require Import GuardMemoryProjectedCondition GuardMemorySequentialCondition
  GuardMemoryStatefulLanguage GuardMemoryStatefulEntry GuardMemoryStatefulVersions
  GuardMemoryVersionFamily.
Import ListNotations PrivateRegion.
Set Implicit Arguments.

Definition memory_verified_guarded_rule live source
  (version : memory_verified_version live source) (property : clight_entry -> Prop) :
  memory_projected_private_rule live source
    (memory_sequential_guarded_statement (memory_version_check version)
      (memory_version_candidate version) source).
Proof.
  refine {| projected_rule_writes := projected_rule_writes (memory_version_rule version);
    projected_rule_source_writes := projected_rule_source_writes (memory_version_rule version);
    projected_rule_domain := projected_rule_domain (memory_version_rule version);
    projected_rule_presumption := property;
    projected_rule_entry := projected_rule_entry (memory_version_rule version) |}.
  intros setup p locals temps memory after final SCOPE SOURCE _.
  set (language := memory_stateful_entry_language (adapter_entry setup) (globalenv p) live).
  assert (OBSERVED : stateful_command_run language source
    (Entry (globalenv p) locals temps memory) (after,final)).
  { split; [reflexivity|]; exists after,final; split; [exact SOURCE|split;
      [apply temp_agree_refl|apply memory_equivalent_refl]]. }
  set (core := @memory_projected_verified_version live source
    (memory_version_candidate version) (memory_version_rule version)
    (memory_version_check version) (memory_version_encoding version) setup p SCOPE).
  pose proof (@stateful_versions_preservation clight_entry language source [core]
    (Entry (globalenv p) locals temps memory) (after,final) OBSERVED) as PRESERVED.
  change (stateful_command_run language
    (memory_sequential_guarded_statement (memory_version_check version)
      (memory_version_candidate version) source)
    (Entry (globalenv p) locals temps memory) (after,final)) in PRESERVED.
  destruct PRESERVED as [_ [next [result [EXEC [PUBLIC EQUAL]]]]].
  exists next,result; auto.
Defined.

Definition memory_prefiltered_version live source
  (version : memory_verified_version live source) property check
  (ENCODE : forall fe s, projected_rule_domain (memory_version_rule version) s ->
    exists accepted checked,
      memory_projected_check_execution fe s live check accepted checked /\
      (accepted = true -> property
        (Entry (entry_ge s) (entry_env s) checked (entry_memory s)))) :
  memory_verified_version live source :=
  {| memory_version_candidate := memory_sequential_guarded_statement
       (memory_version_check version) (memory_version_candidate version) source;
     memory_version_rule := memory_verified_guarded_rule version property;
     memory_version_check := check; memory_version_encoding := ENCODE |}.

Print Assumptions memory_verified_guarded_rule.
Print Assumptions memory_prefiltered_version.
