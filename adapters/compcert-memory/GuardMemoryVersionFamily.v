From Stdlib Require Import List Bool.
From compcert.common Require Import AST Events Memory.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightGuard ClightPrivateRegion ClightTempFrame ClightProjectedExecution
  ClightSharedRegion ClightTempFootprint CompCertMemoryEquivalence StatefulGuard.
From GuardMemory Require Import GuardMemoryProjectedCondition GuardMemorySequentialCondition
  GuardMemoryStatefulLanguage GuardMemoryStatefulEntry GuardMemoryStatefulRule.
From Guard Require Import StatefulGuardVersions.
From GuardMemory Require Import GuardMemoryStatefulVersions.
Import ListNotations PrivateRegion.
Set Implicit Arguments.

Record memory_verified_version live source := MemoryVerifiedVersion {
  memory_version_candidate : statement;
  memory_version_rule : memory_projected_private_rule live source memory_version_candidate;
  memory_version_check : statement;
  memory_version_encoding : forall fe s, projected_rule_domain memory_version_rule s ->
    exists accepted checked,
      memory_projected_check_execution fe s live memory_version_check accepted checked /\
      (accepted = true -> projected_rule_presumption memory_version_rule
        (Entry (entry_ge s) (entry_env s) checked (entry_memory s)))
}.

Fixpoint memory_version_family_statement live source (versions : list (memory_verified_version live source)) : statement :=
  match versions with
  | [] => source
  | version::rest => memory_sequential_guarded_statement (memory_version_check version)
      (memory_version_candidate version) (memory_version_family_statement rest)
  end.

Definition memory_version_family_core live source (versions : list (memory_verified_version live source))
  setup p (SCOPE : statement_scope live source) :=
  map (fun version => @memory_projected_verified_version live source
    (memory_version_candidate version) (memory_version_rule version)
    (memory_version_check version) (memory_version_encoding version) setup p SCOPE) versions.

Lemma memory_version_family_statement_core live source (versions : list (memory_verified_version live source))
  setup p (SCOPE : statement_scope live source) :
  @stateful_versioned_command clight_entry
    (memory_stateful_entry_language (adapter_entry setup) (globalenv p) live) source
    (memory_version_family_core versions setup p SCOPE) = memory_version_family_statement versions.
Proof.
  induction versions as [|version rest IH]; [reflexivity|].
  change (memory_sequential_guarded_statement (memory_version_check version)
    (memory_version_candidate version) (@stateful_versioned_command clight_entry
      (memory_stateful_entry_language (adapter_entry setup) (globalenv p) live) source
      (memory_version_family_core rest setup p SCOPE)) =
    memory_sequential_guarded_statement (memory_version_check version)
      (memory_version_candidate version) (memory_version_family_statement rest)).
  rewrite IH; reflexivity.
Qed.

Theorem memory_version_family_sound live source writes
  (WRITES : writes_only writes source) (versions : list (memory_verified_version live source)) :
  projected_region_contract live source (memory_version_family_statement versions).
Proof.
  intros setup p locals temps target memory after final SCOPE FRAME SOURCE fn continuation.
  destruct (@structured_execution_temp_transport (adapter_entry setup) (globalenv p) locals temps memory source E0 after final
    Out_normal SOURCE live target writes WRITES SCOPE FRAME)
    as [source_exit [TARGET_SOURCE SOURCE_AGREE]].
  assert (SOURCE_OBSERVATION : stateful_command_run
    (memory_stateful_entry_language (adapter_entry setup) (globalenv p) live) source
    (Entry (globalenv p) locals target memory) (source_exit,final)).
  { split; [reflexivity|]; exists source_exit,final; split; [exact TARGET_SOURCE|split;
      [apply temp_agree_refl|apply memory_equivalent_refl]]. }
  pose proof (@stateful_versions_preservation clight_entry
    (memory_stateful_entry_language (adapter_entry setup) (globalenv p) live) source
    (memory_version_family_core versions setup p SCOPE)
    (Entry (globalenv p) locals target memory) (source_exit,final) SOURCE_OBSERVATION) as EXECUTION.
  rewrite memory_version_family_statement_core in EXECUTION.
  destruct EXECUTION as [_ [next [result [EXEC [PUBLIC EQUAL]]]]].
  destruct (exec_stmt_steps (adapter_entry setup) p _ _ _ _ _ _ _ _ EXEC fn continuation)
    as [finish [STEPS EXIT]].
  inversion EXIT; subst finish; exists next,result; split; [exact STEPS|split;
    [eapply temp_agree_trans; eassumption|exact EQUAL]].
Qed.
Print Assumptions memory_version_family_sound.

Definition memory_version_components := (statement * statement)%type.
Fixpoint memory_version_components_statement source (versions : list memory_version_components) :=
  match versions with
  | [] => source
  | (check,candidate)::rest => memory_sequential_guarded_statement check candidate
      (memory_version_components_statement source rest)
  end.
Definition memory_version_components_valid live source (components : memory_version_components) : Prop :=
  exists rule : memory_projected_private_rule live source (snd components),
    forall fe s, projected_rule_domain rule s -> exists accepted checked,
      memory_projected_check_execution fe s live (fst components) accepted checked /\
      (accepted = true -> projected_rule_presumption rule
        (Entry (entry_ge s) (entry_env s) checked (entry_memory s))).

Lemma memory_version_components_certified live source components :
  Forall (memory_version_components_valid live source) components ->
  exists versions : list (memory_verified_version live source),
    memory_version_components_statement source components = memory_version_family_statement versions.
Proof.
  intro VALID; induction VALID as [|[check candidate] rest HEAD TAIL IH].
  - exists []; reflexivity.
  - destruct HEAD as [rule ENCODE]; destruct IH as [versions SAME].
    exists ({| memory_version_candidate := candidate; memory_version_rule := rule;
      memory_version_check := check; memory_version_encoding := ENCODE |}::versions).
    cbn [memory_version_components_statement memory_version_family_statement]; rewrite SAME; reflexivity.
Qed.

Theorem memory_version_components_sound live source writes
  (WRITES : writes_only writes source) components :
  Forall (memory_version_components_valid live source) components ->
  projected_region_contract live source (memory_version_components_statement source components).
Proof.
  intro VALID; destruct (memory_version_components_certified VALID) as [versions SAME].
  rewrite SAME; apply memory_version_family_sound with (writes := writes); exact WRITES.
Qed.
Print Assumptions memory_version_components_sound.

Theorem memory_version_components_nonempty_sound live source components :
  components <> [] -> Forall (memory_version_components_valid live source) components ->
  projected_region_contract live source (memory_version_components_statement source components).
Proof.
  destruct components as [|first rest]; [contradiction|].
  intros _ VALID.
  pose proof (Forall_inv VALID) as HEAD; destruct HEAD as [rule ENCODE].
  eapply memory_version_components_sound with (writes := projected_rule_writes rule);
    [exact (projected_rule_source_writes rule)|exact VALID].
Qed.
Print Assumptions memory_version_components_nonempty_sound.
