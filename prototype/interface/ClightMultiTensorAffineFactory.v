From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightGuard ClightGuardProof ClightPrivateRegion ClightProjectedExecution ClightMemorySteps
  ClightTempFrame ClightTempFootprint CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryInstr GuardMemoryRecursiveSource
  GuardMemoryMultiTensorSequence GuardMemoryTiledCompiler.
From GuardInterface Require Import ClightMultiTensorDataPackage ClightMultiTensorRegionFactory
  ClightMultiTensorScanAllocation ClightMultiTensorAffinePackageScan
  ClightMultiTensorAffinePackageCandidates ClightMultiTensorAffineVersioned
  ClightTensorGeneratedCandidates.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

(** The producer accepts data only. Scan registers are allocated before
    candidate counters, so the two pieces cannot reuse private registers. *)
Definition check_multi_tensor_affine_package_full source
    (package : multi_tensor_region_package source) live typed_pool proposal :=
  match multi_tensor_affine_package_allocate package live typed_pool with
  | Some allocation =>
    match private_counter_pairs (multi_tensor_scan_candidate_pool allocation) with
    | Some pairs =>
      BIND candidate <- check_multi_tensor_affine_package_candidate package live pairs proposal -;
      pure (match candidate with
        | Some code => Some (multi_tensor_affine_package_full_versioned package live allocation code)
        | None => None end)
    | None => pure None end
  | None => pure None end.

Theorem check_multi_tensor_affine_package_full_execution source
    (package : multi_tensor_region_package source) live typed_pool proposal target
    fe ge locals original memory source_after final :
  mayReturn (check_multi_tensor_affine_package_full package live typed_pool proposal) (Some target) ->
  exec_stmt fe ge locals original memory source E0 source_after final Out_normal ->
  exists after, exec_stmt fe ge locals original memory target E0 after final Out_normal /\
    temp_agree live source_after after.
Proof.
  unfold check_multi_tensor_affine_package_full.
  destruct (multi_tensor_affine_package_allocate package live typed_pool) as [allocation|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (private_counter_pairs (multi_tensor_scan_candidate_pool allocation)) as [pairs|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN candidate CHECK; apply mayReturn_pure in RUN.
  destruct candidate as [code|]; [|discriminate]; inversion RUN; subst target.
  intro SOURCE; eapply multi_tensor_affine_package_full_execution; eassumption.
Qed.

Theorem check_multi_tensor_affine_package_full_contract source
    (package : multi_tensor_region_package source) live typed_pool proposal target :
  mayReturn (check_multi_tensor_affine_package_full package live typed_pool proposal) (Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  intros CHECK temps p locals le current memory after final SCOPE AGREE SOURCE fn continuation.
  destruct (@structured_execution_temp_transport (adapter_entry temps) (globalenv p) locals le memory
    source E0 after final Out_normal SOURCE live current (memory_nest_iterators (mtr_nest package))
    (multi_tensor_region_source_writes package) SCOPE AGREE) as [middle [ORIGINAL PUBLIC]].
  destruct (@check_multi_tensor_affine_package_full_execution source package live typed_pool proposal target
    (adapter_entry temps) (globalenv p) locals current memory middle final CHECK ORIGINAL)
    as [exit [RUN EXIT_PUBLIC]].
  destruct (exec_stmt_steps (adapter_entry temps) p _ _ _ _ _ _ _ _ RUN fn continuation)
    as [finish [STEPS EXIT]].
  inversion EXIT; subst finish; exists exit,final; split; [exact STEPS|split].
  - eapply temp_agree_trans; [exact PUBLIC|exact EXIT_PUBLIC].
  - apply memory_equivalent_refl.
Qed.

Definition multi_tensor_affine_description_proposer := statement -> option multi_tensor_region_description.
Definition multi_tensor_affine_candidate_proposer := list L.instr -> option tensor_generated_candidate.
Definition check_multi_tensor_affine_region live typed_pool
    (describe : multi_tensor_affine_description_proposer)
    (propose : multi_tensor_affine_candidate_proposer) source :=
  match describe source with
  | Some description => match check_multi_tensor_region_source source description with
    | Some package => match propose (map mt_instruction (mtr_items package)) with
      | Some proposal => check_multi_tensor_affine_package_full package live typed_pool proposal
      | None => pure None end
    | None => pure None end
  | None => pure None end.

Theorem check_multi_tensor_affine_region_contract live typed_pool describe propose source target :
  mayReturn (check_multi_tensor_affine_region live typed_pool describe propose source) (Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  unfold check_multi_tensor_affine_region.
  destruct (describe source) as [description|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (check_multi_tensor_region_source source description) as [package|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (propose (map mt_instruction (mtr_items package))) as [proposal|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  apply check_multi_tensor_affine_package_full_contract.
Qed.

Fixpoint checked_multi_tensor_affine_regions live typed_pool describe propose sources :=
  match sources with
  | [] => pure []
  | source::rest =>
    BIND target <- check_multi_tensor_affine_region live typed_pool describe propose source -;
    BIND table <- checked_multi_tensor_affine_regions live typed_pool describe propose rest -;
    pure (match target with Some target => (source,target)::table | None => table end)
  end.
Theorem checked_multi_tensor_affine_regions_sound live typed_pool describe propose sources table :
  mayReturn (checked_multi_tensor_affine_regions live typed_pool describe propose sources) table ->
  Forall (fun pair => PrivateRegion.projected_region_contract live (fst pair) (snd pair)) table.
Proof.
  revert table; induction sources as [|source sources IH]; intros table RUN; cbn in RUN.
  - apply mayReturn_pure in RUN; subst; constructor.
  - bind_imp_destruct RUN target CHECK; bind_imp_destruct RUN rest REST; apply mayReturn_pure in RUN.
    destruct target; subst;
      [constructor; [eapply check_multi_tensor_affine_region_contract; exact CHECK|]|]; apply IH; exact REST.
Qed.

Print Assumptions check_multi_tensor_affine_package_full_execution.
Print Assumptions check_multi_tensor_affine_package_full_contract.
Print Assumptions check_multi_tensor_affine_region_contract.
Print Assumptions checked_multi_tensor_affine_regions_sound.
