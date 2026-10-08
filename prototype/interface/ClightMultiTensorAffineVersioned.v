From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightTempFootprint ClightNoWrap.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryScalarLoops
  GuardMemoryRecursiveSource GuardMemoryRecursiveDomain GuardMemoryRecursiveRestore
  GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorBackend GuardMemoryMultiTensorSequence
  GuardMemoryMultiTensorAffineFootprint GuardMemoryMultiTensorAffineScan GuardMemoryBooleanScan.
From GuardInterface Require Import ClightTensorRegionPackage ClightTensorBackendGuard ClightTensorVolumeGuard
  ClightTensorCompleteGuard ClightMultiTensorCompleteGuard ClightMultiTensorDataPackage
  ClightMultiTensorPackageExecution ClightMultiTensorScanAllocation ClightMultiTensorAffinePackageScan
  ClightMultiTensorAffineScanExit ClightMultiTensorAffinePackageCandidates ClightSharedGuard ClightStagedCheck.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma multi_tensor_positive_dimensions_signed sizes :
  Forall (fun size => 0 < size) sizes -> tensor_volume sizes <= Int.max_signed -> Forall signed_range sizes.
Proof.
  intro POSITIVE; induction POSITIVE as [|size sizes POSITIVE REST IH]; intro VOLUME; constructor.
  - cbn [tensor_volume] in VOLUME; pose proof (tensor_positive_volume REST);
      unfold signed_range; pose proof Int.min_signed_neg; nia.
  - apply IH; cbn [tensor_volume] in VOLUME; pose proof (tensor_positive_volume REST); nia.
Qed.
Lemma multi_tensor_dimension_view_observation dimensions sizes temps :
  tensor_dimension_view dimensions sizes temps -> Forall signed_range sizes ->
  tensor_observe_dimensions dimensions temps = Some sizes.
Proof.
  intro VIEW; induction VIEW as [|dimension size dimensions sizes WORD VIEW IH]; intro RANGES;
    [reflexivity|inversion RANGES; subst].
  specialize (IH ltac:(assumption)); destruct dimension; cbn [tensor_observe_dimensions tensor_dimension_value] in *.
  - rewrite IH,WORD; reflexivity.
  - rewrite WORD,IH,Int.signed_repr by assumption; reflexivity.
Qed.

Definition multi_tensor_affine_package_alias_versioned source (package : multi_tensor_region_package source)
    live typed_pool (allocation : multi_tensor_scan_allocation source
      (multi_tensor_affine_package_ports package live) typed_pool
      (length (memory_nest_iterators (mtr_nest package)))) code :=
  Ssequence (multi_tensor_affine_package_guard package live allocation)
    (Sifthenelse (shared_guard_choice (mtas_flag allocation))
      (Ssequence code (memory_recursive_restore (mtr_nest package))) source).
Definition multi_tensor_affine_package_full_versioned source (package : multi_tensor_region_package source)
    live typed_pool (allocation : multi_tensor_scan_allocation source
      (multi_tensor_affine_package_ports package live) typed_pool
      (length (memory_nest_iterators (mtr_nest package)))) code :=
  tree_statement (multi_tensor_package_setup_guard package)
    (multi_tensor_affine_package_alias_versioned package live allocation code) source.

Theorem multi_tensor_affine_package_alias_execution source (package : multi_tensor_region_package source)
    live typed_pool (allocation : multi_tensor_scan_allocation source
      (multi_tensor_affine_package_ports package live) typed_pool
      (length (memory_nest_iterators (mtr_nest package))))
    pool proposal code fe ge locals original memory source_after final :
  exec_stmt fe ge locals original memory source E0 source_after final Out_normal ->
  decision_run (Entry ge locals original memory) (multi_tensor_package_setup_guard package) true ->
  mayReturn (check_multi_tensor_affine_package_candidate package live pool proposal) (Some code) ->
  exists after,
    exec_stmt fe ge locals original memory (multi_tensor_affine_package_alias_versioned package live allocation code)
      E0 after final Out_normal /\ temp_agree live source_after after.
Proof.
  intros SOURCE SETUP CHECK.
  destruct (@multi_tensor_affine_package_source_scan source package live typed_pool allocation fe ge locals
    original original memory source_after final SOURCE SETUP ltac:(apply temp_agree_refl))
    as [sizes [checked (SCAN & PUBLIC & FRAME & LAYOUT & DIMENSIONS & MODEL & FLAG & SOUND)]].
  assert (OBSERVE : tensor_observe_dimensions (mtr_dimensions (mtr_description package)) original = Some sizes).
  { apply multi_tensor_dimension_view_observation; [exact DIMENSIONS|].
    destruct (@tensor_layout_flag_sound sizes LAYOUT) as [POSITIVE [VOLUME _]].
    apply multi_tensor_positive_dimensions_signed; assumption. }
  set (accepted := multi_tensor_affine_scan_check (GuardMemoryMultiTensorBackend.multi_tensor_locations original sizes)
    (multi_tensor_instruction_templates (map mt_instruction (mtr_items package)))
    (memory_recursive_parameters (mtr_scalars (mtr_description package)) original)
    (map Z.of_nat (memory_recursive_counts (memory_nest_bounds (mtr_nest package)) original))) in *.
  assert (BRANCH : exists after,
    exec_stmt fe ge locals checked memory
      (if accepted then Ssequence code (memory_recursive_restore (mtr_nest package)) else source)
      E0 after final Out_normal /\ temp_agree live source_after after).
  { destruct accepted.
    - eapply multi_tensor_affine_package_candidate_at_exit;
        [exact SOURCE|exact SETUP|exact FRAME| |exact CHECK].
      exists sizes; split; [exact OBSERVE|apply SOUND; exact FLAG].
    - exact (@multi_tensor_package_source_at_exit source package live fe ge locals
        original checked memory source_after final PUBLIC SOURCE). }
  destruct BRANCH as [after [RUN EXIT]]; exists after; split; [|exact EXIT].
  unfold multi_tensor_affine_package_alias_versioned; eapply check_result_gate_execution;
    [exact SCAN|exact FLAG|exact RUN].
Qed.

(** Both setup refusal and alias refusal execute the original source AST.
    Only an accepted source-licensed scan reaches checked candidate code. *)
Theorem multi_tensor_affine_package_full_execution source (package : multi_tensor_region_package source)
    live typed_pool (allocation : multi_tensor_scan_allocation source
      (multi_tensor_affine_package_ports package live) typed_pool
      (length (memory_nest_iterators (mtr_nest package))))
    pool proposal code fe ge locals original memory source_after final :
  exec_stmt fe ge locals original memory source E0 source_after final Out_normal ->
  mayReturn (check_multi_tensor_affine_package_candidate package live pool proposal) (Some code) ->
  exists after,
    exec_stmt fe ge locals original memory (multi_tensor_affine_package_full_versioned package live allocation code)
      E0 after final Out_normal /\ temp_agree live source_after after.
Proof.
  intros SOURCE CHECK.
  set (accepted := tensor_complete_flag (mtr_dimensions (mtr_description package)) (mtr_nest package)
    (mtr_scalars (mtr_description package)) (mtr_cap (mtr_description package)) (mtr_profile (mtr_description package))
    (multi_tensor_body_accesses (mtr_items package)) (Entry ge locals original memory)).
  pose proof (@multi_tensor_package_setup_run source package fe ge locals original memory source_after final SOURCE) as SETUP.
  change (decision_run (Entry ge locals original memory) (multi_tensor_package_setup_guard package) accepted) in SETUP.
  assert (BRANCH : exists after,
    exec_stmt fe ge locals original memory
      (if accepted then multi_tensor_affine_package_alias_versioned package live allocation code else source)
      E0 after final Out_normal /\ temp_agree live source_after after).
  { destruct accepted.
    - eapply multi_tensor_affine_package_alias_execution; eassumption.
    - exists source_after; split; [exact SOURCE|apply temp_agree_refl]. }
  destruct BRANCH as [after [RUN EXIT]]; exists after; split; [|exact EXIT].
  unfold multi_tensor_affine_package_full_versioned; eapply decision_fragment_run; [exact SETUP|exact RUN].
Qed.

Print Assumptions multi_tensor_positive_dimensions_signed.
Print Assumptions multi_tensor_dimension_view_observation.
Print Assumptions multi_tensor_affine_package_alias_execution.
Print Assumptions multi_tensor_affine_package_full_execution.
