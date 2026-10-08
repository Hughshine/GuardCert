(** Remove repeated readonly setup probes before shared lowering. The
    original setup result, alias/candidate proof and host remain reusable. *)
From Stdlib Require Import List Bool.
From compcert.common Require Import AST Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryTiledCompiler.
From Guard Require Import ClightCondition ClightTempFrame ClightPrivatePool.
From GuardInterface Require Import ClightCheckPlan ClightCheckPlanFrame
  ClightMultiTensorAffineFactory ClightMultiTensorAffineVersioned ClightMultiTensorDataPackage
  ClightMultiTensorScanAllocation ClightMultiTensorAffinePackageScan
  ClightMultiTensorAffinePackageCandidates ClightMultiTensorPackageExecution
  ClightTensorCompleteGuard ClightMultiTensorCompleteGuard ClightReadonlyProbeMemo.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

Definition multi_tensor_memo_setup_guard source (package : multi_tensor_region_package source) :=
  memo_readonly_tree [] (multi_tensor_package_setup_guard package).

Definition multi_tensor_memo_setup_flag source (package : multi_tensor_region_package source)
    live typed_pool (allocation : multi_tensor_scan_allocation source
      (multi_tensor_affine_package_ports package live) typed_pool
      (length (GuardMemoryRecursiveSource.memory_nest_iterators (mtr_nest package)))) code :=
  let plan:=tree_check_plan (multi_tensor_memo_setup_guard package) in
  let yes:=multi_tensor_affine_package_alias_versioned package live allocation code in
  find (fun flag=>check_plan_resources plan flag live yes source)
    (multi_tensor_integer_names typed_pool).

Definition multi_tensor_memo_setup_statement source (package : multi_tensor_region_package source)
    live typed_pool (allocation : multi_tensor_scan_allocation source
      (multi_tensor_affine_package_ports package live) typed_pool
      (length (GuardMemoryRecursiveSource.memory_nest_iterators (mtr_nest package)))) code flag :=
  check_plan_guarded_statement (tree_check_plan (multi_tensor_memo_setup_guard package)) flag
    (multi_tensor_affine_package_alias_versioned package live allocation code) source.

Theorem multi_tensor_memo_setup_flag_sound source (package : multi_tensor_region_package source)
    live typed_pool (allocation : multi_tensor_scan_allocation source
      (multi_tensor_affine_package_ports package live) typed_pool
      (length (GuardMemoryRecursiveSource.memory_nest_iterators (mtr_nest package)))) code flag :
  multi_tensor_memo_setup_flag package live allocation code=Some flag ->
  In (flag,type_int32s) typed_pool /\
  check_plan_resources (tree_check_plan (multi_tensor_memo_setup_guard package)) flag live
    (multi_tensor_affine_package_alias_versioned package live allocation code) source=true.
Proof.
  unfold multi_tensor_memo_setup_flag; intro FOUND; apply find_some in FOUND as [MEMBER CHECK].
  split; [apply multi_tensor_integer_names_member; exact MEMBER|exact CHECK].
Qed.

Theorem multi_tensor_memo_setup_execution source (package : multi_tensor_region_package source)
    live typed_pool (allocation : multi_tensor_scan_allocation source
      (multi_tensor_affine_package_ports package live) typed_pool
      (length (GuardMemoryRecursiveSource.memory_nest_iterators (mtr_nest package))))
    code flag pool proposal fe ge locals original memory source_after final :
  multi_tensor_memo_setup_flag package live allocation code=Some flag ->
  mayReturn (check_multi_tensor_affine_package_candidate package live pool proposal) (Some code) ->
  exec_stmt fe ge locals original memory source E0 source_after final Out_normal ->
  exists after, exec_stmt fe ge locals original memory
    (multi_tensor_memo_setup_statement package live allocation code flag)
    E0 after final Out_normal /\ temp_agree live source_after after.
Proof.
  intros FLAG CHECK SOURCE.
  destruct (@multi_tensor_memo_setup_flag_sound source package live typed_pool allocation code flag FLAG)
    as [TYPED RESOURCES].
  apply check_plan_resources_sound in RESOURCES as [YES [NO FRESH]].
  pose proof (@multi_tensor_package_setup_run source package fe ge locals original memory source_after final SOURCE) as SETUP.
  set (accepted:=tensor_complete_flag (mtr_dimensions (mtr_description package)) (mtr_nest package)
    (mtr_scalars (mtr_description package)) (mtr_cap (mtr_description package)) (mtr_profile (mtr_description package))
    (multi_tensor_body_accesses (mtr_items package)) (Entry ge locals original memory)) in *.
  assert (MEMO_SETUP : decision_run (Entry ge locals original memory)
    (multi_tensor_memo_setup_guard package) accepted).
  { unfold multi_tensor_memo_setup_guard; apply (proj2 (memo_readonly_empty_exact _ _ _)); exact SETUP. }
  assert (BRANCH : exists middle, exec_stmt fe ge locals original memory
    (if accepted then multi_tensor_affine_package_alias_versioned package live allocation code else source)
    E0 middle final Out_normal /\ temp_agree live source_after middle).
  { destruct accepted.
    - eapply multi_tensor_affine_package_alias_execution; eassumption.
    - exists source_after; split; [exact SOURCE|apply temp_agree_refl]. }
  destruct BRANCH as [middle [RUN PUBLIC]].
  destruct (@check_plan_guarded_normal_execution fe ge locals original memory
    (tree_check_plan (multi_tensor_memo_setup_guard package)) flag live
    (multi_tensor_affine_package_alias_versioned package live allocation code) source accepted middle final)
    as [after [TARGET EXIT]].
  - rewrite tree_check_plan_spec; exact MEMO_SETUP.
  - exact YES.
  - exact NO.
  - exact FRESH.
  - exact RUN.
  - exists after; split; [exact TARGET|eapply temp_agree_trans; eassumption].
Qed.

Definition check_multi_tensor_memo_setup_full source (package : multi_tensor_region_package source)
    live typed_pool proposal :=
  match multi_tensor_affine_package_allocate package live typed_pool with
  | Some allocation=>match private_counter_pairs (multi_tensor_scan_candidate_pool allocation) with
    | Some pairs=>
      BIND candidate <- check_multi_tensor_affine_package_candidate package live pairs proposal -;
      pure (match candidate with
        | Some code=>match multi_tensor_memo_setup_flag package live allocation code with
          | Some flag=>Some (multi_tensor_memo_setup_statement package live allocation code flag)
          | None=>None end
        | None=>None end)
    | None=>pure None end
  | None=>pure None end.

Theorem check_multi_tensor_memo_setup_full_execution source (package : multi_tensor_region_package source)
    live typed_pool proposal target fe ge locals original memory source_after final :
  mayReturn (check_multi_tensor_memo_setup_full package live typed_pool proposal) (Some target) ->
  exec_stmt fe ge locals original memory source E0 source_after final Out_normal ->
  exists after, exec_stmt fe ge locals original memory target E0 after final Out_normal /\
    temp_agree live source_after after.
Proof.
  unfold check_multi_tensor_memo_setup_full.
  destruct (multi_tensor_affine_package_allocate package live typed_pool) as [allocation|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (private_counter_pairs (multi_tensor_scan_candidate_pool allocation)) as [pairs|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN candidate CHECK; apply mayReturn_pure in RUN.
  destruct candidate as [code|]; [|discriminate].
  destruct (multi_tensor_memo_setup_flag package live allocation code) as [flag|] eqn:FLAG;
    [|discriminate].
  inversion RUN; subst target; intro SOURCE; eapply multi_tensor_memo_setup_execution; eassumption.
Qed.

Print Assumptions multi_tensor_memo_setup_flag_sound.
Print Assumptions multi_tensor_memo_setup_execution.
Print Assumptions check_multi_tensor_memo_setup_full_execution.
