(** One factory proof consumes either prepared scan service.  Accepted facts
    suffice; equality with the preceding Boolean is not a common obligation. *)
From Stdlib Require Import List Bool.
From compcert.common Require Import AST Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightCondition ClightTempFrame ClightPrivatePool.
From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryRecursiveRestore GuardMemoryTiledCompiler.
From GuardInterface Require Import ClightSourceLicensedScan ClightMultiTensorScanService
  ClightCheckPlan ClightCheckPlanFrame ClightMultiTensorDataPackage
  ClightMultiTensorAffinePackageScan ClightMultiTensorAffinePackageCandidates
  ClightMultiTensorAffineScanExit ClightMultiTensorAffineFactory
  ClightMultiTensorPackageExecution ClightMultiTensorCompleteGuard
  ClightTensorCompleteGuard ClightReadonlyProbeMemo ClightSharedGuard
  ClightMultiTensorScanAllocation ClightMultiTensorMemoSetup ClightCanonicalMemoSetup.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

Definition scan_service_alias_versioned source (package : multi_tensor_region_package source)
    public (prepared : multi_tensor_prepared_scan package public) code :=
  let scan:=prepared_scan_condition prepared in
  Ssequence (licensed_scan_statement scan)
    (Sifthenelse (shared_guard_choice (licensed_scan_result scan))
      (Ssequence code (memory_recursive_restore (mtr_nest package))) source).

Theorem scan_service_alias_execution source (package : multi_tensor_region_package source)
    public (prepared : multi_tensor_prepared_scan package public)
    pool proposal code fe ge locals original memory source_after final :
  exec_stmt fe ge locals original memory source E0 source_after final Out_normal ->
  decision_run (Entry ge locals original memory) (multi_tensor_package_setup_guard package) true ->
  mayReturn (check_multi_tensor_affine_package_candidate package public pool proposal) (Some code) ->
  exists after,
    exec_stmt fe ge locals original memory (scan_service_alias_versioned prepared code)
      E0 after final Out_normal /\ temp_agree public source_after after.
Proof.
  intros SOURCE READY CHECK; unfold scan_service_alias_versioned.
  eapply licensed_scan_choice_execution with (original:=original) (source_after:=source_after)
    (post:=temp_agree public source_after);
    [exact SOURCE|exact READY|apply temp_agree_refl|].
  intros checked answer PUBLIC PORTS FACT; destruct answer.
  - eapply multi_tensor_affine_package_candidate_at_exit;
      [exact SOURCE|exact READY|exact PORTS|exact (FACT eq_refl)|exact CHECK].
  - exact (@multi_tensor_package_source_at_exit source package public fe ge locals
      original checked memory source_after final PUBLIC SOURCE).
Qed.

Definition scan_service_setup_flag source (package : multi_tensor_region_package source)
    public typed_pool (prepared : multi_tensor_prepared_scan package public) code :=
  let plan:=tree_check_plan (multi_tensor_memo_setup_guard package) in
  let yes:=scan_service_alias_versioned prepared code in
  find (fun flag=>check_plan_resources plan flag public yes source)
    (multi_tensor_integer_names typed_pool).
Definition scan_service_setup_statement source (package : multi_tensor_region_package source)
    public (prepared : multi_tensor_prepared_scan package public) code flag :=
  check_plan_guarded_statement (tree_check_plan (multi_tensor_memo_setup_guard package)) flag
    (scan_service_alias_versioned prepared code) source.

Theorem scan_service_setup_flag_sound source (package : multi_tensor_region_package source)
    public typed_pool (prepared : multi_tensor_prepared_scan package public) code flag :
  scan_service_setup_flag typed_pool prepared code=Some flag ->
  In (flag,type_int32s) typed_pool /\
  check_plan_resources (tree_check_plan (multi_tensor_memo_setup_guard package)) flag public
    (scan_service_alias_versioned prepared code) source=true.
Proof.
  unfold scan_service_setup_flag; intro FOUND; apply find_some in FOUND as [MEMBER CHECK].
  split; [apply multi_tensor_integer_names_member; exact MEMBER|exact CHECK].
Qed.

Theorem scan_service_setup_execution source (package : multi_tensor_region_package source)
    public typed_pool (prepared : multi_tensor_prepared_scan package public)
    code flag pool proposal fe ge locals original memory source_after final :
  scan_service_setup_flag typed_pool prepared code=Some flag ->
  mayReturn (check_multi_tensor_affine_package_candidate package public pool proposal) (Some code) ->
  exec_stmt fe ge locals original memory source E0 source_after final Out_normal ->
  exists after, exec_stmt fe ge locals original memory
    (scan_service_setup_statement prepared code flag) E0 after final Out_normal /\
    temp_agree public source_after after.
Proof.
  intros FLAG CHECK SOURCE.
  destruct (@scan_service_setup_flag_sound source package public typed_pool prepared code flag FLAG)
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
    (if accepted then scan_service_alias_versioned prepared code else source)
    E0 middle final Out_normal /\ temp_agree public source_after middle).
  { destruct accepted.
    - eapply scan_service_alias_execution; eassumption.
    - exists source_after; split; [exact SOURCE|apply temp_agree_refl]. }
  destruct BRANCH as [middle [RUN PUBLIC]].
  destruct (@check_plan_guarded_normal_execution fe ge locals original memory
    (tree_check_plan (multi_tensor_memo_setup_guard package)) flag public
    (scan_service_alias_versioned prepared code) source accepted middle final)
    as [after [TARGET EXIT]].
  - rewrite tree_check_plan_spec; exact MEMO_SETUP.
  - exact YES.
  - exact NO.
  - exact FRESH.
  - exact RUN.
  - exists after; split; [exact TARGET|eapply temp_agree_trans; eassumption].
Qed.

Definition check_scan_service_full (prepare : multi_tensor_scan_builder)
    source (package : multi_tensor_region_package source) public typed_pool proposal :=
  match @prepare source package public typed_pool with
  | Some prepared=>match private_counter_pairs (prepared_scan_candidate_pool prepared) with
    | Some pairs=>
      BIND candidate <- check_multi_tensor_affine_package_candidate package public pairs proposal -;
      pure (match candidate with
        | Some code=>match scan_service_setup_flag typed_pool prepared code with
          | Some flag=>Some (scan_service_setup_statement prepared code flag)
          | None=>None end
        | None=>None end)
    | None=>pure None end
  | None=>pure None end.

Theorem check_scan_service_full_execution prepare source (package : multi_tensor_region_package source)
    public typed_pool proposal target fe ge locals original memory source_after final :
  mayReturn (check_scan_service_full prepare package public typed_pool proposal) (Some target) ->
  exec_stmt fe ge locals original memory source E0 source_after final Out_normal ->
  exists after, exec_stmt fe ge locals original memory target E0 after final Out_normal /\
    temp_agree public source_after after.
Proof.
  unfold check_scan_service_full.
  destruct (@prepare source package public typed_pool) as [prepared|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (private_counter_pairs (prepared_scan_candidate_pool prepared)) as [pairs|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN candidate CHECK; apply mayReturn_pure in RUN.
  destruct candidate as [code|]; [|discriminate].
  destruct (scan_service_setup_flag typed_pool prepared code) as [flag|] eqn:FLAG;
    [|discriminate].
  inversion RUN; subst target; intro SOURCE; eapply scan_service_setup_execution; eassumption.
Qed.

Theorem check_scan_service_pair_exact source (package : multi_tensor_region_package source)
    public typed_pool proposal :
  check_scan_service_full pair_scan_builder package public typed_pool proposal =
    check_multi_tensor_memo_setup_full package public typed_pool proposal.
Proof.
  unfold check_scan_service_full,pair_scan_builder,check_multi_tensor_memo_setup_full.
  destruct (multi_tensor_affine_package_allocate package public typed_pool); reflexivity.
Qed.
Theorem check_scan_service_canonical_exact source (package : multi_tensor_region_package source)
    public typed_pool proposal :
  check_scan_service_full canonical_scan_builder package public typed_pool proposal =
    check_canonical_memo_setup_full package public typed_pool proposal.
Proof.
  unfold check_scan_service_full,canonical_scan_builder,check_canonical_memo_setup_full.
  destruct (ClightCanonicalPackageScan.canonical_package_allocate package public typed_pool); reflexivity.
Qed.

Print Assumptions scan_service_alias_execution.
Print Assumptions scan_service_setup_flag_sound.
Print Assumptions scan_service_setup_execution.
Print Assumptions check_scan_service_full_execution.
Print Assumptions check_scan_service_pair_exact.
Print Assumptions check_scan_service_canonical_exact.
