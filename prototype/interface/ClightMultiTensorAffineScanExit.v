From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightCountedLoop ClightFrontendLoopProtocol
  ClightTempFrame ClightTempFootprint ClightProjectedExecution ClightStraightLine.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryFiniteFootprint
  GuardMemoryFootprintRestriction GuardMemoryRecursiveSource GuardMemoryDynamicTensorBackend
  GuardMemoryMultiTensorBackend GuardMemoryMultiTensorGuardExit GuardMemoryMultiTensorAffineFootprint.
From GuardInterface Require Import ClightAdministrative ClightLoopAdministrative ClightTensorBackendGuard
  ClightMultiTensorDataPackage ClightMultiTensorAffinePackageScan.
Import ListNotations.
Set Implicit Arguments.

Lemma multi_tensor_join_statement_temps first second :
  statement_temps (join_statements first second) = statement_temps first ++ statement_temps second.
Proof.
  destruct first; cbn [join_statements statement_temps]; try reflexivity;
    destruct second; cbn [statement_temps]; try reflexivity; rewrite app_nil_r; reflexivity.
Qed.
Lemma multi_tensor_trim_statement_temps source :
  statement_temps (trim_loop_skips source) = statement_temps source.
Proof.
  revert source; fix IH 1; intro source; destruct source; cbn [trim_loop_skips statement_temps]; try reflexivity.
  - rewrite multi_tensor_join_statement_temps,IH,IH; reflexivity.
  - rewrite IH,IH; reflexivity.
  - destruct source1; cbn [trim_loop_skips statement_temps]; try reflexivity; rewrite IH; reflexivity.
Qed.

Lemma multi_tensor_package_initial_at_exit source (package : multi_tensor_region_package source) original checked :
  temp_agree (statement_temps source) original checked ->
  memory_nest_initial (mtr_nest package) original -> memory_nest_initial (mtr_nest package) checked.
Proof.
  intros FRAME INITIAL; pose proof (mtr_source package) as SOURCE.
  destruct (mtr_nest package) as [body|iterator bound body child]; [exact I|].
  cbn [memory_nest_initial] in *; rewrite FRAME; [exact INITIAL|].
  rewrite <-multi_tensor_trim_statement_temps,SOURCE.
  cbn [memory_nest_source frontend_counted_loop counter_condition counter_increment statement_temps expression_temps].
  cbn; auto.
Qed.

Theorem multi_tensor_package_source_at_exit source (package : multi_tensor_region_package source)
    live fe ge locals original checked memory after final :
  temp_agree (statement_temps source++live) original checked ->
  exec_stmt fe ge locals original memory source E0 after final Out_normal ->
  exists checked_after,
    exec_stmt fe ge locals checked memory source E0 checked_after final Out_normal /\
    temp_agree live after checked_after.
Proof.
  intros FRAME SOURCE.
  destruct (@structured_execution_temp_transport fe ge locals original memory source E0 after final Out_normal
    SOURCE (statement_temps source++live) checked (memory_nest_iterators (mtr_nest package))
    (multi_tensor_region_source_writes package) ltac:(intros id IN; apply in_or_app; left; exact IN) FRAME)
    as [checked_after [RUN AFTER]].
  exists checked_after; split; [exact RUN|].
  eapply temp_agree_weaken; [|exact AFTER]; intros id IN; apply in_or_app; right; exact IN.
Qed.

Lemma multi_tensor_affine_source_footprint_pointers counts values instructions :
  Forall (fun cell => In (arr_id cell) (map (fun access : AccessFunction => fst access)
    (multi_tensor_instruction_templates instructions))) (multi_tensor_affine_source_footprint counts values instructions).
Proof.
  apply Forall_forall; intros cell MEMBER.
  apply multi_tensor_affine_source_footprint_member in MEMBER as [point [[array coordinates] [_ [ACCESS SAME]]]].
  subst cell; cbn [exact_cell arr_id]; apply in_map_iff; exists (array,coordinates); auto.
Qed.

Theorem multi_tensor_affine_separation_at_exit counts values instructions sizes original checked :
  temp_agree (map (fun access : AccessFunction => fst access) (multi_tensor_instruction_templates instructions))
    original checked ->
  locations_nonalias (memory_restrict_locations (memory_footprint_allowed
    (multi_tensor_affine_source_footprint counts values instructions)) (multi_tensor_locations original sizes)) ->
  locations_nonalias (memory_restrict_locations (memory_footprint_allowed
    (multi_tensor_affine_source_footprint counts values instructions)) (multi_tensor_locations checked sizes)).
Proof.
  intros FRAME SEPARATION; eapply multi_tensor_restricted_separation_at_exit;
    [exact FRAME|apply multi_tensor_affine_source_footprint_pointers|exact SEPARATION].
Qed.

(** Dynamic setup observations and the original iterator initializer are
    interpreted at the actual scan exit, not on hypothetical entry caches. *)
Theorem multi_tensor_affine_package_setup_at_exit source (package : multi_tensor_region_package source)
    live counts values sizes ge locals original checked memory :
  temp_agree (multi_tensor_affine_package_ports package live) original checked ->
  memory_nest_bindings (memory_nest_bounds (mtr_nest package)) counts original ->
  memory_nest_initial (mtr_nest package) original ->
  memory_nest_bindings (mtr_scalars (mtr_description package)) values original ->
  tensor_observe_dimensions (mtr_dimensions (mtr_description package)) original = Some sizes ->
  decision_run (Entry ge locals original memory) (tensor_backend_guard (mtr_dimensions (mtr_description package))) true ->
  memory_nest_bindings (memory_nest_bounds (mtr_nest package)) counts checked /\
  memory_nest_initial (mtr_nest package) checked /\
  memory_nest_bindings (mtr_scalars (mtr_description package)) values checked /\
  tensor_observe_dimensions (mtr_dimensions (mtr_description package)) checked = Some sizes /\
  decision_run (Entry ge locals checked memory) (tensor_backend_guard (mtr_dimensions (mtr_description package))) true.
Proof.
  intros FRAME BOUNDS INITIAL SCALARS OBSERVE GUARD.
  assert (DIMENSION_FRAME : temp_agree (tensor_dimension_registers (mtr_dimensions (mtr_description package))) original checked).
  { eapply temp_agree_weaken; [|exact FRAME]; intros id IN.
    unfold multi_tensor_affine_package_ports,GuardMemoryMultiTensorAffineScan.multi_tensor_affine_scan_public;
      repeat rewrite in_app_iff; tauto. }
  destruct (@tensor_backend_guard_at_framed_exit (mtr_dimensions (mtr_description package)) sizes
    (Entry ge locals original memory) checked DIMENSION_FRAME OBSERVE GUARD) as [AFTER_OBSERVE AFTER_GUARD].
  split.
  - eapply memory_nest_bindings_frame_from; [|exact FRAME|exact BOUNDS].
    intros id IN; unfold multi_tensor_affine_package_ports; apply in_or_app; left; exact IN.
  - split.
    + eapply multi_tensor_package_initial_at_exit; [|exact INITIAL].
      eapply temp_agree_weaken; [|exact FRAME]; intros id IN.
      unfold multi_tensor_affine_package_ports,GuardMemoryMultiTensorAffineScan.multi_tensor_affine_scan_public;
        repeat rewrite in_app_iff; tauto.
    + split.
      * eapply memory_nest_bindings_frame_from; [|exact FRAME|exact SCALARS].
        intros id IN; unfold multi_tensor_affine_package_ports,GuardMemoryMultiTensorAffineScan.multi_tensor_affine_scan_public;
          repeat rewrite in_app_iff; tauto.
      * split; assumption.
Qed.

Print Assumptions multi_tensor_join_statement_temps.
Print Assumptions multi_tensor_trim_statement_temps.
Print Assumptions multi_tensor_package_initial_at_exit.
Print Assumptions multi_tensor_package_source_at_exit.
Print Assumptions multi_tensor_affine_source_footprint_pointers.
Print Assumptions multi_tensor_affine_separation_at_exit.
Print Assumptions multi_tensor_affine_package_setup_at_exit.
