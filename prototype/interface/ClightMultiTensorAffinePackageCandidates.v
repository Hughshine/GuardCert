From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightNoWrap ClightTempFootprint.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryScalarLoops
  GuardMemoryScalarChecker GuardMemoryArrayBackend GuardMemoryRecursiveSource GuardMemoryRecursiveDomain
  GuardMemoryRecursiveRestore GuardMemoryDynamicTensorBackend GuardMemoryMultiTensorSequence
  GuardMemoryMultiTensorSourceCapabilities GuardMemoryMultiTensorSourceRegion GuardMemoryMultiTensorAffineScan
  GuardMemoryMultiTensorAffineFootprint GuardMemoryFiniteFootprint GuardMemoryFootprintRestriction GuardMemoryMultiTensorBackend.
From GuardInterface Require Import ClightMultiTensorDataPackage ClightMultiTensorPackageExecution
  ClightTensorBackendGuard
  ClightMultiTensorCandidates ClightMultiTensorSourceCandidates ClightMultiTensorAffinePackageScan
  ClightMultiTensorAffineScanExit.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The existing mapped/tiling checker consumes proposed Loop code and domain
    witnesses. Names, source dimensions and instructions come from the package. *)
Definition check_multi_tensor_affine_package_candidate source (package : multi_tensor_region_package source)
    live pool proposal :=
  check_multi_tensor_generated (length (memory_nest_iterators (mtr_nest package)))
    (mtr_cap (mtr_description package)) (length (mtr_scalars (mtr_description package)))
    (map mt_instruction (mtr_items package)) (mtr_dimensions (mtr_description package))
    (multi_tensor_body_pointers (mtr_items package))
    (memory_nest_bounds (mtr_nest package)++mtr_scalars (mtr_description package)) live pool proposal.

Lemma multi_tensor_affine_package_ports_public source (package : multi_tensor_region_package source) live :
  incl (statement_temps source++live) (multi_tensor_affine_package_ports package live).
Proof.
  intros id MEMBER; unfold multi_tensor_affine_package_ports,multi_tensor_affine_scan_public;
    repeat rewrite in_app_iff in *; tauto.
Qed.

Theorem multi_tensor_affine_package_candidate_at_exit source (package : multi_tensor_region_package source)
    live pool proposal code fe ge locals original checked memory source_after final :
  exec_stmt fe ge locals original memory source E0 source_after final Out_normal ->
  decision_run (Entry ge locals original memory) (multi_tensor_package_setup_guard package) true ->
  temp_agree (multi_tensor_affine_package_ports package live) original checked ->
  (exists sizes,
    tensor_observe_dimensions (mtr_dimensions (mtr_description package)) original = Some sizes /\
    locations_nonalias (memory_restrict_locations (memory_footprint_allowed
      (multi_tensor_affine_source_footprint
        (map Z.of_nat (memory_recursive_counts (memory_nest_bounds (mtr_nest package)) original))
        (memory_recursive_parameters (mtr_scalars (mtr_description package)) original)
        (map mt_instruction (mtr_items package)))) (multi_tensor_locations original sizes))) ->
  mayReturn (check_multi_tensor_affine_package_candidate package live pool proposal) (Some code) ->
  exists restored,
    exec_stmt fe ge locals checked memory (Ssequence code (memory_recursive_restore (mtr_nest package)))
      E0 restored final Out_normal /\ temp_agree live source_after restored.
Proof.
  intros SOURCE SETUP FRAME [licensed_sizes [LICENSED_OBSERVE SEPARATION]] CHECK.
  set (counts := memory_recursive_counts (memory_nest_bounds (mtr_nest package)) original).
  set (values := memory_recursive_parameters (mtr_scalars (mtr_description package)) original).
  destruct (@multi_tensor_package_setup_accept source package fe ge locals original memory source_after final SOURCE SETUP)
    as [sizes (LENGTH & COUNTS & BOUNDS & INITIAL & SCALARS & SIGNED & OBSERVE & GUARD & BOX & WITHIN)].
  rewrite OBSERVE in LICENSED_OBSERVE; inversion LICENSED_OBSERVE; subst licensed_sizes.
  destruct (@multi_tensor_package_source_at_exit source package live fe ge locals original checked memory source_after final
    ltac:(eapply temp_agree_weaken; [apply multi_tensor_affine_package_ports_public|exact FRAME]) SOURCE)
    as [checked_after [CHECKED_SOURCE EXIT_FRAME]].
  destruct (@multi_tensor_affine_package_setup_at_exit source package live (map Z.of_nat counts) values sizes
    ge locals original checked memory FRAME BOUNDS INITIAL SCALARS OBSERVE GUARD)
    as (CHECKED_BOUNDS & CHECKED_INITIAL & CHECKED_SCALARS & CHECKED_OBSERVE & CHECKED_GUARD).
  assert (CHECKED_SEPARATION : multi_tensor_separated_source (length counts) (length values)
    (map mt_instruction (mtr_items package)) (map Z.of_nat counts++values) checked sizes).
  { unfold multi_tensor_separated_source,multi_tensor_source_footprint.
    pose proof (@multi_tensor_affine_separation_at_exit (map Z.of_nat counts) values
      (map mt_instruction (mtr_items package)) sizes original checked
      ltac:(eapply temp_agree_weaken; [|exact FRAME]; intros id IN;
        unfold multi_tensor_affine_package_ports,multi_tensor_affine_scan_public;
          repeat rewrite in_app_iff; tauto) SEPARATION) as AFTER.
    unfold multi_tensor_affine_source_footprint in AFTER; rewrite length_map in AFTER; exact AFTER. }
  assert (VALUE_LENGTH : length values = length (mtr_scalars (mtr_description package))) by
    (symmetry; apply (Forall2_length SCALARS)).
  unfold check_multi_tensor_affine_package_candidate in CHECK; rewrite <-LENGTH,<-VALUE_LENGTH in CHECK.
  destruct (@multi_tensor_original_generated_restored
    (mtr_dimensions (mtr_description package)) (mtr_nest package) (mtr_scalars (mtr_description package))
    (multi_tensor_body_pointers (mtr_items package)) (mtr_items package) fe ge locals counts values sizes
    checked checked_after memory final (mtr_cap (mtr_description package)) live pool
    (mtr_body package) (mtr_shapes package) (mtr_fresh package) (mtr_unique package) (mtr_protected package)
    LENGTH COUNTS CHECKED_BOUNDS CHECKED_INITIAL CHECKED_SCALARS SIGNED
    (multi_tensor_body_pointers_check (mtr_items package)) CHECKED_OBSERVE CHECKED_GUARD BOX WITHIN CHECKED_SEPARATION
    ltac:(eapply multi_tensor_region_source_execution; exact CHECKED_SOURCE) proposal code CHECK)
    as [restored [RUN PUBLIC]].
  exists restored; split; [exact RUN|eapply temp_agree_trans; eassumption].
Qed.

Print Assumptions multi_tensor_affine_package_ports_public.
Print Assumptions multi_tensor_affine_package_candidate_at_exit.
