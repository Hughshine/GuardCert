From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Guard Require Import ClightCondition ClightCountedLoop ClightNoWrap ClightTempFrame ClightTempFootprint ClightProjectedExecution
  ClightGuard ClightPrivateRegion CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemoryArrayBackend GuardMemoryRecursiveSource GuardMemoryRecursiveDomain GuardMemoryMultiTensorSequence
  GuardMemoryMultiTensorSourceCapabilities GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorBackend.
From GuardInterface Require Import ClightTensorSourceGuard ClightTensorCompleteGuard ClightTensorBoxGuard
  ClightMultiTensorSourceGuard ClightMultiTensorCompleteGuard ClightMultiTensorExample ClightMultiTensorSourceExample
  ClightMultiTensorPermissionExample ClightMultiTensorCandidates ClightMultiTensorPairScanExample
  ClightMultiTensorPairScanExit ClightMultiTensorPairScanCandidates ClightMultiTensorPublicScan ClightMultiTensorPublicCandidates
  ClightMultiTensorCompleteCandidates ClightMultiTensorCompleteExample ClightTensorRegionPackage.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem multi_tensor_demo_public_full_versioned_execution fe ge locals temps memory source_after final
    cap profile tree live pool proposal code :
  signed_range cap ->
  compile_tensor_box_guard (tensor_coordinate_layout multi_tensor_demo_dimensions multi_tensor_nest_demo_nest
    [2%positive;5%positive]) profile (memory_nest_bounds multi_tensor_nest_demo_nest)
    [2%positive;5%positive] multi_tensor_demo_dimensions (multi_tensor_body_accesses multi_tensor_nest_demo_items) = Some tree ->
  (tensor_disjoint live multi_tensor_demo_pair_private = true) ->
  exec_stmt fe ge locals temps memory (memory_nest_source multi_tensor_nest_demo_nest) E0 source_after final Out_normal ->
  mayReturn (check_multi_tensor_generated 3 cap 2 multi_tensor_nest_demo_instructions
    multi_tensor_demo_dimensions multi_tensor_demo_pointers multi_tensor_demo_layout live pool proposal) (Some code) ->
  exists after,
    exec_stmt fe ge locals temps memory (multi_tensor_demo_full_versioned cap profile tree code) E0 after final Out_normal /\
    temp_agree live source_after after.
Proof.
  intros CAP COMPILE FRESH SOURCE CHECK.
  pose (entry := Entry ge locals temps memory).
  assert (DEFINED : tensor_original_defined multi_tensor_nest_demo_nest fe entry) by (exists source_after,final; exact SOURCE).
  set (accepted := tensor_complete_flag multi_tensor_demo_dimensions multi_tensor_nest_demo_nest [2%positive;5%positive]
    cap profile (multi_tensor_body_accesses multi_tensor_nest_demo_items) entry).
  assert (RUN : decision_run entry (tensor_complete_tree multi_tensor_demo_dimensions multi_tensor_nest_demo_nest
    [2%positive;5%positive] cap profile tree) accepted).
  { apply (@multi_tensor_complete_guard_exact multi_tensor_demo_dimensions multi_tensor_nest_demo_nest
      [2%positive;5%positive] multi_tensor_nest_demo_items fe cap CAP multi_tensor_nest_demo_body_checked
      multi_tensor_demo_guard_nonempty multi_tensor_nest_demo_shapes multi_tensor_nest_demo_fresh
      multi_tensor_demo_guard_protected multi_tensor_demo_used_scalar_check multi_tensor_demo_guard_dimension_reads
      profile tree COMPILE entry DEFINED); reflexivity. }
  assert (BRANCH : exists after,
    exec_stmt fe ge locals temps memory
      (if accepted then multi_tensor_demo_pair_versioned code else memory_nest_source multi_tensor_nest_demo_nest)
      E0 after final Out_normal /\ temp_agree live source_after after).
  { destruct accepted.
    - destruct (@multi_tensor_complete_source_setup multi_tensor_demo_dimensions multi_tensor_nest_demo_nest
        [2%positive;5%positive] multi_tensor_nest_demo_items fe cap CAP multi_tensor_nest_demo_body_checked
        multi_tensor_demo_guard_nonempty multi_tensor_nest_demo_shapes multi_tensor_nest_demo_fresh
        multi_tensor_demo_guard_protected multi_tensor_demo_used_scalar_check multi_tensor_demo_guard_dimension_reads
        profile tree COMPILE ge locals temps memory DEFINED RUN)
        as [sizes (LENGTH & COUNTS & BOUNDS & INITIAL & SCALARS & SIGNED & OBSERVE & GUARD & BOX & WITHIN)].
      change (length (memory_recursive_counts [1%positive;3%positive;4%positive] temps) = 3%nat) in LENGTH.
      eapply (@multi_tensor_demo_pair_public_versioned_execution fe ge locals
        (memory_recursive_counts [1%positive;3%positive;4%positive] temps)
        (memory_recursive_parameters [2%positive;5%positive] temps) sizes temps source_after memory final
        cap live pool proposal code LENGTH COUNTS BOUNDS INITIAL SCALARS SIGNED OBSERVE GUARD BOX WITHIN FRESH SOURCE).
      rewrite LENGTH; cbn [memory_recursive_parameters length map]; exact CHECK.
    - exists source_after; split; [exact SOURCE|apply temp_agree_refl]. }
  destruct BRANCH as [after [LEAF EXIT]]; exists after; split; [|exact EXIT].
  unfold multi_tensor_demo_full_versioned; eapply decision_fragment_run; [exact RUN|exact LEAF].
Qed.

(** Source users supply candidate data and resource options. The producer
    checks the static private/live boundary itself before wrapping the checked
    candidate in the complete setup and alias guard. *)
Definition check_multi_tensor_demo_public_full_versioned live pool proposal :=
  if tensor_disjoint live multi_tensor_demo_pair_private then
    check_multi_tensor_demo_full_versioned live pool proposal
  else pure None.

Theorem check_multi_tensor_demo_public_full_versioned_execution fe ge locals temps memory source_after final
    live pool proposal target :
  exec_stmt fe ge locals temps memory (memory_nest_source multi_tensor_nest_demo_nest)
    E0 source_after final Out_normal ->
  mayReturn (check_multi_tensor_demo_public_full_versioned live pool proposal) (Some target) ->
  exists after, exec_stmt fe ge locals temps memory target E0 after final Out_normal /\
    temp_agree live source_after after.
Proof.
  intros SOURCE RUN; unfold check_multi_tensor_demo_public_full_versioned in RUN.
  destruct (tensor_disjoint live multi_tensor_demo_pair_private) eqn:FRESH;
    [|apply mayReturn_pure in RUN; discriminate].
  unfold check_multi_tensor_demo_full_versioned in RUN.
  bind_imp_destruct RUN checked_option CHECK; apply mayReturn_pure in RUN.
  destruct checked_option as [code|]; [|discriminate]; inversion RUN; subst target.
  eapply multi_tensor_demo_public_full_versioned_execution;
    [unfold signed_range; vm_compute; intuition congruence|exact multi_tensor_demo_setup_compiled|
      exact FRESH|exact SOURCE|exact CHECK].
Qed.

(** The concrete host consumes a small-step region guarantee. Source progress,
    typed declarations, placement and target label checks remain separate host
    installation obligations, rather than optimizer-supplied simulations. *)
Theorem check_multi_tensor_demo_public_full_versioned_contract live pool proposal target :
  mayReturn (check_multi_tensor_demo_public_full_versioned live pool proposal) (Some target) ->
  PrivateRegion.projected_region_contract live (memory_nest_source multi_tensor_nest_demo_nest) target.
Proof.
  intros CHECK temps p locals le current memory after final SCOPE AGREE SOURCE fn continuation.
  destruct (@structured_execution_temp_transport (adapter_entry temps) (globalenv p) locals le memory
    (memory_nest_source multi_tensor_nest_demo_nest) E0 after final Out_normal SOURCE live current
    [6%positive;7%positive;8%positive] multi_tensor_demo_pair_source_writes SCOPE AGREE)
    as [middle [ORIGINAL PUBLIC]].
  destruct (@check_multi_tensor_demo_public_full_versioned_execution (adapter_entry temps) (globalenv p) locals
    current memory middle final live pool proposal target ORIGINAL CHECK) as [exit [RUN EXIT_PUBLIC]].
  destruct (exec_stmt_steps (adapter_entry temps) p _ _ _ _ _ _ _ _ RUN fn continuation)
    as [finish [STEPS EXIT]].
  inversion EXIT; subst finish; exists exit,final; split; [exact STEPS|split].
  - eapply temp_agree_trans; [exact PUBLIC|exact EXIT_PUBLIC].
  - apply memory_equivalent_refl.
Qed.

Theorem check_multi_tensor_demo_public_full_versioned_refuses_private_collision live pool proposal :
  tensor_disjoint live multi_tensor_demo_pair_private = false ->
  check_multi_tensor_demo_public_full_versioned live pool proposal = pure None.
Proof. intro FRESH; unfold check_multi_tensor_demo_public_full_versioned; rewrite FRESH; reflexivity. Qed.

Print Assumptions multi_tensor_demo_public_full_versioned_execution.
Print Assumptions check_multi_tensor_demo_public_full_versioned_execution.
Print Assumptions check_multi_tensor_demo_public_full_versioned_contract.
Print Assumptions check_multi_tensor_demo_public_full_versioned_refuses_private_collision.
