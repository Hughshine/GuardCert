From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Guard Require Import ClightCondition ClightCountedLoop ClightNoWrap ClightTempFrame.
From GuardMemory Require Import GuardMemoryArrayBackend GuardMemoryRecursiveSource GuardMemoryRecursiveDomain GuardMemoryMultiTensorSequence
  GuardMemoryMultiTensorSourceCapabilities GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorBackend.
From GuardInterface Require Import ClightTensorSourceGuard ClightTensorCompleteGuard ClightTensorBoxGuard
  ClightMultiTensorSourceGuard ClightMultiTensorCompleteGuard ClightMultiTensorExample ClightMultiTensorSourceExample
  ClightMultiTensorPermissionExample ClightMultiTensorCandidates ClightMultiTensorPairScanExample
  ClightMultiTensorPairScanCandidates.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

Example multi_tensor_demo_guard_nonempty : multi_tensor_nest_demo_items <> [].
Proof. vm_compute; discriminate. Qed.
Example multi_tensor_demo_guard_protected : forall identifier,
  In identifier (memory_nest_iterators multi_tensor_nest_demo_nest) ->
  ~ In identifier (multi_tensor_body_pointers multi_tensor_nest_demo_items ++
    tensor_dimension_registers (tl multi_tensor_demo_dimensions) ++ [2%positive;5%positive]).
Proof. intros identifier MEMBER BAD; vm_compute in MEMBER,BAD; intuition congruence. Qed.
Example multi_tensor_demo_guard_dimension_reads : forall identifier,
  In identifier (tensor_dimension_registers multi_tensor_demo_dimensions) ->
  In identifier (memory_nest_bounds multi_tensor_nest_demo_nest) \/
  In identifier (tensor_dimension_registers (tl multi_tensor_demo_dimensions)).
Proof. intros identifier MEMBER; vm_compute in MEMBER; vm_compute; intuition congruence. Qed.

Definition multi_tensor_demo_full_versioned cap profile tree code :=
  tree_statement (tensor_complete_tree multi_tensor_demo_dimensions multi_tensor_nest_demo_nest
    [2%positive;5%positive] cap profile tree)
    (multi_tensor_demo_pair_versioned code) (memory_nest_source multi_tensor_nest_demo_nest).

Theorem multi_tensor_demo_full_versioned_execution fe ge locals temps memory source_after final
    cap profile tree live pool proposal code :
  signed_range cap ->
  compile_tensor_box_guard (tensor_coordinate_layout multi_tensor_demo_dimensions multi_tensor_nest_demo_nest
    [2%positive;5%positive]) profile (memory_nest_bounds multi_tensor_nest_demo_nest)
    [2%positive;5%positive] multi_tensor_demo_dimensions (multi_tensor_body_accesses multi_tensor_nest_demo_items) = Some tree ->
  (forall identifier, In identifier live -> In identifier multi_tensor_demo_pair_public) ->
  exec_stmt fe ge locals temps memory (memory_nest_source multi_tensor_nest_demo_nest) E0 source_after final Out_normal ->
  mayReturn (check_multi_tensor_generated 3 cap 2 multi_tensor_nest_demo_instructions
    multi_tensor_demo_dimensions multi_tensor_demo_pointers multi_tensor_demo_layout live pool proposal) (Some code) ->
  exists after,
    exec_stmt fe ge locals temps memory (multi_tensor_demo_full_versioned cap profile tree code) E0 after final Out_normal /\
    temp_agree live source_after after.
Proof.
  intros CAP COMPILE LIVE SOURCE CHECK.
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
      eapply (@multi_tensor_demo_pair_versioned_execution fe ge locals
        (memory_recursive_counts [1%positive;3%positive;4%positive] temps)
        (memory_recursive_parameters [2%positive;5%positive] temps) sizes temps source_after memory final
        cap live pool proposal code LENGTH COUNTS BOUNDS INITIAL SCALARS SIGNED OBSERVE GUARD BOX WITHIN LIVE SOURCE).
      rewrite LENGTH; cbn [memory_recursive_parameters length map]; exact CHECK.
    - exists source_after; split; [exact SOURCE|apply temp_agree_refl]. }
  destruct BRANCH as [after [LEAF EXIT]]; exists after; split; [|exact EXIT].
  unfold multi_tensor_demo_full_versioned; eapply decision_fragment_run; [exact RUN|exact LEAF].
Qed.

Print Assumptions multi_tensor_demo_guard_nonempty.
Print Assumptions multi_tensor_demo_guard_protected.
Print Assumptions multi_tensor_demo_guard_dimension_reads.
Print Assumptions multi_tensor_demo_full_versioned_execution.
