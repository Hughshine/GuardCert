From Stdlib Require Import List Bool.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightTempFrame ClightTempFootprint.
From GuardMemory Require Import GuardMemoryPairScanWrites GuardMemoryMultiTensorPairScan.
From GuardInterface Require Import ClightTensorRegionPackage ClightMultiTensorScanAllocation.
Import ListNotations.
Set Implicit Arguments.

Definition multi_tensor_allocated_pair_guard source live pool rank
    (allocation : multi_tensor_scan_allocation source live pool rank) dimensions bounds first second :=
  Ssequence (Sset (mtas_flag allocation) (Econst_int Int.one type_int32s))
    (multi_tensor_pair_scan dimensions (mtas_left allocation) (mtas_right allocation) bounds
      (mtas_flag allocation) first second).

Theorem multi_tensor_allocated_pair_guard_writes source live pool rank
    (allocation : multi_tensor_scan_allocation source live pool rank) dimensions bounds first second :
  writes_only (multi_tensor_scan_private allocation)
    (multi_tensor_allocated_pair_guard allocation dimensions bounds first second).
Proof.
  unfold multi_tensor_allocated_pair_guard; apply writes_sequence.
  - apply writes_set; unfold multi_tensor_scan_private; repeat rewrite in_app_iff; cbn; tauto.
  - apply multi_tensor_pair_scan_writes.
Qed.

(** Actual emitted code preserves all source and caller observations. Its
    safety and accepting coverage still require the domain's source receipts. *)
Theorem multi_tensor_allocated_pair_guard_frame source live pool rank
    (allocation : multi_tensor_scan_allocation source live pool rank) dimensions bounds first second
    fe ge locals original memory trace checked final outcome :
  exec_stmt fe ge locals original memory (multi_tensor_allocated_pair_guard allocation dimensions bounds first second)
    trace checked final outcome -> temp_agree (statement_temps source++live) original checked.
Proof.
  intro RUN; eapply structured_temp_frame;
    [apply multi_tensor_allocated_pair_guard_writes|apply multi_tensor_scan_allocation_fresh|exact RUN].
Qed.

Print Assumptions multi_tensor_allocated_pair_guard_writes.
Print Assumptions multi_tensor_allocated_pair_guard_frame.
