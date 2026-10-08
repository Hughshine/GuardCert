From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightTempFrame ClightTempFootprint ClightProjectedExecution.
From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryPairScanWrites.
From GuardInterface Require Import ClightTensorRegionPackage ClightMultiTensorExample ClightMultiTensorSourceExample
  ClightMultiTensorPairScanExample ClightMultiTensorPairScanExit.
Import ListNotations.
Set Implicit Arguments.

(** Boundary observations may include unrelated caller temporaries. Joining
    these frames requires neither an equality of private state nor a fixed
    source-port list as the complete public interface. *)
Lemma clight_temp_agree_union first second original checked :
  temp_agree first original checked -> temp_agree second original checked ->
  temp_agree (first++second) original checked.
Proof.
  intros FIRST SECOND identifier MEMBER; apply in_app_or in MEMBER;
    destruct MEMBER; [apply FIRST|apply SECOND]; assumption.
Qed.

Definition multi_tensor_demo_pair_private :=
  multi_tensor_demo_pair_left++multi_tensor_demo_pair_right++[multi_tensor_demo_pair_flag].

Theorem multi_tensor_demo_pair_guard_writes :
  writes_only multi_tensor_demo_pair_private multi_tensor_demo_pair_guard.
Proof.
  unfold multi_tensor_demo_pair_guard; apply writes_sequence.
  - apply writes_set; vm_compute; intuition congruence.
  - exact (multi_tensor_pair_scan_writes multi_tensor_demo_dimensions multi_tensor_demo_pair_left
      multi_tensor_demo_pair_right [1%positive;3%positive;4%positive]
      multi_tensor_demo_pair_flag 9%positive 10%positive).
Qed.

Theorem multi_tensor_demo_pair_guard_public_frame fe ge locals original checked memory live :
  tensor_disjoint live multi_tensor_demo_pair_private = true ->
  exec_stmt fe ge locals original memory multi_tensor_demo_pair_guard E0 checked memory Out_normal ->
  temp_agree live original checked.
Proof.
  intros FRESH SCAN; eapply structured_temp_frame;
    [exact multi_tensor_demo_pair_guard_writes|apply tensor_disjoint_sound; exact FRESH|exact SCAN].
Qed.

(** Transport the actual original source to the produced guard exit while
    preserving every caller-requested observation, including unrelated temps. *)
Theorem multi_tensor_demo_pair_source_at_public_exit fe ge locals original checked memory after final live :
  temp_agree multi_tensor_demo_pair_public original checked ->
  temp_agree live original checked ->
  exec_stmt fe ge locals original memory (memory_nest_source multi_tensor_nest_demo_nest)
    E0 after final Out_normal ->
  exists source_after,
    exec_stmt fe ge locals checked memory (memory_nest_source multi_tensor_nest_demo_nest)
      E0 source_after final Out_normal /\ temp_agree live after source_after.
Proof.
  intros PUBLIC LIVE SOURCE.
  assert (SCOPE : statement_scope (multi_tensor_demo_pair_public++live)
      (memory_nest_source multi_tensor_nest_demo_nest)).
  { intros identifier MEMBER; apply in_or_app; left;
      exact (@multi_tensor_demo_pair_source_scope identifier MEMBER). }
  destruct (@structured_execution_temp_transport fe ge locals original memory
    (memory_nest_source multi_tensor_nest_demo_nest) E0 after final Out_normal SOURCE
    (multi_tensor_demo_pair_public++live) checked [6%positive;7%positive;8%positive]
    multi_tensor_demo_pair_source_writes SCOPE (clight_temp_agree_union PUBLIC LIVE))
    as [source_after [RUN FRAME]].
  exists source_after; split; [exact RUN|].
  eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER; apply in_or_app; auto.
Qed.

Example multi_tensor_demo_pair_extra_caller_is_fresh :
  tensor_disjoint (multi_tensor_demo_pair_public++[301%positive]) multi_tensor_demo_pair_private = true.
Proof. vm_compute; reflexivity. Qed.
Example multi_tensor_demo_pair_flag_collision_refused :
  tensor_disjoint [multi_tensor_demo_pair_flag] multi_tensor_demo_pair_private = false.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions clight_temp_agree_union.
Print Assumptions multi_tensor_demo_pair_guard_writes.
Print Assumptions multi_tensor_demo_pair_guard_public_frame.
Print Assumptions multi_tensor_demo_pair_source_at_public_exit.
Print Assumptions multi_tensor_demo_pair_extra_caller_is_fresh.
Print Assumptions multi_tensor_demo_pair_flag_collision_refused.
