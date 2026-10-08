From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps.
From compcert.common Require Import Values Memory.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightPureExpr ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryFiniteFootprint GuardMemoryFootprintRestriction
  GuardMemoryDynamicTensorBackend GuardMemoryMultiTensorBackend GuardMemoryMultiTensorFrame.
From GuardInterface Require Import ClightTensorBackendGuard.
Import ListNotations.
Set Implicit Arguments.

Lemma tensor_observe_dimensions_frame sources before after :
  temp_agree (tensor_dimension_registers sources) before after ->
  tensor_observe_dimensions sources after = tensor_observe_dimensions sources before.
Proof.
  intro FRAME; induction sources as [|source rest IH]; [reflexivity|].
  destruct source; cbn [tensor_observe_dimensions tensor_dimension_registers] in *.
  - rewrite IH by exact FRAME; reflexivity.
  - rewrite FRAME by (cbn; auto); rewrite IH; [reflexivity|].
    eapply temp_agree_weaken; [|exact FRAME]; cbn; auto.
Qed.

Theorem tensor_backend_guard_at_framed_exit sources dimensions entry current :
  temp_agree (tensor_dimension_registers sources) (entry_temps entry) current ->
  tensor_observe_dimensions sources (entry_temps entry) = Some dimensions ->
  decision_run entry (tensor_backend_guard sources) true ->
  tensor_observe_dimensions sources current = Some dimensions /\
  decision_run (Entry (entry_ge entry) (entry_env entry) current (entry_memory entry))
    (tensor_backend_guard sources) true.
Proof.
  intros FRAME OBSERVE GUARD.
  assert (AFTER : tensor_observe_dimensions sources current = Some dimensions).
  { rewrite tensor_observe_dimensions_frame with (before:=entry_temps entry); assumption. }
  split; [exact AFTER|].
  pose proof (@pure_tree_determinate (tensor_backend_guard sources) (tensor_backend_guard_pure sources)
    entry true (ClightTensorVolumeGuard.tensor_volume_check GuardMemoryDynamicTensorLayout.tensor_volume_cap 1 dimensions)
    GUARD (@tensor_backend_guard_run entry sources dimensions OBSERVE)) as ACCEPT.
  pose proof (@tensor_backend_guard_run
    (Entry (entry_ge entry) (entry_env entry) current (entry_memory entry)) sources dimensions AFTER) as RUN.
  rewrite <- ACCEPT in RUN; exact RUN.
Qed.

(** Only source-footprint pointer bindings must agree. Unrelated entries in
    the raw locator may change during private cursor initialization. *)
Lemma multi_tensor_restricted_locations_frame pointers cells sizes original current :
  temp_agree pointers original current -> Forall (fun cell => In (arr_id cell) pointers) cells ->
  forall cell,
    memory_restrict_locations (memory_footprint_allowed cells) (multi_tensor_locations original sizes) cell =
    memory_restrict_locations (memory_footprint_allowed cells) (multi_tensor_locations current sizes) cell.
Proof.
  intros FRAME USED cell; unfold memory_restrict_locations.
  destruct (memory_footprint_allowed cells cell) eqn:ALLOWED; [|reflexivity].
  apply memory_footprint_allowed_exact in ALLOWED; rewrite Forall_forall in USED.
  apply multi_tensor_locations_pointer_frame with (pointers:=pointers); [exact FRAME|apply USED; exact ALLOWED].
Qed.

Theorem multi_tensor_restricted_separation_at_exit pointers cells sizes original current :
  temp_agree pointers original current -> Forall (fun cell => In (arr_id cell) pointers) cells ->
  locations_nonalias (memory_restrict_locations (memory_footprint_allowed cells) (multi_tensor_locations original sizes)) ->
  locations_nonalias (memory_restrict_locations (memory_footprint_allowed cells) (multi_tensor_locations current sizes)).
Proof.
  intros FRAME USED SEPARATED first second loc1 loc2 FIRST SECOND DIFFERENT.
  rewrite <- (@multi_tensor_restricted_locations_frame pointers cells sizes original current FRAME USED first) in FIRST.
  rewrite <- (@multi_tensor_restricted_locations_frame pointers cells sizes original current FRAME USED second) in SECOND.
  exact (SEPARATED first second loc1 loc2 FIRST SECOND DIFFERENT).
Qed.

Print Assumptions tensor_observe_dimensions_frame.
Print Assumptions tensor_backend_guard_at_framed_exit.
Print Assumptions multi_tensor_restricted_locations_frame.
Print Assumptions multi_tensor_restricted_separation_at_exit.
