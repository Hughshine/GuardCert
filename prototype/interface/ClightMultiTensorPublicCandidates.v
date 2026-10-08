From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightNoWrap.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryArrayBackend GuardMemoryScalarChecker GuardMemoryScalarLoops
  GuardMemoryRecursiveSource GuardMemoryRecursiveRestore GuardMemoryMultiTensorSourceRegion
  GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorBackend GuardMemoryBooleanScan GuardMemoryMultiTensorPairScan.
From GuardInterface Require Import ClightTensorBackendGuard ClightTensorRegionPackage ClightMultiTensorExample
  ClightMultiTensorSourceExample ClightMultiTensorCandidates ClightMultiTensorPairScanExample
  ClightMultiTensorPairScanExit ClightMultiTensorPairScanCandidates ClightMultiTensorPublicScan
  ClightSharedGuard ClightStagedCheck.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The existing generated AST now has a boundary theorem for arbitrary caller
    observations. The executable freshness test is a static installation gate. *)
Section EXECUTION.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable counts : list nat.
Variables values sizes : list Z.
Variables temps source_after : temp_env.
Variables memory final : mem.
Variable cap : Z.
Variable live : list ident.
Variable pool : list (ident * ident).
Variable proposal : ClightTensorGeneratedCandidates.tensor_generated_candidate.
Variable code : statement.
Hypotheses (LENGTH : length counts = 3%nat)
  (COUNTS : Forall (fun count => count <> O /\ signed_range (Z.of_nat count)) counts)
  (BOUNDS : memory_nest_bindings [1%positive;3%positive;4%positive] (map Z.of_nat counts) temps)
  (INITIAL : temps!6%positive = Some (Vint Int.zero))
  (SCALARS : memory_nest_bindings [2%positive;5%positive] values temps)
  (SIGNED : Forall signed_range values)
  (OBSERVE : tensor_observe_dimensions multi_tensor_demo_dimensions temps = Some sizes)
  (GUARD : decision_run (Entry ge locals temps memory) (tensor_backend_guard multi_tensor_demo_dimensions) true)
  (BOX : multi_tensor_body_box multi_tensor_nest_demo_items counts values sizes = true)
  (WITHIN : MemoryNested.A.env_within (memory_scalar_static_bounds (length counts) cap (length values))
    (map Z.of_nat counts++values))
  (FRESH : tensor_disjoint live multi_tensor_demo_pair_private = true)
  (SOURCE : exec_stmt fe ge locals temps memory (memory_nest_source multi_tensor_nest_demo_nest) E0 source_after final Out_normal)
  (CHECK : mayReturn (check_multi_tensor_generated (length counts) cap (length values) multi_tensor_nest_demo_instructions
    multi_tensor_demo_dimensions multi_tensor_demo_pointers multi_tensor_demo_layout live pool proposal) (Some code)).

Theorem multi_tensor_demo_pair_candidate_at_public_exit checked :
  temp_agree multi_tensor_demo_pair_public temps checked ->
  temp_agree live temps checked ->
  multi_tensor_separated_source (length counts) (length values) multi_tensor_nest_demo_instructions
    (map Z.of_nat counts++values) temps sizes ->
  exists restored,
    exec_stmt fe ge locals checked memory (Ssequence code (memory_recursive_restore multi_tensor_nest_demo_nest))
      E0 restored final Out_normal /\ temp_agree live source_after restored.
Proof.
  intros FRAME PUBLIC SEPARATED.
  destruct (@multi_tensor_demo_pair_source_at_public_exit fe ge locals temps checked memory source_after final live
    FRAME PUBLIC SOURCE) as [after [CHECKED_SOURCE SOURCE_FRAME]].
  destruct (@multi_tensor_demo_pair_setup_at_exit counts values sizes ge locals temps checked memory FRAME
    BOUNDS INITIAL SCALARS OBSERVE GUARD) as [AFTER_BOUNDS [AFTER_INITIAL [AFTER_SCALARS [AFTER_OBSERVE AFTER_GUARD]]]].
  assert (VALUE_LENGTH : length values = 2%nat).
  { pose proof (Forall2_length SCALARS) as LEN; cbn [length] in LEN; lia. }
  pose proof (@multi_tensor_demo_pair_separation_at_exit counts values sizes temps checked LENGTH VALUE_LENGTH
    FRAME SEPARATED) as AFTER_SEPARATED.
  destruct (@multi_tensor_nest_demo_generated_restored fe ge locals counts values sizes checked memory after final
    cap live pool proposal code LENGTH COUNTS AFTER_BOUNDS AFTER_INITIAL AFTER_SCALARS SIGNED AFTER_OBSERVE AFTER_GUARD
    BOX WITHIN AFTER_SEPARATED CHECKED_SOURCE CHECK) as [restored [RUN EXIT]].
  exists restored; split; [exact RUN|].
  eapply temp_agree_trans; [exact SOURCE_FRAME|exact EXIT].
Qed.

Theorem multi_tensor_demo_pair_public_versioned_execution :
  exists after,
    exec_stmt fe ge locals temps memory (multi_tensor_demo_pair_versioned code) E0 after final Out_normal /\
    temp_agree live source_after after.
Proof.
  assert (LAYOUT : tensor_layout_flag sizes = true).
  { exact (@tensor_backend_guard_accepts (Entry ge locals temps memory) multi_tensor_demo_dimensions sizes OBSERVE GUARD). }
  destruct (@tensor_observe_dimensions_sound multi_tensor_demo_dimensions temps sizes OBSERVE) as [DIMENSIONS _].
  destruct (@multi_tensor_demo_source_licensed_pair_guard fe ge locals counts values sizes temps memory source_after final
    LENGTH COUNTS BOUNDS INITIAL LAYOUT DIMENSIONS SCALARS BOX SOURCE)
    as [checked [SCAN [FRAME [FLAG SOUND]]]].
  pose proof (@multi_tensor_demo_pair_guard_public_frame fe ge locals temps checked memory live FRESH SCAN) as PUBLIC.
  set (accepted := multi_tensor_pair_check (GuardMemoryMultiTensorBackend.multi_tensor_locations temps sizes)
    (map Z.of_nat counts) 9%positive 10%positive) in *.
  assert (BRANCH : exists after,
    exec_stmt fe ge locals checked memory
      (if accepted then Ssequence code (memory_recursive_restore multi_tensor_nest_demo_nest)
       else memory_nest_source multi_tensor_nest_demo_nest) E0 after final Out_normal /\
    temp_agree live source_after after).
  { destruct accepted.
    - apply multi_tensor_demo_pair_candidate_at_public_exit; [exact FRAME|exact PUBLIC|apply SOUND; exact FLAG].
    - exact (@multi_tensor_demo_pair_source_at_public_exit fe ge locals temps checked memory source_after final live
        FRAME PUBLIC SOURCE). }
  destruct BRANCH as [after [RUN EXIT]].
  exists after; split; [|exact EXIT].
  unfold multi_tensor_demo_pair_versioned; eapply check_result_gate_execution;
    [exact SCAN|exact FLAG|exact RUN].
Qed.
End EXECUTION.

Print Assumptions multi_tensor_demo_pair_candidate_at_public_exit.
Print Assumptions multi_tensor_demo_pair_public_versioned_execution.
