From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightTempFootprint
  ClightProjectedExecution ClightNoWrap CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryFiniteFootprint GuardMemoryFootprintRestriction
  GuardMemoryRecursiveSource GuardMemoryMultiTensorBackend GuardMemoryMultiTensorPairSeparation
  GuardMemoryMultiTensorGuardExit GuardMemoryDynamicTensorBackend.
From GuardInterface Require Import ClightMultiTensorExample ClightMultiTensorSourceExample
  ClightMultiTensorCandidates ClightMultiTensorPairScanExample ClightTensorBackendGuard.
Import ListNotations.
Set Implicit Arguments.

Example multi_tensor_demo_pair_source_scope :
  statement_scope multi_tensor_demo_pair_public (memory_nest_source multi_tensor_nest_demo_nest).
Proof.
  intros identifier MEMBER; vm_compute in MEMBER; vm_compute; intuition congruence.
Qed.
Example multi_tensor_demo_pair_source_writes :
  writes_only [6%positive;7%positive;8%positive] (memory_nest_source multi_tensor_nest_demo_nest).
Proof.
  unfold multi_tensor_nest_demo_nest,multi_tensor_nest_demo_middle,multi_tensor_nest_demo_inner.
  cbn [memory_nest_source multi_tensor_demo_body];
    unfold ClightRectangularLoops.rectangle_reset,ClightCountedLoop.counted_loop,ClightCountedLoop.counter_increment;
    repeat first [apply writes_sequence|apply writes_if|apply writes_loop|apply writes_set|
      apply writes_assign|apply writes_skip|apply writes_break|apply writes_continue]; cbn; auto.
Qed.

Theorem multi_tensor_demo_pair_source_at_exit fe ge locals original checked memory after final :
  temp_agree multi_tensor_demo_pair_public original checked ->
  exec_stmt fe ge locals original memory (memory_nest_source multi_tensor_nest_demo_nest) E0 after final Out_normal ->
  exists source_after,
    exec_stmt fe ge locals checked memory (memory_nest_source multi_tensor_nest_demo_nest) E0 source_after final Out_normal /\
    temp_agree multi_tensor_demo_pair_public after source_after.
Proof.
  intros FRAME SOURCE; eapply structured_execution_temp_transport;
    [exact SOURCE|exact multi_tensor_demo_pair_source_writes|exact multi_tensor_demo_pair_source_scope|exact FRAME].
Qed.

Theorem multi_tensor_demo_pair_separation_at_exit counts values sizes original checked :
  length counts = 3%nat -> length values = 2%nat ->
  temp_agree multi_tensor_demo_pair_public original checked ->
  multi_tensor_separated_source (length counts) (length values) multi_tensor_nest_demo_instructions
    (map Z.of_nat counts++values) original sizes ->
  multi_tensor_separated_source (length counts) (length values) multi_tensor_nest_demo_instructions
    (map Z.of_nat counts++values) checked sizes.
Proof.
  intros LENGTH VALUE_LENGTH FRAME SEPARATED.
  unfold multi_tensor_separated_source in *.
  change (locations_nonalias (memory_restrict_locations (memory_footprint_allowed
    (multi_tensor_demo_pair_footprint counts values)) (multi_tensor_locations checked sizes))).
  eapply multi_tensor_restricted_separation_at_exit with (pointers:=[9%positive;10%positive]) (original:=original).
  - eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER;
      vm_compute in MEMBER; vm_compute; intuition congruence.
  - pose proof (@multi_tensor_demo_pair_footprint_covered counts values LENGTH VALUE_LENGTH) as COVERED.
    eapply Forall_impl; [|exact COVERED]; intros cell [[FIRST|SECOND] RANGE]; cbn; auto.
  - exact SEPARATED.
Qed.

(** All parameter observations refer to the actual check exit. No equality of
    the complete raw registry or all private temporaries is required. *)
Theorem multi_tensor_demo_pair_setup_at_exit counts values sizes ge locals original checked memory :
  temp_agree multi_tensor_demo_pair_public original checked ->
  memory_nest_bindings [1%positive;3%positive;4%positive] (map Z.of_nat counts) original ->
  original!6%positive = Some (Vint Int.zero) ->
  memory_nest_bindings [2%positive;5%positive] values original ->
  tensor_observe_dimensions multi_tensor_demo_dimensions original = Some sizes ->
  decision_run (Entry ge locals original memory) (tensor_backend_guard multi_tensor_demo_dimensions) true ->
  memory_nest_bindings [1%positive;3%positive;4%positive] (map Z.of_nat counts) checked /\
  checked!6%positive = Some (Vint Int.zero) /\
  memory_nest_bindings [2%positive;5%positive] values checked /\
  tensor_observe_dimensions multi_tensor_demo_dimensions checked = Some sizes /\
  decision_run (Entry ge locals checked memory) (tensor_backend_guard multi_tensor_demo_dimensions) true.
Proof.
  intros FRAME BOUNDS INITIAL SCALARS OBSERVE GUARD.
  assert (DIMENSION_FRAME : temp_agree (tensor_dimension_registers multi_tensor_demo_dimensions) original checked).
  { eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER;
      vm_compute in MEMBER; vm_compute; intuition congruence. }
  destruct (@tensor_backend_guard_at_framed_exit multi_tensor_demo_dimensions sizes
    (Entry ge locals original memory) checked DIMENSION_FRAME OBSERVE GUARD) as [AFTER_OBSERVE AFTER_GUARD].
  split.
  - eapply memory_nest_bindings_frame_from; [|exact FRAME|exact BOUNDS].
    intros identifier MEMBER; vm_compute in MEMBER; vm_compute; intuition congruence.
  - split; [rewrite FRAME by (vm_compute; intuition congruence); exact INITIAL|split].
    + eapply memory_nest_bindings_frame_from; [|exact FRAME|exact SCALARS].
      intros identifier MEMBER; vm_compute in MEMBER; vm_compute; intuition congruence.
    + split; assumption.
Qed.

Print Assumptions multi_tensor_demo_pair_source_scope.
Print Assumptions multi_tensor_demo_pair_source_writes.
Print Assumptions multi_tensor_demo_pair_source_at_exit.
Print Assumptions multi_tensor_demo_pair_separation_at_exit.
Print Assumptions multi_tensor_demo_pair_setup_at_exit.
