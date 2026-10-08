From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRuntimeReceipts GuardMemoryRecursiveSource
  GuardMemoryDynamicTensorBackend GuardMemoryMultiTensorBackend GuardMemoryMultiTensorAffineFootprint
  GuardMemoryMultiTensorAffineScan GuardMemoryBooleanScan GuardMemoryBooleanTests.
Import ListNotations.
Set Implicit Arguments.

Definition canonical_affine_read_ports dimensions scalars accesses :=
  multi_tensor_affine_scan_public dimensions scalars accesses [].
Definition canonical_affine_tests_statement dimensions left right scalars flag accesses :=
  memory_boolean_tests_statement flag
    (map (multi_tensor_affine_checked_test dimensions (left++scalars) (right++scalars))
      (multi_tensor_affine_pairs accesses)).

(** Extra private control state is framed at its current value, not compared
    with undefined scratch at the original source entry. *)
Theorem canonical_affine_tests_execution dimensions sizes original current memory
    left right scalars flag accesses values a b extra fe ge locals accepted :
  GuardMemoryDynamicTensorLayout.tensor_layout_flag sizes = true ->
  tensor_dimension_view dimensions sizes original ->
  memory_nest_bindings scalars values original ->
  temp_agree (canonical_affine_read_ports dimensions scalars accesses) original current ->
  memory_nest_bindings left a current -> memory_nest_bindings right b current ->
  (forall access, In access accesses ->
    memory_cell_access (multi_tensor_locations original sizes) memory (exact_cell access (a++values)) Readable) ->
  (forall access, In access accesses ->
    memory_cell_access (multi_tensor_locations original sizes) memory (exact_cell access (b++values)) Readable) ->
  ~ In flag (left++right++canonical_affine_read_ports dimensions scalars accesses++extra) ->
  current!flag = Some (memory_boolean_word accepted) ->
  exists after,
    exec_stmt fe ge locals current memory
      (canonical_affine_tests_statement dimensions left right scalars flag accesses) E0 after memory Out_normal /\
    temp_agree (left++right++canonical_affine_read_ports dimensions scalars accesses++extra) current after /\
    after!flag = Some (memory_boolean_word
      (accepted && multi_tensor_affine_point_check (multi_tensor_locations original sizes) accesses values a b)).
Proof.
  intros LAYOUT DIMENSIONS SCALARS PUBLIC LEFT RIGHT FIRST_POINTS SECOND_POINTS FLAG_FRESH FLAG.
  assert (TESTS : forall pair inside, In pair (multi_tensor_affine_pairs accesses) ->
    temp_agree (left++right++canonical_affine_read_ports dimensions scalars accesses++extra) current inside ->
    expression_test (multi_tensor_affine_checked_test dimensions (left++scalars) (right++scalars) pair)
      (Entry ge locals inside memory)
      (multi_tensor_affine_access_check (multi_tensor_locations original sizes)
        (fst pair) (snd pair) (a++values) (b++values))).
  { intros [first second] inside MEMBER INSIDE.
    apply multi_tensor_affine_pairs_member in MEMBER as [FIRST SECOND].
    assert (PORTS : temp_agree (canonical_affine_read_ports dimensions scalars accesses) original inside).
    { eapply temp_agree_trans; [exact PUBLIC|]; eapply temp_agree_weaken; [|exact INSIDE];
        intros id IN; repeat rewrite in_app_iff; tauto. }
    assert (SCALAR_WORDS : memory_nest_bindings scalars values inside).
    { eapply memory_nest_bindings_frame_from; [|exact PORTS|exact SCALARS].
      intros id IN; unfold canonical_affine_read_ports,multi_tensor_affine_scan_public;
        repeat rewrite in_app_iff; tauto. }
    eapply multi_tensor_affine_checked_test_evaluation;
      [exact LAYOUT| | | | |apply FIRST_POINTS; exact FIRST|apply SECOND_POINTS; exact SECOND].
    - eapply tensor_dimension_view_frame; [|exact DIMENSIONS].
      eapply temp_agree_weaken; [|exact PORTS].
      intros id IN; unfold canonical_affine_read_ports,multi_tensor_affine_scan_public;
        repeat rewrite in_app_iff; tauto.
    - eapply temp_agree_weaken; [|exact PORTS]; cbn; intros id [ID|[ID|[]]]; subst id;
        unfold canonical_affine_read_ports,multi_tensor_affine_scan_public;
        apply in_or_app; left; apply in_map_iff; [exists first|exists second]; auto.
    - apply Forall2_app; [|exact SCALAR_WORDS].
      eapply memory_nest_bindings_frame_from; [|exact INSIDE|exact LEFT];
        intros id IN; repeat rewrite in_app_iff; tauto.
    - apply Forall2_app; [|exact SCALAR_WORDS].
      eapply memory_nest_bindings_frame_from; [|exact INSIDE|exact RIGHT];
        intros id IN; repeat rewrite in_app_iff; tauto. }
  destruct (@memory_boolean_tests_execution fe ge locals memory flag
    (left++right++canonical_affine_read_ports dimensions scalars accesses++extra) current
    (AccessFunction*AccessFunction)
    (multi_tensor_affine_checked_test dimensions (left++scalars) (right++scalars))
    (fun pair => multi_tensor_affine_access_check (multi_tensor_locations original sizes)
      (fst pair) (snd pair) (a++values) (b++values))
    (multi_tensor_affine_pairs accesses) FLAG_FRESH TESTS current accepted ltac:(apply temp_agree_refl) FLAG)
    as [after [RUN [FRAME RESULT]]].
  exists after; split; [exact RUN|split; [exact FRAME|]].
  unfold multi_tensor_affine_pairs in RESULT; rewrite multi_tensor_affine_pairs_results in RESULT; exact RESULT.
Qed.

Print Assumptions canonical_affine_tests_execution.
