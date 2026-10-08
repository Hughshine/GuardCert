From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightNoWrap ClightTempFrame ClightRectangularStore.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops
  GuardMemoryLoopTrace GuardMemoryFiniteFootprint GuardMemoryRuntimeReceipts
  GuardMemoryFiniteAliasCondition GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorBackend
  GuardMemoryRecursiveSource GuardMemoryScalarLoops GuardMemoryMultiTensorSequence
  GuardMemoryMultiTensorSourceCapabilities GuardMemoryMultiTensorBackend GuardMemoryMultiTensorFrame
  GuardMemoryMultiTensorSourceRegion GuardMemoryMultiTensorAddressReceipts.
From GuardInterface Require Import ClightMultiTensorExample ClightMultiTensorSourceExample ClightMultiTensorCandidates.
Import ListNotations.
Local Open Scope Z_scope.

Example multi_tensor_demo_used_scalar_check :
  multi_tensor_scalar_use_check [2%positive;5%positive] multi_tensor_nest_demo_items = true.
Proof. vm_compute; reflexivity. Qed.
Example multi_tensor_demo_unused_scalar_refused :
  multi_tensor_scalar_use_check [2%positive;5%positive;99%positive] multi_tensor_nest_demo_items = false.
Proof. vm_compute; reflexivity. Qed.
Example multi_tensor_demo_actual_pointer_uses :
  multi_tensor_body_pointers multi_tensor_nest_demo_items = [9%positive;10%positive;10%positive;9%positive].
Proof. vm_compute; reflexivity. Qed.

(** No layout, alias, mathematical coordinate, or entry value premise is used
    to obtain the pointer and scalar words from a reached original body. *)
Theorem multi_tensor_demo_entry_observations fe ge locals temps memory after final :
  Forall (fun bound => 0 < Int.signed (temp_word bound temps)) [1%positive;3%positive;4%positive] ->
  temps!6%positive = Some (Vint Int.zero) ->
  exec_stmt fe ge locals temps memory (memory_nest_source multi_tensor_nest_demo_nest) E0 after final Out_normal ->
  Forall (multi_tensor_pointer_domain temps) [9%positive;10%positive;10%positive;9%positive] /\
  (forall identifier, In identifier [2%positive;5%positive] -> multi_tensor_word_domain temps identifier).
Proof.
  intros POSITIVE INITIAL SOURCE.
  destruct (@multi_tensor_source_region_first_capabilities multi_tensor_demo_dimensions multi_tensor_nest_demo_nest
    [2%positive;5%positive] multi_tensor_nest_demo_items fe ge locals temps memory after final
    multi_tensor_nest_demo_body_checked ltac:(vm_compute; discriminate)
    multi_tensor_nest_demo_shapes multi_tensor_nest_demo_fresh
    ltac:(intros identifier MEMBER BAD; cbn in MEMBER; vm_compute in BAD; intuition congruence)
    multi_tensor_demo_used_scalar_check POSITIVE INITIAL SOURCE) as [POINTERS WORDS].
  split; [exact POINTERS|intros identifier MEMBER; apply WORDS; apply in_or_app; right; exact MEMBER].
Qed.

(** A reference guard for the actual entry footprint, after layout/box setup.
    Its list is an entry-indexed specification witness. It is not an emitted
    runtime scanner for arbitrary unknown counts. *)
Definition multi_tensor_demo_reference_alias_tree counts scalar_values :=
  memory_finite_address_tree (multi_tensor_cell_address multi_tensor_demo_dimensions)
    (memory_events_footprint (memory_loop_trace
      (memory_scalar_rectangle 0 (length counts) (length scalar_values) multi_tensor_nest_demo_instructions)
      (map Z.of_nat counts ++ scalar_values))).

Theorem multi_tensor_demo_reference_alias_condition fe ge locals counts scalar_values sizes temps memory after final :
  length counts = 3%nat -> Forall (fun count => count <> O /\ signed_range (Z.of_nat count)) counts ->
  memory_nest_bindings [1%positive;3%positive;4%positive] (map Z.of_nat counts) temps -> temps!6%positive = Some (Vint Int.zero) ->
  tensor_layout_flag sizes = true -> tensor_dimension_view multi_tensor_demo_dimensions sizes temps ->
  memory_nest_bindings [2%positive;5%positive] scalar_values temps ->
  multi_tensor_body_box multi_tensor_nest_demo_items counts scalar_values sizes = true ->
  exec_stmt fe ge locals temps memory (memory_nest_source multi_tensor_nest_demo_nest) E0 after final Out_normal ->
  exists accepted,
    decision_run (Entry ge locals temps memory) (multi_tensor_demo_reference_alias_tree counts scalar_values) accepted /\
    (accepted = true -> multi_tensor_separated_source (length counts) (length scalar_values)
      multi_tensor_nest_demo_instructions (map Z.of_nat counts ++ scalar_values) temps sizes).
Proof.
  intros LENGTH COUNTS BOUNDS INITIAL LAYOUT DIMENSIONS SCALARS BOX SOURCE.
  destruct (@multi_tensor_nest_demo_source_execution fe ge locals counts scalar_values sizes temps memory after final
    LENGTH COUNTS BOUNDS INITIAL LAYOUT DIMENSIONS SCALARS BOX SOURCE) as [MODEL _].
  pose proof (@multi_tensor_loop_entry_address_receipts multi_tensor_demo_dimensions sizes temps memory final
    _ _ ge locals LAYOUT DIMENSIONS MODEL) as BINDINGS.
  set (cells := memory_events_footprint (memory_loop_trace
    (memory_scalar_rectangle 0 (length counts) (length scalar_values) multi_tensor_nest_demo_instructions)
    (map Z.of_nat counts ++ scalar_values))) in *.
  set (accepted := memory_finite_address_check (multi_tensor_locations temps sizes) cells).
  assert (RUN : decision_run (Entry ge locals temps memory)
    (memory_finite_address_tree (multi_tensor_cell_address multi_tensor_demo_dimensions) cells) accepted).
  { apply (proj2 (@memory_finite_address_exact _ _ _ cells BINDINGS accepted)); reflexivity. }
  exists accepted; split; [exact RUN|intro ACCEPT].
  unfold multi_tensor_separated_source,multi_tensor_source_footprint.
  eapply memory_finite_alias_condition_sound; [exact BINDINGS|rewrite <- ACCEPT; exact RUN].
Qed.

Theorem multi_tensor_demo_entry_permissions fe ge locals counts scalar_values sizes temps memory after final :
  length counts = 3%nat -> Forall (fun count => count <> O /\ signed_range (Z.of_nat count)) counts ->
  memory_nest_bindings [1%positive;3%positive;4%positive] (map Z.of_nat counts) temps -> temps!6%positive = Some (Vint Int.zero) ->
  tensor_layout_flag sizes = true -> tensor_dimension_view multi_tensor_demo_dimensions sizes temps ->
  memory_nest_bindings [2%positive;5%positive] scalar_values temps ->
  multi_tensor_body_box multi_tensor_nest_demo_items counts scalar_values sizes = true ->
  exec_stmt fe ge locals temps memory (memory_nest_source multi_tensor_nest_demo_nest) E0 after final Out_normal ->
  Forall (memory_event_access_receipt (multi_tensor_locations temps sizes) memory)
    (memory_loop_trace (memory_scalar_rectangle 0 (length counts) (length scalar_values) multi_tensor_nest_demo_instructions)
      (map Z.of_nat counts ++ scalar_values)).
Proof.
  intros LENGTH COUNTS BOUNDS INITIAL LAYOUT DIMENSIONS SCALARS BOX SOURCE.
  destruct (@multi_tensor_nest_demo_source_execution fe ge locals counts scalar_values sizes temps memory after final
    LENGTH COUNTS BOUNDS INITIAL LAYOUT DIMENSIONS SCALARS BOX SOURCE) as [MODEL _].
  exact (@memory_loop_entry_access_receipts
    (memory_scalar_rectangle 0 (length counts) (length scalar_values) multi_tensor_nest_demo_instructions)
    (map Z.of_nat counts ++ scalar_values) (RuntimeState (multi_tensor_locations temps sizes) memory)
    (RuntimeState (multi_tensor_locations temps sizes) final) MODEL).
Qed.

(** An allocated word has address permissions while its value is Vundef.
    Storing an integer then defines it. Thus entry permission alone cannot
    justify a value-dependent check copied from after this initializing store. *)
Theorem multi_tensor_demo_initialization_distinguishes_permission :
  exists memory block written,
    Mem.valid_access memory Mint32 block 0 Writable /\
    Mem.load Mint32 memory block 0 = Some Vundef /\
    Mem.store Mint32 memory block 0 (Vint (Int.repr 11)) = Some written /\
    Mem.load Mint32 written block 0 = Some (Vint (Int.repr 11)) /\
    (forall ge alpha, Cop.sem_binary_operation ge Oadd Vundef type_int32s (Vint alpha) type_int32s memory = None).
Proof.
  destruct (Mem.alloc Mem.empty 0 4) as [memory block] eqn:ALLOC.
  assert (PERMISSION : Mem.valid_access memory Mint32 block 0 Writable).
  { eapply Mem.valid_access_implies.
    - exact (@Mem.valid_access_alloc_same Mem.empty 0 4 memory block ALLOC Mint32 0
        ltac:(lia) ltac:(cbn; lia) ltac:(apply Z.divide_0_r)).
    - constructor. }
  destruct (@Mem.valid_access_store memory Mint32 block 0 (Vint (Int.repr 11)) PERMISSION) as [written STORE].
  exists memory,block,written; split; [exact PERMISSION|split].
  - exact (@Mem.load_alloc_same' Mem.empty 0 4 memory block ALLOC Mint32 0
      ltac:(lia) ltac:(cbn; lia) ltac:(apply Z.divide_0_r)).
  - split; [exact STORE|split].
    + exact (@Mem.load_store_same Mint32 memory block 0 (Vint (Int.repr 11)) written STORE).
    + intros; reflexivity.
Qed.

Print Assumptions multi_tensor_demo_used_scalar_check.
Print Assumptions multi_tensor_demo_unused_scalar_refused.
Print Assumptions multi_tensor_demo_actual_pointer_uses.
Print Assumptions multi_tensor_demo_entry_observations.
Print Assumptions multi_tensor_demo_entry_permissions.
Print Assumptions multi_tensor_demo_reference_alias_condition.
Print Assumptions multi_tensor_demo_initialization_distinguishes_permission.
