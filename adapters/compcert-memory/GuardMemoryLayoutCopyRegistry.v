From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import CompCertMemoryActions ClightRectangularStore.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryMultipleArrays
  GuardMemoryRegistryBackend GuardMemoryNamedRegistrySource GuardMemoryCopyArray
  GuardMemoryLayoutCopy GuardMemoryLayoutCopyInstruction.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_layout_copy_descriptors write_shape read_shape write_array read_array :=
  [MemoryArrayDescriptor write_array write_array write_shape;
    MemoryArrayDescriptor read_array read_array read_shape].
Definition memory_layout_copy_point ge locals write_shape read_shape write_array read_array i j before after :=
  exists write_block read_block, rect_array_binding write_shape ge locals write_array write_block /\
    rect_array_binding read_shape ge locals read_array read_block /\
    memory_action_run (memory_layout_copy_action write_shape read_shape write_block read_block i j) before after.
Theorem memory_layout_copy_registry write_shape read_shape write_array read_array ge locals before after :
  rectangle_layout_valid write_shape -> rectangle_layout_valid read_shape -> write_array <> read_array ->
  memory_layout_copy_point ge locals write_shape read_shape write_array read_array 0 0 before after ->
  exists entries,
    Forall2 (memory_descriptor_binding ge locals)
      (memory_layout_copy_descriptors write_shape read_shape write_array read_array) entries /\
    NoDup (map memory_array_id entries) /\
    Forall (fun entry => Mem.valid_pointer before (memory_array_block entry) 0 = true) entries.
Proof.
  intros WVALID RVALID DISTINCT [write_block [read_block [WRITE [READ RUN]]]].
  assert (COMMON : memory_action_run (memory_copy_action write_shape write_block read_block 0 0) before after) by exact RUN.
  destruct (@memory_copy_physical_store write_shape write_block read_block 0 0 before after COMMON) as [value STORE].
  assert (WPOINTER : Mem.valid_pointer before write_block 0 = true).
  { replace (4*(0*rectangle_stride write_shape+0)) with 0 in STORE by ring.
    apply Mem.valid_pointer_nonempty_perm.
    pose proof (@Mem.store_valid_access_3 _ _ _ _ _ _ STORE) as [PERMISSION ALIGN].
    eapply Mem.perm_implies; [apply PERMISSION; change (0 <= 0 < 4); lia|constructor]. }
  pose proof (@memory_copy_base_read_valid write_shape write_block read_block before after COMMON) as RPOINTER.
  exists [MemoryArrayEntry write_array write_block (rectangle_extent write_shape);
    MemoryArrayEntry read_array read_block (rectangle_extent read_shape)].
  split.
  - constructor; [unfold memory_descriptor_binding; cbn; split; [reflexivity|]; split; [reflexivity|]; split; assumption|].
    constructor; [unfold memory_descriptor_binding; cbn; split; [reflexivity|]; split; [reflexivity|]; split; assumption|constructor].
  - split.
    + cbn; constructor; [cbn; intuition congruence|constructor; [cbn; tauto|constructor]].
    + constructor; [exact WPOINTER|constructor; [exact RPOINTER|constructor]].
Qed.
Theorem memory_layout_copy_point_execution write_shape read_shape write_array read_array entries ge locals i j before after :
  Forall2 (memory_descriptor_binding ge locals)
    (memory_layout_copy_descriptors write_shape read_shape write_array read_array) entries ->
  NoDup (map memory_array_id entries) ->
  0 <= i*rectangle_stride write_shape+j < rectangle_extent write_shape ->
  0 <= i*rectangle_stride read_shape+j < rectangle_extent read_shape ->
  (memory_layout_copy_point ge locals write_shape read_shape write_array read_array i j before after <->
    memory_point (memory_layout_copy_instruction write_shape read_shape write_array read_array) i j
      (RuntimeState (memory_array_registry entries) before) (RuntimeState (memory_array_registry entries) after)).
Proof.
  intros BINDINGS UNIQUE WINDEX RINDEX.
  inversion BINDINGS as [|descriptor write_entry descriptors rest WB TAIL]; subst.
  inversion TAIL as [|descriptor read_entry descriptors empty RB END]; subst.
  inversion END; subst.
  destruct WB as [WRITE_ID [WRITE_EXTENT [WVALID WRITE]]].
  destruct RB as [READ_ID [READ_EXTENT [RVALID READ]]].
  cbn in WRITE_ID,READ_ID,WRITE_EXTENT,READ_EXTENT,WRITE,READ.
  unfold memory_layout_copy_point.
  rewrite <- WRITE_ID in WRITE; rewrite <- READ_ID in READ.
  rewrite <- WRITE_ID,<- READ_ID.
  rewrite (@memory_layout_copy_registry_execution [write_entry;read_entry] write_entry read_entry write_shape read_shape i j before after
    UNIQUE ltac:(cbn; auto) ltac:(cbn; auto) WRITE_EXTENT READ_EXTENT WINDEX RINDEX).
  split.
  - intros [write_block [read_block [WB [RB RUN]]]].
    assert (WSAME : write_block = memory_array_block write_entry) by (eapply rect_array_binding_unique; eauto).
    assert (RSAME : read_block = memory_array_block read_entry) by (eapply rect_array_binding_unique; eauto).
    subst write_block read_block; exact RUN.
  - intro RUN; exists (memory_array_block write_entry),(memory_array_block read_entry); repeat split; assumption.
Qed.
Print Assumptions memory_layout_copy_registry.
Print Assumptions memory_layout_copy_point_execution.
