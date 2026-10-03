From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import CompCertMemoryActions ClightRectangularStore.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryMultipleArrays
  GuardMemoryRegistryBackend GuardMemoryNamedRegistrySource GuardMemoryCopyArray
  GuardMemoryLayoutCopy GuardMemoryLayoutCopyInstruction GuardMemoryLayoutCopyRegistry.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_copy_layout_descriptors write_shape read_shape write_array read_array :=
  if Pos.eq_dec write_array read_array then [MemoryArrayDescriptor write_array write_array write_shape]
  else memory_layout_copy_descriptors write_shape read_shape write_array read_array.
Definition memory_copy_layout_compatible write_shape read_shape (write_array read_array : ident) :=
  write_array <> read_array \/ rectangle_extent write_shape = rectangle_extent read_shape.
Lemma memory_rect_binding_equal_extent first second ge locals array block :
  rectangle_extent first = rectangle_extent second ->
  (rect_array_binding first ge locals array block <-> rect_array_binding second ge locals array block).
Proof. intro EXTENT; unfold rect_array_binding,rect_array_type; rewrite EXTENT; reflexivity. Qed.
Theorem memory_copy_layout_registry write_shape read_shape write_array read_array ge locals before after :
  rectangle_layout_valid write_shape -> rectangle_layout_valid read_shape ->
  memory_copy_layout_compatible write_shape read_shape write_array read_array ->
  memory_layout_copy_point ge locals write_shape read_shape write_array read_array 0 0 before after ->
  exists entries,
    Forall2 (memory_descriptor_binding ge locals)
      (memory_copy_layout_descriptors write_shape read_shape write_array read_array) entries /\
    NoDup (map memory_array_id entries) /\
    Forall (fun entry => Mem.valid_pointer before (memory_array_block entry) 0 = true) entries.
Proof.
  intros WVALID RVALID COMPATIBLE RUN.
  unfold memory_copy_layout_descriptors; destruct (Pos.eq_dec write_array read_array) as [SAME|DIFFERENT].
  - subst read_array; destruct COMPATIBLE as [CONTRA|EXTENT]; [contradiction|].
    destruct RUN as [write_block [read_block [WRITE [READ RUN]]]].
    apply (proj2 (@memory_rect_binding_equal_extent write_shape read_shape ge locals write_array read_block EXTENT)) in READ.
    assert (BLOCK : read_block = write_block) by (eapply rect_array_binding_unique; eauto).
    subst read_block.
    assert (COMMON : memory_action_run (memory_copy_action write_shape write_block write_block 0 0) before after) by exact RUN.
    destruct (@memory_copy_physical_store write_shape write_block write_block 0 0 before after COMMON) as [value STORE].
    assert (POINTER : Mem.valid_pointer before write_block 0 = true).
    { replace (4*(0*rectangle_stride write_shape+0)) with 0 in STORE by ring.
      apply Mem.valid_pointer_nonempty_perm.
      pose proof (@Mem.store_valid_access_3 _ _ _ _ _ _ STORE) as [PERMISSION ALIGN].
      eapply Mem.perm_implies; [apply PERMISSION; change (0 <= 0 < 4); lia|constructor]. }
    exists [MemoryArrayEntry write_array write_block (rectangle_extent write_shape)]; split.
    + constructor; [unfold memory_descriptor_binding; cbn; split; [reflexivity|]; split; [reflexivity|]; split; assumption|constructor].
    + split; [constructor; [cbn; tauto|constructor]|constructor; [exact POINTER|constructor]].
  - eapply memory_layout_copy_registry; eassumption.
Qed.
Theorem memory_copy_layout_point_execution write_shape read_shape write_array read_array entries ge locals i j before after :
  rectangle_layout_valid read_shape -> memory_copy_layout_compatible write_shape read_shape write_array read_array ->
  Forall2 (memory_descriptor_binding ge locals)
    (memory_copy_layout_descriptors write_shape read_shape write_array read_array) entries ->
  NoDup (map memory_array_id entries) ->
  0 <= i*rectangle_stride write_shape+j < rectangle_extent write_shape ->
  0 <= i*rectangle_stride read_shape+j < rectangle_extent read_shape ->
  (memory_layout_copy_point ge locals write_shape read_shape write_array read_array i j before after <->
    memory_point (memory_layout_copy_instruction write_shape read_shape write_array read_array) i j
      (RuntimeState (memory_array_registry entries) before) (RuntimeState (memory_array_registry entries) after)).
Proof.
  intros RVALID COMPATIBLE BINDINGS UNIQUE WINDEX RINDEX.
  unfold memory_copy_layout_descriptors in BINDINGS; destruct (Pos.eq_dec write_array read_array) as [SAME|DIFFERENT].
  - subst read_array; destruct COMPATIBLE as [CONTRA|EXTENT]; [contradiction|].
    inversion BINDINGS as [|descriptor entry descriptors empty BINDING END]; subst.
    inversion END; subst.
    destruct BINDING as [IDENTIFIER [SIZE [WVALID WRITE]]]; cbn in IDENTIFIER,SIZE,WRITE.
    assert (READ : rect_array_binding read_shape ge locals write_array (memory_array_block entry)).
    { apply (proj1 (@memory_rect_binding_equal_extent write_shape read_shape ge locals write_array (memory_array_block entry) EXTENT)); exact WRITE. }
    unfold memory_layout_copy_point; rewrite <- IDENTIFIER in WRITE,READ |- *.
    rewrite (@memory_layout_copy_registry_execution [entry] entry entry write_shape read_shape i j before after
      UNIQUE ltac:(cbn; auto) ltac:(cbn; auto) SIZE ltac:(rewrite SIZE; exact EXTENT) WINDEX RINDEX).
    split.
    + intros [write_block [read_block [WB [RB RUN]]]].
      assert (WSAME : write_block = memory_array_block entry) by (eapply rect_array_binding_unique; eauto).
      assert (RSAME : read_block = memory_array_block entry) by (eapply rect_array_binding_unique; eauto).
      subst write_block read_block; exact RUN.
    + intro RUN; exists (memory_array_block entry),(memory_array_block entry); repeat split; assumption.
  - apply memory_layout_copy_point_execution; assumption.
Qed.
Print Assumptions memory_copy_layout_registry.
Print Assumptions memory_copy_layout_point_execution.
