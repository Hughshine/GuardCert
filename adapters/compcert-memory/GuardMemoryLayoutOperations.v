From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import CompCertMemoryActions ClightRectangularStore ClightRectangularGuard ClightTempFrame ClightLoopSyntax ClightRegionProgress ClightStraightLine.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryMultipleArrays GuardMemoryNamedOperations GuardMemoryCopyArray
  GuardMemoryNamedRegistrySource GuardMemoryLayoutCopy GuardMemoryLayoutCopyInstruction GuardMemoryLayoutCopyRegistry
  GuardMemoryRegistryBackend GuardMemoryLayoutRegistry GuardMemoryArrayFamilyBackend GuardMemoryClightRectangles GuardMemoryLayoutCopyRegistryPoint.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Inductive memory_layout_operation :=
| MemoryLayoutNamed (operation : named_array_operation)
| MemoryLayoutCopy (write_shape read_shape : rectangle_shape) (write_array read_array : ident).
Definition memory_layout_operation_requests operation :=
  match operation with
  | MemoryLayoutNamed operation => map (fun array => MemoryArrayDescriptor array array (named_operation_shape operation)) (named_operation_arrays operation)
  | MemoryLayoutCopy write_shape read_shape write_array read_array => memory_layout_copy_descriptors write_shape read_shape write_array read_array
  end.
Definition memory_layout_operation_instruction operation :=
  match operation with
  | MemoryLayoutNamed operation => named_operation_instruction operation
  | MemoryLayoutCopy write_shape read_shape write_array read_array => memory_layout_copy_instruction write_shape read_shape write_array read_array
  end.
Definition memory_layout_operation_statement row column operation :=
  match operation with
  | MemoryLayoutNamed operation => named_operation_statement row column operation
  | MemoryLayoutCopy write_shape read_shape write_array read_array => memory_layout_copy_statement write_shape read_shape write_array read_array row column
  end.
Definition memory_layout_operation_physical ge locals i j operation :=
  match operation with
  | MemoryLayoutNamed operation => named_operation_physical ge locals i j operation
  | MemoryLayoutCopy write_shape read_shape write_array read_array => memory_layout_copy_point ge locals write_shape read_shape write_array read_array i j
  end.
Definition memory_layout_operation_write_shape operation :=
  match operation with MemoryLayoutNamed operation => named_operation_shape operation | MemoryLayoutCopy write_shape _ _ _ => write_shape end.
Lemma memory_layout_operation_physical_store ge locals operation i j before after :
  memory_layout_operation_physical ge locals i j operation before after ->
  exists block value, Mem.store Mint32 before block
    (4*(i*rectangle_stride (memory_layout_operation_write_shape operation)+j)) value = Some after.
Proof.
  destruct operation as [operation|ws rs wa ra]; cbn.
  - apply named_operation_physical_store.
  - intros [wb [rb [WRITE [READ [inputs [value [LOAD [COMPUTE STORE]]]]]]]].
    exists wb,value; exact STORE.
Qed.
Lemma memory_layout_operation_initial_bindings ge locals operation before after :
  memory_layout_operation_physical ge locals 0 0 operation before after ->
  forall descriptor, In descriptor (memory_layout_operation_requests operation) ->
    exists block, rect_array_binding (memory_descriptor_shape descriptor) ge locals (memory_descriptor_variable descriptor) block /\
      Mem.valid_pointer before block 0 = true.
Proof.
  destruct operation as [operation|ws rs wa ra]; cbn.
  - intros RUN descriptor MEMBER; apply in_map_iff in MEMBER as [array [SAME MEMBER]].
    subst descriptor; cbn.
    eapply named_operation_base_bindings; [unfold named_operation_layout; split; reflexivity|exact RUN|exact MEMBER].
  - intros [wb [rb [WRITE [READ RUN]]]] descriptor MEMBER.
    assert (COMMON : memory_action_run (memory_copy_action ws wb rb 0 0) before after) by exact RUN.
    destruct MEMBER as [SAME|[SAME|BAD]]; [subst descriptor|subst descriptor|contradiction]; cbn.
    + exists wb; split; [exact WRITE|].
      destruct (@memory_copy_physical_store ws wb rb 0 0 before after COMMON) as [value STORE].
      replace (4*(0*rectangle_stride ws+0)) with 0 in STORE by ring.
      apply Mem.valid_pointer_nonempty_perm.
      pose proof (@Mem.store_valid_access_3 _ _ _ _ _ _ STORE) as [PERMISSION ALIGN].
      eapply Mem.perm_implies; [apply PERMISSION; change (0 <= 0 < 4); lia|constructor].
    + exists rb; split; [exact READ|eapply memory_copy_base_read_valid; exact COMMON].
Qed.
Print Assumptions memory_layout_operation_initial_bindings.

Definition memory_layout_indices requests i j :=
  forall descriptor, In descriptor requests ->
    rectangle_layout_valid (memory_descriptor_shape descriptor) /\
    0 <= i*rectangle_stride (memory_descriptor_shape descriptor)+j < rectangle_extent (memory_descriptor_shape descriptor) /\
    0 <= i*rectangle_stride (memory_descriptor_shape descriptor) < rectangle_extent (memory_descriptor_shape descriptor).
Lemma memory_layout_named_indices operation i j :
  memory_layout_indices (memory_layout_operation_requests (MemoryLayoutNamed operation)) i j ->
  rectangle_layout_valid (named_operation_shape operation) /\
  0 <= i*rectangle_stride (named_operation_shape operation)+j < rectangle_extent (named_operation_shape operation) /\
  0 <= i*rectangle_stride (named_operation_shape operation) < rectangle_extent (named_operation_shape operation).
Proof.
  intro INDICES; apply (INDICES (MemoryArrayDescriptor (named_operation_array operation) (named_operation_array operation) (named_operation_shape operation))).
  unfold memory_layout_operation_requests; apply in_map_iff; exists (named_operation_array operation); split; [reflexivity|].
  destruct operation; cbn; auto.
Qed.
Lemma memory_layout_operation_clight_inverse operation row column fe ge locals i j temps memory after final :
  memory_layout_indices (memory_layout_operation_requests operation) i j ->
  temps ! row = Some (Vint (Int.repr i)) -> temps ! column = Some (Vint (Int.repr j)) ->
  exec_stmt fe ge locals temps memory (memory_layout_operation_statement row column operation) E0 after final Out_normal ->
  memory_layout_operation_physical ge locals i j operation memory final /\ after = temps.
Proof.
  destruct operation as [operation|ws rs wa ra]; intros INDICES ROW COLUMN RUN; cbn in RUN |- *.
  - destruct (@memory_layout_named_indices operation i j INDICES) as [VALID [INDEX READ_INDEX]].
    eapply named_operation_clight_inverse; [exact VALID|unfold named_operation_layout; split; reflexivity|exact INDEX|exact READ_INDEX|exact ROW|exact COLUMN|exact RUN].
  - destruct (INDICES (MemoryArrayDescriptor wa wa ws) ltac:(cbn; auto)) as [WVALID [WINDEX WBASE]].
    destruct (INDICES (MemoryArrayDescriptor ra ra rs) ltac:(cbn; auto)) as [RVALID [RINDEX RBASE]].
    cbn in WVALID,WINDEX,RVALID,RINDEX.
    destruct (@memory_layout_copy_statement_inverse ws rs WVALID RVALID fe ge locals temps memory wa ra row column i j E0 after final Out_normal
      ROW COLUMN WINDEX RINDEX RUN) as [wb [rb [WRITE [READ [TRACE [TEMPS [OUT ACT]]]]]]].
    split; [exists wb,rb; auto|exact TEMPS].
Qed.
Lemma memory_layout_operation_normal row column operation :
  normal_statement (memory_layout_operation_statement row column operation) = true.
Proof. destruct operation as [[mode shape array|shape wa ra|shape wa ra]|ws rs wa ra]; cbn; try reflexivity; apply mode_normal. Qed.
Lemma memory_layout_operation_quiet row column operation :
  quiet_statement (memory_layout_operation_statement row column operation) = true.
Proof. destruct operation as [[mode shape array|shape wa ra|shape wa ra]|ws rs wa ra]; cbn; try reflexivity; apply mode_quiet. Qed.
Lemma memory_layout_operation_writes row column operation :
  writes_only [] (memory_layout_operation_statement row column operation).
Proof. destruct operation as [[mode shape array|shape wa ra|shape wa ra]|ws rs wa ra]; cbn; try constructor; apply mode_writes. Qed.
Print Assumptions memory_layout_operation_clight_inverse.

Theorem memory_layout_operation_registry_execution descriptors entries ge locals operation i j before after :
  Forall2 (memory_descriptor_binding ge locals) descriptors entries ->
  memory_descriptors_cover descriptors (memory_layout_operation_requests operation) ->
  NoDup (map memory_array_id entries) ->
  memory_layout_indices (memory_layout_operation_requests operation) i j ->
  (memory_layout_operation_physical ge locals i j operation before after <->
    memory_point (memory_layout_operation_instruction operation) i j
      (RuntimeState (memory_array_registry entries) before) (RuntimeState (memory_array_registry entries) after)).
Proof.
  destruct operation as [operation|ws rs wa ra]; intros ARRAYS COVER UNIQUE INDICES; cbn.
  - destruct (@memory_layout_named_indices operation i j INDICES) as [VALID [INDEX READ_INDEX]].
    apply named_operation_registry_execution with (base := named_operation_shape operation); auto.
    + unfold named_operation_layout; split; reflexivity.
    + intros array MEMBER; exact (@memory_registry_requested_array descriptors
        (memory_layout_operation_requests (MemoryLayoutNamed operation)) entries ge locals array (named_operation_shape operation)
        ARRAYS COVER ltac:(unfold memory_layout_operation_requests; apply in_map_iff; exists array; split; [reflexivity|exact MEMBER])).
  - destruct (INDICES (MemoryArrayDescriptor wa wa ws) ltac:(cbn; auto)) as [WVALID [WINDEX WBASE]].
    destruct (INDICES (MemoryArrayDescriptor ra ra rs) ltac:(cbn; auto)) as [RVALID [RINDEX RBASE]].
    cbn in WINDEX,RINDEX; apply memory_layout_copy_general_registry_point with (descriptors := descriptors); assumption.
Qed.
Print Assumptions memory_layout_operation_registry_execution.
