From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import CompCertMemoryActions CompCertStoreSchedule RectangularIteration
  ClightRectangularStore ClightRectangularRegion ClightRectangularUpdate ClightRectangularRowUpdate
  RectangularMemorySchedule RectangularRowSchedule ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles
  GuardMemoryLoops GuardMemorySequenceLoops GuardMemoryClightRectangles GuardMemoryArrayFamilyBackend
  GuardMemoryMultipleArrays GuardMemoryRegistryBackend GuardMemoryRegistryTransfer GuardMemoryNamedOperations
  GuardMemoryCrossArray GuardMemoryCrossInstruction GuardMemoryCopyArray GuardMemoryCopyInstruction.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition named_array_descriptors base operations :=
  map (fun array => MemoryArrayDescriptor array array base)
    (nodup Pos.eq_dec (flat_map named_operation_arrays operations)).

Lemma memory_mode_physical_store mode shape block i j before after :
  mode_physical mode shape block i j before after ->
  exists value, Mem.store Mint32 before block (4*(i*rectangle_stride shape+j)) value = Some after.
Proof.
  destruct mode; cbn [mode_physical].
  - intro STORE; exists (rect_payload shape i j); exact STORE.
  - intros [inputs [value [_ [_ STORE]]]]; exists value; exact STORE.
  - intros [inputs [value [_ [_ STORE]]]]; exists value; exact STORE.
Qed.
Lemma memory_store_valid_pointer chunk before block offset value after pointer index :
  Mem.store chunk before block offset value = Some after ->
  (Mem.valid_pointer before pointer index = true <-> Mem.valid_pointer after pointer index = true).
Proof.
  intro STORE; rewrite !Mem.valid_pointer_nonempty_perm; split;
    [eapply Mem.perm_store_1|eapply Mem.perm_store_2]; exact STORE.
Qed.
Lemma memory_mode_base_valid mode shape block before after :
  mode_physical mode shape block 0 0 before after -> Mem.valid_pointer before block 0 = true.
Proof.
  intro RUN; destruct (@memory_mode_physical_store mode shape block 0 0 before after RUN) as [value STORE].
  replace (4*(0*rectangle_stride shape+0)) with 0 in STORE by ring.
  apply Mem.valid_pointer_nonempty_perm.
  pose proof (@Mem.store_valid_access_3 _ _ _ _ _ _ STORE) as ACCESS.
  destruct ACCESS as [PERMISSION ALIGN].
  eapply Mem.perm_implies; [apply PERMISSION; change (0 <= 0 < 4); lia|constructor].
Qed.

Lemma memory_cross_physical_store shape write_block read_block i j before after :
  memory_action_run (memory_cross_action shape write_block read_block i j) before after ->
  exists value, Mem.store Mint32 before write_block (4*(i*rectangle_stride shape+j)) value = Some after.
Proof. intros [inputs [value [_ [_ STORE]]]]; exists value; exact STORE. Qed.
Lemma memory_cross_base_read_valid shape write_block read_block before after :
  memory_action_run (memory_cross_action shape write_block read_block 0 0) before after ->
  Mem.valid_pointer before read_block 0 = true.
Proof.
  intros [inputs [value [LOAD [_ STORE]]]].
  unfold memory_cross_action in LOAD; cbn in LOAD.
  change (match Mem.load Mint32 before read_block (4*(0*rectangle_stride shape+0)) with
    | Some old => Some [old] | None => None end = Some inputs) in LOAD.
  replace (4*(0*rectangle_stride shape+0)) with 0 in LOAD by ring.
  destruct (Mem.load Mint32 before read_block 0) eqn:READ; [|discriminate].
  apply Mem.valid_pointer_nonempty_perm.
  pose proof (@Mem.load_valid_access _ _ _ _ _ READ) as [PERMISSION ALIGN].
  eapply Mem.perm_implies; [apply PERMISSION; change (0 <= 0 < 4); lia|constructor].
Qed.
Lemma memory_copy_physical_store shape write_block read_block i j before after :
  memory_action_run (memory_copy_action shape write_block read_block i j) before after ->
  exists value, Mem.store Mint32 before write_block (4*(i*rectangle_stride shape+j)) value = Some after.
Proof. intros [inputs [value [_ [_ STORE]]]]; exists value; exact STORE. Qed.
Lemma memory_copy_base_read_valid shape write_block read_block before after :
  memory_action_run (memory_copy_action shape write_block read_block 0 0) before after ->
  Mem.valid_pointer before read_block 0 = true.
Proof.
  intros [inputs [value [LOAD [_ STORE]]]].
  unfold memory_copy_action in LOAD; cbn in LOAD.
  change (match Mem.load Mint32 before read_block (4*(0*rectangle_stride shape+0)) with
    | Some old => Some [old] | None => None end = Some inputs) in LOAD.
  replace (4*(0*rectangle_stride shape+0)) with 0 in LOAD by ring.
  destruct (Mem.load Mint32 before read_block 0) eqn:READ; [|discriminate].
  apply Mem.valid_pointer_nonempty_perm.
  pose proof (@Mem.load_valid_access _ _ _ _ _ READ) as [PERMISSION ALIGN].
  eapply Mem.perm_implies; [apply PERMISSION; change (0 <= 0 < 4); lia|constructor].
Qed.
Lemma named_operation_physical_store ge locals operation i j before after :
  named_operation_physical ge locals i j operation before after ->
  exists block value, Mem.store Mint32 before block
    (4*(i*rectangle_stride (named_operation_shape operation)+j)) value = Some after.
Proof.
  destruct operation as [mode shape array|shape write_array read_array|shape write_array read_array]; cbn.
  - intros [block [_ RUN]]; destruct (@memory_mode_physical_store _ _ _ _ _ _ _ RUN) as [value STORE].
    exists block,value; exact STORE.
  - intros [write_block [read_block [_ [_ RUN]]]];
    destruct (@memory_cross_physical_store _ _ _ _ _ _ _ RUN) as [value STORE].
    exists write_block,value; exact STORE.
  - intros [write_block [read_block [_ [_ RUN]]]];
    destruct (@memory_copy_physical_store _ _ _ _ _ _ _ RUN) as [value STORE].
    exists write_block,value; exact STORE.
Qed.
Lemma named_operation_base_bindings base ge locals operation before after :
  named_operation_layout base operation ->
  named_operation_physical ge locals 0 0 operation before after ->
  forall array, In array (named_operation_arrays operation) ->
  exists block, rect_array_binding base ge locals array block /\ Mem.valid_pointer before block 0 = true.
Proof.
  intros [EXTENT STRIDE]; destruct operation as [mode shape array|shape write_array read_array|shape write_array read_array];
    cbn in EXTENT,STRIDE |- *.
  - intros [block [BINDING RUN]] variable [SAME|BAD]; [subst variable|contradiction].
    exists block; split.
    + unfold rect_array_binding,rect_array_type in *; rewrite EXTENT in BINDING; exact BINDING.
    + eapply memory_mode_base_valid; exact RUN.
  - intros [write_block [read_block [WRITE [READ RUN]]]] variable [SAME|[SAME|BAD]];
      [subst variable|subst variable|contradiction].
    + exists write_block; split.
      * unfold rect_array_binding,rect_array_type in *; rewrite EXTENT in WRITE; exact WRITE.
      * destruct (@memory_cross_physical_store _ _ _ _ _ _ _ RUN) as [value STORE].
        replace (4*(0*rectangle_stride shape+0)) with 0 in STORE by ring.
        apply Mem.valid_pointer_nonempty_perm.
        pose proof (@Mem.store_valid_access_3 _ _ _ _ _ _ STORE) as [PERMISSION ALIGN].
        eapply Mem.perm_implies; [apply PERMISSION; change (0 <= 0 < 4); lia|constructor].
    + exists read_block; split.
      * unfold rect_array_binding,rect_array_type in *; rewrite EXTENT in READ; exact READ.
      * eapply memory_cross_base_read_valid; exact RUN.
  - intros [write_block [read_block [WRITE [READ RUN]]]] variable [SAME|[SAME|BAD]];
      [subst variable|subst variable|contradiction].
    + exists write_block; split.
      * unfold rect_array_binding,rect_array_type in *; rewrite EXTENT in WRITE; exact WRITE.
      * destruct (@memory_copy_physical_store _ _ _ _ _ _ _ RUN) as [value STORE].
        replace (4*(0*rectangle_stride shape+0)) with 0 in STORE by ring.
        apply Mem.valid_pointer_nonempty_perm.
        pose proof (@Mem.store_valid_access_3 _ _ _ _ _ _ STORE) as [PERMISSION ALIGN].
        eapply Mem.perm_implies; [apply PERMISSION; change (0 <= 0 < 4); lia|constructor].
    + exists read_block; split.
      * unfold rect_array_binding,rect_array_type in *; rewrite EXTENT in READ; exact READ.
      * eapply memory_copy_base_read_valid; exact RUN.
Qed.
Lemma named_array_operations_bindings base ge locals operations before after :
  Forall (named_operation_layout base) operations ->
  named_array_operations_physical ge locals 0 0 operations before after ->
  forall array, In array (flat_map named_operation_arrays operations) ->
  exists block, rect_array_binding base ge locals array block /\ Mem.valid_pointer before block 0 = true.
Proof.
  intro LAYOUTS; revert before after; induction LAYOUTS as [|operation operations LAYOUT REST IH];
    intros before after RUN array MEMBER; inversion RUN; subst.
  - contradiction.
  - cbn in MEMBER; apply in_app_or in MEMBER; destruct MEMBER as [MEMBER|MEMBER].
    + eapply named_operation_base_bindings; eassumption.
    + match goal with TAIL : named_array_operations_physical _ _ _ _ _ _ _ |- _ =>
        destruct (IH _ _ TAIL array MEMBER) as [other [BINDING POINTER]] end.
      exists other; split; [exact BINDING|].
      match goal with HEAD : named_operation_physical _ _ _ _ _ _ _ |- _ =>
        destruct (@named_operation_physical_store _ _ _ _ _ _ _ HEAD) as [block [value STORE]];
        apply (proj2 (@memory_store_valid_pointer _ _ _ _ _ _ _ _ STORE)); exact POINTER end.
Qed.

Lemma named_array_entries_exist base ge locals memory arrays :
  rectangle_layout_valid base ->
  (forall array, In array arrays -> exists block,
    rect_array_binding base ge locals array block /\ Mem.valid_pointer memory block 0 = true) ->
  exists entries, Forall2 (memory_descriptor_binding ge locals)
      (map (fun array => MemoryArrayDescriptor array array base) arrays) entries /\
    map memory_array_id entries = arrays /\
    Forall (fun entry => Mem.valid_pointer memory (memory_array_block entry) 0 = true) entries.
Proof.
  intros VALID BINDINGS; induction arrays as [|array arrays IH].
  - exists []; split; [constructor|split; [reflexivity|constructor]].
  - destruct (BINDINGS array ltac:(cbn; auto)) as [block [BINDING POINTER]].
    destruct (IH ltac:(intros id MEMBER; apply BINDINGS; cbn; auto)) as [entries [RELATED [IDS POINTERS]]].
    exists (MemoryArrayEntry array block (rectangle_extent base)::entries); split.
    + constructor; [unfold memory_descriptor_binding; cbn; split; [reflexivity|];
        split; [reflexivity|]; split; assumption|exact RELATED].
    + split; [cbn; rewrite IDS; reflexivity|constructor; assumption].
Qed.
Theorem named_array_operations_registry base operations ge locals before after :
  rectangle_layout_valid base -> Forall (named_operation_layout base) operations ->
  named_array_operations_physical ge locals 0 0 operations before after ->
  exists entries,
    Forall2 (memory_descriptor_binding ge locals) (named_array_descriptors base operations) entries /\
    NoDup (map memory_array_id entries) /\
    Forall (fun entry => Mem.valid_pointer before (memory_array_block entry) 0 = true) entries.
Proof.
  intros VALID LAYOUTS RUN.
  destruct (@named_array_entries_exist base ge locals before
    (nodup Pos.eq_dec (flat_map named_operation_arrays operations)) VALID
    ltac:(intros array MEMBER; apply nodup_In in MEMBER;
      eapply named_array_operations_bindings; eauto)) as [entries [RELATED [IDS POINTERS]]].
  exists entries; split; [exact RELATED|split; [rewrite IDS; apply NoDup_nodup|exact POINTERS]].
Qed.

Lemma named_array_registry_variable base operations entries ge locals array :
  Forall2 (memory_descriptor_binding ge locals) (named_array_descriptors base operations) entries ->
  In array (flat_map named_operation_arrays operations) ->
  exists entry, In entry entries /\ memory_array_id entry = array /\
    memory_array_extent entry = rectangle_extent base /\
    rect_array_binding base ge locals array (memory_array_block entry).
Proof.
  intros RELATED MEMBER.
  assert (IN : In (MemoryArrayDescriptor array array base) (named_array_descriptors base operations)).
  { apply in_map_iff; exists array; split; [reflexivity|]. apply nodup_In; exact MEMBER. }
  clear MEMBER; revert IN; induction RELATED as [|descriptor entry descriptors entries BINDING REST IH];
    intro IN; [contradiction|].
  cbn in IN; destruct IN as [SAME|IN].
  - subst descriptor; destruct BINDING as [ID [EXTENT [VALID ARRAY]]]; cbn in ID,EXTENT,ARRAY.
    exists entry; split; [cbn; auto|]; split; [exact ID|]; split; assumption.
  - destruct (IH IN) as [other [MEMBER [ID [EXTENT ARRAY]]]].
    exists other; split; [cbn; auto|]; split; [exact ID|]; split; assumption.
Qed.
Lemma named_operation_registry_execution base operation entries ge locals i j before after :
  NoDup (map memory_array_id entries) -> named_operation_layout base operation ->
  (forall array, In array (named_operation_arrays operation) ->
    exists entry, In entry entries /\ memory_array_id entry = array /\
      memory_array_extent entry = rectangle_extent base /\
      rect_array_binding base ge locals array (memory_array_block entry)) ->
  0 <= i*rectangle_stride base+j < rectangle_extent base ->
  0 <= i*rectangle_stride base < rectangle_extent base ->
  (named_operation_physical ge locals i j operation before after <->
   memory_point (named_operation_instruction operation) i j
     (RuntimeState (memory_array_registry entries) before)
     (RuntimeState (memory_array_registry entries) after)).
Proof.
  intros UNIQUE [EXTENT STRIDE] ARRAYS INDEX READ_INDEX.
  destruct operation as [mode shape array|shape write_array read_array|shape write_array read_array]; cbn in EXTENT,STRIDE,ARRAYS |- *.
  - destruct (ARRAYS array ltac:(cbn; auto)) as [entry [ENTRY [ID [ENTRY_EXTENT ARRAY]]]].
    assert (BINDING : rect_array_binding shape ge locals array (memory_array_block entry)).
    { unfold rect_array_binding,rect_array_type; rewrite EXTENT; exact ARRAY. }
    rewrite <- ID.
    rewrite <- (@memory_mode_registry_execution entries entry mode shape i j before after UNIQUE ENTRY
      ltac:(rewrite EXTENT; exact ENTRY_EXTENT)
      ltac:(rewrite EXTENT,STRIDE; exact INDEX)
      ltac:(rewrite EXTENT,STRIDE; exact READ_INDEX)).
    split.
    + intros [block [ORIGINAL POINT]].
      rewrite ID in ORIGINAL; assert (SAME : block = memory_array_block entry)
        by (eapply rect_array_binding_unique; eauto); subst block; exact POINT.
    + intro POINT; exists (memory_array_block entry); split; [rewrite ID; exact BINDING|exact POINT].
  - destruct (ARRAYS write_array ltac:(cbn; auto)) as [write_entry [WRITE_ENTRY [WRITE_ID [WRITE_EXTENT WRITE_ARRAY]]]].
    destruct (ARRAYS read_array ltac:(cbn; auto)) as [read_entry [READ_ENTRY [READ_ID [READ_EXTENT READ_ARRAY]]]].
    assert (WRITE_BINDING : rect_array_binding shape ge locals write_array (memory_array_block write_entry)).
    { unfold rect_array_binding,rect_array_type; rewrite EXTENT; exact WRITE_ARRAY. }
    assert (READ_BINDING : rect_array_binding shape ge locals read_array (memory_array_block read_entry)).
    { unfold rect_array_binding,rect_array_type; rewrite EXTENT; exact READ_ARRAY. }
    rewrite <- WRITE_ID,<- READ_ID.
    rewrite (@memory_cross_registry_execution entries write_entry read_entry shape i j before after UNIQUE
      WRITE_ENTRY READ_ENTRY ltac:(rewrite EXTENT; exact WRITE_EXTENT)
      ltac:(rewrite EXTENT; exact READ_EXTENT) ltac:(rewrite EXTENT,STRIDE; exact INDEX)).
    split.
    + intros [write_block [read_block [WRITE [READ POINT]]]].
      rewrite WRITE_ID in WRITE; rewrite READ_ID in READ.
      assert (WRITE_SAME : write_block = memory_array_block write_entry)
        by (eapply rect_array_binding_unique; eauto).
      assert (READ_SAME : read_block = memory_array_block read_entry)
        by (eapply rect_array_binding_unique; eauto).
      subst write_block read_block; exact POINT.
    + intro POINT; exists (memory_array_block write_entry),(memory_array_block read_entry).
      split; [rewrite WRITE_ID; exact WRITE_BINDING|]; split; [rewrite READ_ID; exact READ_BINDING|exact POINT].
  - destruct (ARRAYS write_array ltac:(cbn; auto)) as [write_entry [WRITE_ENTRY [WRITE_ID [WRITE_EXTENT WRITE_ARRAY]]]].
    destruct (ARRAYS read_array ltac:(cbn; auto)) as [read_entry [READ_ENTRY [READ_ID [READ_EXTENT READ_ARRAY]]]].
    assert (WRITE_BINDING : rect_array_binding shape ge locals write_array (memory_array_block write_entry)).
    { unfold rect_array_binding,rect_array_type; rewrite EXTENT; exact WRITE_ARRAY. }
    assert (READ_BINDING : rect_array_binding shape ge locals read_array (memory_array_block read_entry)).
    { unfold rect_array_binding,rect_array_type; rewrite EXTENT; exact READ_ARRAY. }
    rewrite <- WRITE_ID,<- READ_ID.
    rewrite (@memory_copy_registry_execution entries write_entry read_entry shape i j before after UNIQUE
      WRITE_ENTRY READ_ENTRY ltac:(rewrite EXTENT; exact WRITE_EXTENT)
      ltac:(rewrite EXTENT; exact READ_EXTENT) ltac:(rewrite EXTENT,STRIDE; exact INDEX)).
    split.
    + intros [write_block [read_block [WRITE [READ POINT]]]].
      rewrite WRITE_ID in WRITE; rewrite READ_ID in READ.
      assert (WRITE_SAME : write_block = memory_array_block write_entry)
        by (eapply rect_array_binding_unique; eauto).
      assert (READ_SAME : read_block = memory_array_block read_entry)
        by (eapply rect_array_binding_unique; eauto).
      subst write_block read_block; exact POINT.
    + intro POINT; exists (memory_array_block write_entry),(memory_array_block read_entry).
      split; [rewrite WRITE_ID; exact WRITE_BINDING|]; split; [rewrite READ_ID; exact READ_BINDING|exact POINT].
Qed.
Print Assumptions named_array_operations_registry.

Theorem named_array_operations_point_execution base universe entries ge locals i j operations :
  Forall2 (memory_descriptor_binding ge locals) (named_array_descriptors base universe) entries ->
  NoDup (map memory_array_id entries) -> Forall (named_operation_layout base) operations ->
  Forall (fun operation => In operation universe) operations ->
  0 <= i*rectangle_stride base+j < rectangle_extent base ->
  0 <= i*rectangle_stride base < rectangle_extent base ->
  forall before after,
  (named_array_operations_physical ge locals i j operations before after <->
   memory_sequence_point (map named_operation_instruction operations) i j
     (RuntimeState (memory_array_registry entries) before)
     (RuntimeState (memory_array_registry entries) after)).
Proof.
  intros ARRAYS UNIQUE LAYOUTS; induction LAYOUTS as [|operation operations LAYOUT LAYOUTS IH];
    intros MEMBERS INDEX READ_INDEX before after; unfold memory_sequence_point; cbn [map].
  - split; intro RUN; inversion RUN; subst; constructor.
  - inversion MEMBERS as [|head tail MEMBER REST]; subst.
    assert (BINDINGS : forall array, In array (named_operation_arrays operation) ->
      exists entry, In entry entries /\ memory_array_id entry = array /\
        memory_array_extent entry = rectangle_extent base /\
        rect_array_binding base ge locals array (memory_array_block entry)).
    { intros array IN; eapply named_array_registry_variable; [exact ARRAYS|].
      apply in_flat_map; exists operation; split; assumption. }
    split; intro RUN.
    + inversion RUN; subst.
      eapply Iter.IProgress with (st2 := RuntimeState (memory_array_registry entries) middle).
      * apply (proj1 (@named_operation_registry_execution base operation entries ge locals i j before middle
          UNIQUE LAYOUT BINDINGS INDEX READ_INDEX)); assumption.
      * apply IH; assumption.
    + inversion RUN; subst.
      match goal with POINT : memory_point _ _ _ _ ?middle |- _ =>
        destruct middle as [locations middle_memory];
        assert (LOCATIONS : locations = memory_array_registry entries)
          by (exact (@memory_point_locations _ i j _ _ POINT)); subst locations end.
      eapply named_array_operations_physical_cons with (middle := middle_memory).
      * apply (proj2 (@named_operation_registry_execution base operation entries ge locals i j before middle_memory
          UNIQUE LAYOUT BINDINGS INDEX READ_INDEX)); assumption.
      * apply IH; assumption.
Qed.
Print Assumptions named_operation_registry_execution.
Print Assumptions named_array_operations_point_execution.
