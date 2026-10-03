From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import CompCertMemoryActions CompCertStoreSchedule RectangularIteration
  ClightRectangularStore ClightRectangularRegion ClightRectangularUpdate ClightRectangularRowUpdate
  RectangularMemorySchedule RectangularRowSchedule ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles
  GuardMemoryLoops GuardMemorySequenceLoops GuardMemoryClightRectangles GuardMemoryArrayFamilyBackend
  GuardMemoryMultipleArrays GuardMemoryRegistryBackend GuardMemoryRegistryTransfer GuardMemoryNamedOperations.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition named_array_descriptors base operations :=
  map (fun array => MemoryArrayDescriptor array array base)
    (nodup Pos.eq_dec (map named_operation_array operations)).

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

Lemma named_array_operations_bindings base ge locals operations before after :
  Forall (named_operation_layout base) operations ->
  named_array_operations_physical ge locals 0 0 operations before after ->
  forall array, In array (map named_operation_array operations) ->
  exists block, rect_array_binding base ge locals array block /\ Mem.valid_pointer before block 0 = true.
Proof.
  intro LAYOUTS; revert before after; induction LAYOUTS as [|operation operations LAYOUT REST IH];
    intros before after RUN array MEMBER; inversion RUN; subst.
  - contradiction.
  - cbn in MEMBER; destruct MEMBER as [SAME|MEMBER].
    + subst array; exists block; split.
      * unfold rect_array_binding,rect_array_type in *.
        destruct LAYOUT as [EXTENT STRIDE]; rewrite EXTENT in *; assumption.
      * eapply memory_mode_base_valid; eassumption.
    + match goal with TAIL : named_array_operations_physical _ _ _ _ _ _ _ |- _ =>
        destruct (IH _ _ TAIL array MEMBER) as [other [BINDING POINTER]] end.
      exists other; split; [exact BINDING|].
      match goal with HEAD : mode_physical _ _ _ _ _ _ _ |- _ =>
        destruct (@memory_mode_physical_store _ _ _ _ _ _ _ HEAD) as [value STORE];
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
    (nodup Pos.eq_dec (map named_operation_array operations)) VALID
    ltac:(intros array MEMBER; apply nodup_In in MEMBER;
      eapply named_array_operations_bindings; eauto)) as [entries [RELATED [IDS POINTERS]]].
  exists entries; split; [exact RELATED|split; [rewrite IDS; apply NoDup_nodup|exact POINTERS]].
Qed.

Lemma named_array_registry_operation base operations entries ge locals operation :
  Forall2 (memory_descriptor_binding ge locals) (named_array_descriptors base operations) entries ->
  In operation operations ->
  exists entry, In entry entries /\ memory_array_id entry = named_operation_array operation /\
    memory_array_extent entry = rectangle_extent base /\
    rect_array_binding base ge locals (named_operation_array operation) (memory_array_block entry).
Proof.
  intros RELATED MEMBER.
  assert (IN : In (MemoryArrayDescriptor (named_operation_array operation) (named_operation_array operation) base)
    (named_array_descriptors base operations)).
  { apply in_map_iff; exists (named_operation_array operation); split; [reflexivity|].
    apply nodup_In; apply in_map; exact MEMBER. }
  clear MEMBER; revert IN; induction RELATED as [|descriptor entry descriptors entries BINDING REST IH];
    intro IN; [contradiction|].
  cbn in IN; destruct IN as [SAME|IN].
  - subst descriptor; destruct BINDING as [ID [EXTENT [VALID ARRAY]]]; cbn in ID,EXTENT,ARRAY.
    exists entry; split; [cbn; auto|]; split; [exact ID|]; split; assumption.
  - destruct (IH IN) as [other [MEMBER [ID [EXTENT ARRAY]]]].
    exists other; split; [cbn; auto|]; split; [exact ID|]; split; assumption.
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
    intros MEMBERS INDEX READ_INDEX before after; unfold memory_sequence_point; cbn [map];
    split; intro RUN.
  - inversion RUN; subst; constructor.
  - inversion RUN; subst; constructor.
  - inversion MEMBERS as [|head tail MEMBER REST]; subst.
    destruct (@named_array_registry_operation base universe entries ge locals operation ARRAYS MEMBER)
      as [entry [ENTRY [ID [EXTENT ARRAY]]]].
    destruct LAYOUT as [SHAPE_EXTENT SHAPE_STRIDE].
    assert (BINDING : rect_array_binding (named_operation_shape operation) ge locals
      (named_operation_array operation) (memory_array_block entry)).
    { unfold rect_array_binding,rect_array_type; rewrite SHAPE_EXTENT; exact ARRAY. }
    inversion RUN; subst.
    match goal with ORIGINAL : rect_array_binding _ _ _ _ ?other |- _ =>
      assert (SAME : other = memory_array_block entry) by
        (eapply rect_array_binding_unique; [exact ORIGINAL|exact BINDING]); subst other end.
    eapply Iter.IProgress with (st2 := RuntimeState (memory_array_registry entries) middle).
    + unfold named_operation_instruction; rewrite <- ID.
      apply (proj1 (@memory_mode_registry_execution entries entry (named_operation_mode operation)
        (named_operation_shape operation) i j before middle UNIQUE ENTRY
        ltac:(rewrite SHAPE_EXTENT; exact EXTENT)
        ltac:(rewrite SHAPE_EXTENT,SHAPE_STRIDE; exact INDEX)
        ltac:(rewrite SHAPE_EXTENT,SHAPE_STRIDE; exact READ_INDEX))); assumption.
    + apply IH; assumption.
  - inversion MEMBERS as [|head tail MEMBER REST]; subst.
    destruct (@named_array_registry_operation base universe entries ge locals operation ARRAYS MEMBER)
      as [entry [ENTRY [ID [EXTENT ARRAY]]]].
    destruct LAYOUT as [SHAPE_EXTENT SHAPE_STRIDE].
    inversion RUN; subst.
    match goal with POINT : memory_point _ _ _ _ ?middle |- _ =>
      destruct middle as [locations middle_memory];
      assert (LOCATIONS : locations = memory_array_registry entries)
        by (exact (@memory_point_locations _ i j _ _ POINT)); subst locations end.
    eapply named_array_operations_physical_cons with (block := memory_array_block entry)
      (middle := middle_memory).
    + unfold rect_array_binding,rect_array_type; rewrite SHAPE_EXTENT; exact ARRAY.
    + apply (proj2 (@memory_mode_registry_execution entries entry (named_operation_mode operation)
        (named_operation_shape operation) i j before middle_memory UNIQUE ENTRY
        ltac:(rewrite SHAPE_EXTENT; exact EXTENT)
        ltac:(rewrite SHAPE_EXTENT,SHAPE_STRIDE; exact INDEX)
        ltac:(rewrite SHAPE_EXTENT,SHAPE_STRIDE; exact READ_INDEX))).
      rewrite ID; assumption.
    + apply IH; assumption.
Qed.

Print Assumptions named_array_operations_point_execution.
