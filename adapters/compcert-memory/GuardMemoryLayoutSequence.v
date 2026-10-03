From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightFiniteRegion ClightStraightLine ClightLoopSyntax ClightRegionProgress ClightRectangularStore ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemorySequenceLoops
  GuardMemoryMultipleArrays GuardMemoryRegistryBackend GuardMemoryNamedRegistrySource GuardMemoryLayoutRegistry
  GuardMemoryLayoutOperations.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Inductive memory_layout_operations_physical ge locals i j : list memory_layout_operation -> mem -> mem -> Prop :=
| LayoutOperationsNil : forall memory, memory_layout_operations_physical ge locals i j [] memory memory
| LayoutOperationsCons : forall operation operations before middle final,
    memory_layout_operation_physical ge locals i j operation before middle ->
    memory_layout_operations_physical ge locals i j operations middle final ->
    memory_layout_operations_physical ge locals i j (operation::operations) before final.
Definition memory_layout_sequence_requests operations := flat_map memory_layout_operation_requests operations.
Lemma memory_layout_sequence_body_normal operations row column body :
  flatten_region body = map (memory_layout_operation_statement row column) operations -> normal_statement body = true.
Proof.
  intro BODY; apply flatten_normal_certificate; rewrite BODY; apply Forall_map,Forall_forall.
  intros; apply memory_layout_operation_normal.
Qed.
Lemma memory_layout_sequence_body_quiet operations row column body :
  flatten_region body = map (memory_layout_operation_statement row column) operations -> quiet_statement body = true.
Proof.
  intro BODY; apply flatten_quiet_certificate; rewrite BODY; apply Forall_map,Forall_forall.
  intros; apply memory_layout_operation_quiet.
Qed.
Lemma memory_layout_sequence_body_writes operations row column body :
  flatten_region body = map (memory_layout_operation_statement row column) operations -> writes_only [] body.
Proof.
  intro BODY; apply flatten_writes_certificate; rewrite BODY; apply Forall_map,Forall_forall.
  intros; apply memory_layout_operation_writes.
Qed.
Lemma memory_layout_sequence_tail_inverse operations row column fe ge locals i j temps memory after final :
  Forall (fun operation => memory_layout_indices (memory_layout_operation_requests operation) i j) operations ->
  temps ! row = Some (Vint (Int.repr i)) -> temps ! column = Some (Vint (Int.repr j)) ->
  tail_execution fe ge locals (map (memory_layout_operation_statement row column) operations)
    temps memory after final -> memory_layout_operations_physical ge locals i j operations memory final /\ after = temps.
Proof.
  intro INDICES; revert temps memory after final; induction INDICES as [|operation operations INDEX INDICES IH];
    intros temps memory after final ROW COLUMN RUN; cbn in RUN; inversion RUN; subst.
  - split; [constructor|reflexivity].
  - match goal with HEAD : exec_stmt _ _ _ _ _ (memory_layout_operation_statement _ _ _) _ _ _ _ |- _ =>
      destruct (@memory_layout_operation_clight_inverse operation row column fe ge locals i j temps memory _ _ INDEX ROW COLUMN HEAD)
        as [POINT TEMPS]; subst end.
    match goal with TAIL : tail_execution _ _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ _ _ ROW COLUMN TAIL) as [REST EXIT] end.
    split; [econstructor; eauto|exact EXIT].
Qed.
Lemma memory_layout_sequence_initial_bindings ge locals operations before after :
  memory_layout_operations_physical ge locals 0 0 operations before after ->
  forall descriptor, In descriptor (memory_layout_sequence_requests operations) ->
    exists block, rect_array_binding (memory_descriptor_shape descriptor) ge locals (memory_descriptor_variable descriptor) block /\
      Mem.valid_pointer before block 0 = true.
Proof.
  intro RUN; induction RUN as [memory|operation operations before middle final HEAD TAIL IH];
    intros descriptor MEMBER; [contradiction|].
  cbn [memory_layout_sequence_requests flat_map] in MEMBER; apply in_app_or in MEMBER as [MEMBER|MEMBER].
  - eapply memory_layout_operation_initial_bindings; eassumption.
  - destruct (IH descriptor MEMBER) as [block [BINDING POINTER]].
    exists block; split; [exact BINDING|].
    destruct (@memory_layout_operation_physical_store ge locals operation 0 0 before middle HEAD) as [write [value STORE]].
    apply (proj2 (@memory_store_valid_pointer _ _ _ _ _ _ _ _ STORE)); exact POINTER.
Qed.
Print Assumptions memory_layout_sequence_tail_inverse.
Print Assumptions memory_layout_sequence_initial_bindings.

Theorem memory_layout_sequence_registry ge locals operations before after :
  Forall (fun descriptor => rectangle_layout_valid (memory_descriptor_shape descriptor)) (memory_layout_sequence_requests operations) ->
  memory_layout_operations_physical ge locals 0 0 operations before after ->
  exists entries, Forall2 (memory_descriptor_binding ge locals)
      (memory_unique_descriptors (memory_layout_sequence_requests operations)) entries /\
    NoDup (map memory_array_id entries) /\
    Forall (fun entry => Mem.valid_pointer before (memory_array_block entry) 0 = true) entries.
Proof.
  intros VALID RUN; apply memory_descriptor_entries_exist.
  - apply Forall_forall; intros descriptor MEMBER; apply memory_unique_descriptors_member in MEMBER.
    apply Forall_forall with (x := descriptor) in VALID; assumption.
  - apply memory_unique_descriptor_ids.
  - intros descriptor MEMBER; apply memory_unique_descriptors_member in MEMBER.
    eapply memory_layout_sequence_initial_bindings; eassumption.
Qed.
Lemma memory_layout_sequence_cover descriptors operations :
  memory_descriptors_cover descriptors (memory_layout_sequence_requests operations) ->
  Forall (fun operation => memory_descriptors_cover descriptors (memory_layout_operation_requests operation)) operations.
Proof.
  intro COVER; apply Forall_forall; intros operation MEMBER; apply Forall_forall; intros descriptor REQUEST.
  apply Forall_forall with (x := descriptor) in COVER.
  - exact COVER.
  - apply in_flat_map; exists operation; split; assumption.
Qed.
Theorem memory_layout_sequence_point_execution descriptors entries ge locals i j operations :
  Forall2 (memory_descriptor_binding ge locals) descriptors entries ->
  NoDup (map memory_array_id entries) ->
  Forall (fun operation => memory_descriptors_cover descriptors (memory_layout_operation_requests operation)) operations ->
  Forall (fun operation => memory_layout_indices (memory_layout_operation_requests operation) i j) operations ->
  forall before after,
    (memory_layout_operations_physical ge locals i j operations before after <->
      memory_sequence_point (map memory_layout_operation_instruction operations) i j
        (RuntimeState (memory_array_registry entries) before) (RuntimeState (memory_array_registry entries) after)).
Proof.
  intros ARRAYS UNIQUE COVERS; induction COVERS as [|operation operations COVER COVERS IH];
    intros INDICES before after; unfold memory_sequence_point; cbn [map].
  - split; intro RUN; inversion RUN; subst; constructor.
  - inversion INDICES as [|head tail INDEX REST]; subst.
    split; intro RUN.
    + inversion RUN; subst.
      eapply Iter.IProgress with (st2 := RuntimeState (memory_array_registry entries) middle).
      * apply (proj1 (@memory_layout_operation_registry_execution descriptors entries ge locals operation i j before middle
          ARRAYS COVER UNIQUE INDEX)); assumption.
      * apply IH; assumption.
    + inversion RUN; subst.
      match goal with POINT : memory_point _ _ _ _ ?middle |- _ =>
        destruct middle as [locations middle_memory];
        assert (LOCATIONS : locations = memory_array_registry entries)
          by (exact (@memory_point_locations _ i j _ _ POINT)); subst locations end.
      eapply LayoutOperationsCons with (middle := middle_memory).
      * apply (proj2 (@memory_layout_operation_registry_execution descriptors entries ge locals operation i j before middle_memory
          ARRAYS COVER UNIQUE INDEX)); assumption.
      * apply IH; assumption.
Qed.
Print Assumptions memory_layout_sequence_registry.
Print Assumptions memory_layout_sequence_point_execution.
