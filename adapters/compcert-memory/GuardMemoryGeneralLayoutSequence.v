From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightFiniteRegion ClightStraightLine ClightLoopSyntax ClightRegionProgress ClightRectangularStore ClightRectangularGuard ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemorySequenceLoops
  GuardMemoryMultipleArrays GuardMemoryRegistryBackend GuardMemoryNamedRegistrySource GuardMemoryLayoutRegistry
  GuardMemoryGeneralLayoutOperations.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Inductive memory_general_operations_physical ge locals i j : list memory_general_layout_operation -> mem -> mem -> Prop :=
| GeneralOperationsNil : forall memory, memory_general_operations_physical ge locals i j [] memory memory
| GeneralOperationsCons : forall operation operations before middle final,
    memory_general_layout_physical ge locals i j operation before middle ->
    memory_general_operations_physical ge locals i j operations middle final ->
    memory_general_operations_physical ge locals i j (operation::operations) before final.
Definition memory_general_sequence_requests operations := flat_map memory_general_layout_requests operations.
Lemma memory_general_sequence_body_normal operations row column body :
  flatten_region body = map (memory_general_layout_statement row column) operations -> normal_statement body = true.
Proof.
  intro BODY; apply flatten_normal_certificate; rewrite BODY; apply Forall_map,Forall_forall.
  intros; apply memory_general_layout_normal.
Qed.
Lemma memory_general_sequence_body_quiet operations row column body :
  flatten_region body = map (memory_general_layout_statement row column) operations -> quiet_statement body = true.
Proof.
  intro BODY; apply flatten_quiet_certificate; rewrite BODY; apply Forall_map,Forall_forall.
  intros; apply memory_general_layout_quiet.
Qed.
Lemma memory_general_sequence_body_writes operations row column body :
  flatten_region body = map (memory_general_layout_statement row column) operations -> writes_only [] body.
Proof.
  intro BODY; apply flatten_writes_certificate; rewrite BODY; apply Forall_map,Forall_forall.
  intros; apply memory_general_layout_writes.
Qed.
Lemma memory_general_sequence_tail_inverse base operations row column fe ge locals i j temps memory after final :
  rectangle_layout_valid base -> row <> column ->
  Forall (memory_general_layout_valid base row column) operations ->
  0 <= i < rectangle_outer_limit base -> 0 <= j < rectangle_stride base ->
  temps ! row = Some (Vint (Int.repr i)) -> temps ! column = Some (Vint (Int.repr j)) ->
  tail_execution fe ge locals (map (memory_general_layout_statement row column) operations)
    temps memory after final -> memory_general_operations_physical ge locals i j operations memory final /\ after = temps.
Proof.
  intros VALID DISTINCT CERT I J; revert temps memory after final; induction CERT as [|operation operations HEAD CERT IH];
    intros temps memory after final ROW COLUMN RUN; cbn in RUN; inversion RUN; subst.
  - split; [constructor|reflexivity].
  - match goal with POINT : exec_stmt _ _ _ _ _ (memory_general_layout_statement _ _ _) _ _ _ _ |- _ =>
      destruct (@memory_general_layout_clight_inverse base row column operation fe ge locals temps memory _ _ i j
        VALID DISTINCT HEAD I J ROW COLUMN POINT) as [ACT TEMPS]; subst end.
    match goal with TAIL : tail_execution _ _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ _ _ ROW COLUMN TAIL) as [REST EXIT] end.
    split; [econstructor; eauto|exact EXIT].
Qed.
Lemma memory_general_sequence_initial_bindings base row column ge locals operations before after :
  Forall (memory_general_layout_valid base row column) operations ->
  memory_general_operations_physical ge locals 0 0 operations before after ->
  forall descriptor, In descriptor (memory_general_sequence_requests operations) ->
    exists block, rect_array_binding (memory_descriptor_shape descriptor) ge locals (memory_descriptor_variable descriptor) block /\
      Mem.valid_pointer before block 0 = true.
Proof.
  intros CERT RUN; revert CERT; induction RUN as [memory|operation operations before middle final HEAD TAIL IH];
    intros CERT descriptor MEMBER; [contradiction|].
  inversion CERT as [|head tail HC TC]; subst.
  cbn [memory_general_sequence_requests flat_map] in MEMBER; apply in_app_or in MEMBER as [MEMBER|MEMBER].
  - eapply memory_general_layout_initial_bindings; eassumption.
  - destruct (IH TC descriptor MEMBER) as [block [BINDING POINTER]].
    exists block; split; [exact BINDING|].
    destruct (@memory_general_layout_physical_store ge locals operation 0 0 before middle HEAD) as [write [offset [value STORE]]].
    apply (proj2 (@memory_store_valid_pointer _ _ _ _ _ _ _ _ STORE)); exact POINTER.
Qed.
Lemma memory_general_descriptor_valid base row column operation :
  memory_general_layout_valid base row column operation ->
  Forall (fun descriptor => rectangle_layout_valid (memory_descriptor_shape descriptor)) (memory_general_layout_requests operation).
Proof.
  destruct operation as [operation|write read]; cbn; intro CERT.
  - eapply Forall_impl; [|exact CERT]; intros descriptor [VALID RANGE]; exact VALID.
  - destruct CERT as [[WVALID REST] [RVALID REST']]; constructor; [exact WVALID|]; constructor; [exact RVALID|constructor].
Qed.
Theorem memory_general_sequence_registry base row column ge locals operations before after :
  Forall (memory_general_layout_valid base row column) operations ->
  memory_general_operations_physical ge locals 0 0 operations before after ->
  exists entries, Forall2 (memory_descriptor_binding ge locals)
      (memory_unique_descriptors (memory_general_sequence_requests operations)) entries /\
    NoDup (map memory_array_id entries) /\
    Forall (fun entry => Mem.valid_pointer before (memory_array_block entry) 0 = true) entries.
Proof.
  intros CERT RUN; apply memory_descriptor_entries_exist.
  - apply Forall_forall; intros descriptor MEMBER; apply memory_unique_descriptors_member in MEMBER.
    apply in_flat_map in MEMBER as [operation [MEMBER REQUEST]].
    apply Forall_forall with (x := operation) in CERT; [|exact MEMBER].
    pose proof (@memory_general_descriptor_valid base row column operation CERT) as VALID.
    apply Forall_forall with (x := descriptor) in VALID; assumption.
  - apply memory_unique_descriptor_ids.
  - intros descriptor MEMBER; apply memory_unique_descriptors_member in MEMBER.
    eapply memory_general_sequence_initial_bindings; eassumption.
Qed.
Lemma memory_general_sequence_cover descriptors operations :
  memory_descriptors_cover descriptors (memory_general_sequence_requests operations) ->
  Forall (fun operation => memory_descriptors_cover descriptors (memory_general_layout_requests operation)) operations.
Proof.
  intro COVER; apply Forall_forall; intros operation MEMBER; apply Forall_forall; intros descriptor REQUEST.
  apply Forall_forall with (x := descriptor) in COVER.
  - exact COVER.
  - apply in_flat_map; exists operation; split; assumption.
Qed.
Theorem memory_general_sequence_point_execution base row column descriptors entries ge locals i j operations :
  rectangle_layout_valid base ->
  Forall2 (memory_descriptor_binding ge locals) descriptors entries ->
  NoDup (map memory_array_id entries) ->
  Forall (fun operation => memory_descriptors_cover descriptors (memory_general_layout_requests operation)) operations ->
  Forall (memory_general_layout_valid base row column) operations ->
  0 <= i < rectangle_outer_limit base -> 0 <= j < rectangle_stride base ->
  forall before after,
    (memory_general_operations_physical ge locals i j operations before after <->
      memory_sequence_point (map memory_general_layout_instruction operations) i j
        (RuntimeState (memory_array_registry entries) before) (RuntimeState (memory_array_registry entries) after)).
Proof.
  intros VALID ARRAYS UNIQUE COVERS; induction COVERS as [|operation operations COVER COVERS IH];
    intros CERT I J before after; unfold memory_sequence_point; cbn [map].
  - split; intro RUN; inversion RUN; subst; constructor.
  - inversion CERT as [|head tail HEAD REST]; subst.
    split; intro RUN.
    + inversion RUN; subst.
      eapply Iter.IProgress with (st2 := RuntimeState (memory_array_registry entries) middle).
      * apply (proj1 (@memory_general_layout_registry_execution base row column descriptors entries ge locals operation i j before middle
          VALID ARRAYS COVER UNIQUE HEAD I J)); assumption.
      * apply IH; assumption.
    + inversion RUN; subst.
      match goal with POINT : memory_point _ _ _ _ ?middle |- _ =>
        destruct middle as [locations middle_memory];
        assert (LOCATIONS : locations = memory_array_registry entries)
          by (exact (@memory_point_locations _ i j _ _ POINT)); subst locations end.
      eapply GeneralOperationsCons with (middle := middle_memory).
      * apply (proj2 (@memory_general_layout_registry_execution base row column descriptors entries ge locals operation i j before middle_memory
          VALID ARRAYS COVER UNIQUE HEAD I J)); assumption.
      * apply IH; assumption.
Qed.
Print Assumptions memory_general_sequence_registry.
Print Assumptions memory_general_sequence_point_execution.
