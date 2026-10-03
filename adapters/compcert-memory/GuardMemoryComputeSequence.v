From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightFiniteRegion ClightStraightLine ClightLoopSyntax ClightRegionProgress
  ClightRectangularStore ClightRectangularGuard ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemorySequenceLoops
  GuardMemoryMultipleArrays GuardMemoryRegistryBackend GuardMemoryNamedRegistrySource GuardMemoryLayoutRegistry
  GuardMemoryAffineAccessExpressions GuardMemoryAffineAccess GuardMemoryOffsetAccessRanges
  GuardMemorySourceValues GuardMemoryAffineCompute GuardMemoryComputeAnchors.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Inductive memory_compute_sequence_physical ge locals i j : list memory_affine_compute -> mem -> mem -> Prop :=
| ComputeSequenceNil : forall memory, memory_compute_sequence_physical ge locals i j [] memory memory
| ComputeSequenceCons : forall operation operations before middle final,
    memory_affine_compute_physical ge locals i j operation before middle ->
    memory_compute_sequence_physical ge locals i j operations middle final ->
    memory_compute_sequence_physical ge locals i j (operation::operations) before final.
Definition memory_compute_sequence_requests operations := flat_map memory_affine_compute_requests operations.
Definition memory_compute_sequence_anchors operations := flat_map memory_compute_anchors operations.
Lemma memory_compute_sequence_normal operations body :
  flatten_region body = map memory_affine_compute_statement operations -> normal_statement body = true.
Proof.
  intro BODY; apply flatten_normal_certificate; rewrite BODY; apply Forall_map,Forall_forall.
  intros; apply memory_affine_compute_normal.
Qed.
Lemma memory_compute_sequence_quiet operations body :
  flatten_region body = map memory_affine_compute_statement operations -> quiet_statement body = true.
Proof.
  intro BODY; apply flatten_quiet_certificate; rewrite BODY; apply Forall_map,Forall_forall.
  intros; apply memory_affine_compute_quiet.
Qed.
Lemma memory_compute_sequence_writes operations body :
  flatten_region body = map memory_affine_compute_statement operations -> writes_only [] body.
Proof.
  intro BODY; apply flatten_writes_certificate; rewrite BODY; apply Forall_map,Forall_forall.
  intros; apply memory_affine_compute_writes.
Qed.
Lemma memory_compute_sequence_tail_inverse base operations row column fe ge locals i j temps memory after final :
  row <> column -> Forall (memory_affine_compute_valid base row column) operations ->
  0 <= i < rectangle_outer_limit base -> 0 <= j < rectangle_stride base ->
  temps ! row = Some (Vint (Int.repr i)) -> temps ! column = Some (Vint (Int.repr j)) ->
  tail_execution fe ge locals (map memory_affine_compute_statement operations) temps memory after final ->
  memory_compute_sequence_physical ge locals i j operations memory final /\ after = temps.
Proof.
  intros DISTINCT CERT I J; revert temps memory after final; induction CERT as [|operation operations HEAD CERT IH];
    intros temps memory after final ROW COLUMN RUN; cbn in RUN; inversion RUN; subst.
  - split; [constructor|reflexivity].
  - match goal with POINT : exec_stmt _ _ _ _ _ (memory_affine_compute_statement _) _ _ _ _ |- _ =>
      destruct (@memory_affine_compute_inverse base row column operation fe ge locals temps memory _ _ i j
        DISTINCT HEAD I J ROW COLUMN POINT) as [ACT TEMPS]; subst end.
    match goal with TAIL : tail_execution _ _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ _ _ ROW COLUMN TAIL) as [REST EXIT] end.
    split; [econstructor; eauto|exact EXIT].
Qed.
Lemma memory_compute_sequence_anchor_bindings ge locals operations before after :
  memory_compute_sequence_physical ge locals 0 0 operations before after ->
  forall descriptor, In descriptor (memory_compute_sequence_anchors operations) ->
    exists block, rect_array_binding (memory_descriptor_shape descriptor) ge locals
      (memory_descriptor_variable descriptor) block /\ Mem.valid_pointer before block 0 = true.
Proof.
  intro RUN; induction RUN as [memory|operation operations before middle final HEAD TAIL IH];
    intros descriptor MEMBER; [contradiction|].
  cbn [memory_compute_sequence_anchors flat_map] in MEMBER; apply in_app_or in MEMBER as [MEMBER|MEMBER].
  - eapply memory_compute_anchor_bindings; eassumption.
  - destruct (IH descriptor MEMBER) as [block [ARRAY POINTER]]; exists block; split; [exact ARRAY|].
    destruct (@memory_affine_compute_store ge locals 0 0 operation before middle HEAD) as [wb [offset [value STORE]]].
    apply (proj2 (@memory_store_valid_pointer _ _ _ _ _ _ _ _ STORE)); exact POINTER.
Qed.
Lemma memory_compute_request_valid base row column operation :
  memory_affine_compute_valid base row column operation ->
  Forall (fun descriptor => rectangle_layout_valid (memory_descriptor_shape descriptor)) (memory_affine_compute_requests operation).
Proof.
  intros [[WRITE REST] [READS REST']]; unfold memory_affine_compute_requests; cbn; constructor; [exact WRITE|].
  apply Forall_map; eapply Forall_impl; [|exact READS]; intros access [VALID OTHER]; exact VALID.
Qed.
Theorem memory_compute_sequence_registry base row column ge locals operations before after :
  Forall (memory_affine_compute_valid base row column) operations ->
  memory_compute_sequence_physical ge locals 0 0 operations before after ->
  exists entries, Forall2 (memory_descriptor_binding ge locals)
      (memory_unique_descriptors (memory_compute_sequence_anchors operations)) entries /\
    NoDup (map memory_array_id entries) /\
    Forall (fun entry => Mem.valid_pointer before (memory_array_block entry) 0 = true) entries.
Proof.
  intros CERT RUN; apply memory_descriptor_entries_exist.
  - apply Forall_forall; intros descriptor MEMBER; apply memory_unique_descriptors_member in MEMBER.
    apply in_flat_map in MEMBER as [operation [MEMBER ANCHOR]].
    apply memory_compute_anchor_member in ANCHOR.
    apply Forall_forall with (x := operation) in CERT; [|exact MEMBER].
    pose proof (@memory_compute_request_valid base row column operation CERT) as VALID.
    apply Forall_forall with (x := descriptor) in VALID; assumption.
  - apply memory_unique_descriptor_ids.
  - intros descriptor MEMBER; apply memory_unique_descriptors_member in MEMBER.
    eapply memory_compute_sequence_anchor_bindings; eassumption.
Qed.
Lemma memory_compute_sequence_cover descriptors operations :
  memory_descriptors_cover descriptors (memory_compute_sequence_requests operations) ->
  Forall (fun operation => memory_descriptors_cover descriptors (memory_affine_compute_requests operation)) operations.
Proof.
  intro COVER; apply Forall_forall; intros operation MEMBER; apply Forall_forall; intros descriptor REQUEST.
  apply Forall_forall with (x := descriptor) in COVER; [exact COVER|].
  apply in_flat_map; exists operation; split; assumption.
Qed.
Theorem memory_compute_sequence_point_execution base row column descriptors entries ge locals i j operations :
  Forall2 (memory_descriptor_binding ge locals) descriptors entries -> NoDup (map memory_array_id entries) ->
  Forall (fun operation => memory_descriptors_cover descriptors (memory_affine_compute_requests operation)) operations ->
  Forall (memory_affine_compute_valid base row column) operations ->
  0 <= i < rectangle_outer_limit base -> 0 <= j < rectangle_stride base ->
  forall before after,
    (memory_compute_sequence_physical ge locals i j operations before after <->
      memory_sequence_point (map memory_affine_compute_instruction operations) i j
        (RuntimeState (memory_array_registry entries) before) (RuntimeState (memory_array_registry entries) after)).
Proof.
  intros ARRAYS UNIQUE COVERS; induction COVERS as [|operation operations COVER COVERS IH];
    intros CERT I J before after; unfold memory_sequence_point; cbn [map].
  - split; intro RUN; inversion RUN; subst; constructor.
  - inversion CERT as [|head tail HEAD REST]; subst.
    assert (WBOUND : 0 <= memory_index_value (memory_access_index (memory_compute_write operation)) i j <
      rectangle_extent (memory_access_shape (memory_compute_write operation)))
      by (destruct HEAD as [[_ [_ BOUND]] _]; apply BOUND; assumption).
    assert (RBOUNDS : Forall (fun access => 0 <= memory_index_value (memory_access_index access) i j <
      rectangle_extent (memory_access_shape access)) (memory_compute_reads operation)).
    { destruct HEAD as [_ [READS _]]; eapply Forall_impl; [|exact READS]; intros access [_ [_ BOUND]]; apply BOUND; assumption. }
    split; intro RUN.
    + inversion RUN; subst.
      eapply Iter.IProgress with (st2 := RuntimeState (memory_array_registry entries) middle).
      * apply (proj1 (@memory_affine_compute_registry descriptors entries ge locals i j operation before middle
          ARRAYS UNIQUE COVER WBOUND RBOUNDS)); assumption.
      * apply IH; assumption.
    + inversion RUN; subst.
      match goal with POINT : memory_point _ _ _ _ ?middle |- _ =>
        destruct middle as [locations middle_memory];
        assert (LOCATIONS : locations = memory_array_registry entries)
          by (exact (@memory_point_locations _ i j _ _ POINT)); subst locations end.
      eapply ComputeSequenceCons with (middle := middle_memory).
      * apply (proj2 (@memory_affine_compute_registry descriptors entries ge locals i j operation before middle_memory
          ARRAYS UNIQUE COVER WBOUND RBOUNDS)); assumption.
      * apply IH; assumption.
Qed.
Print Assumptions memory_compute_sequence_registry.
Print Assumptions memory_compute_sequence_point_execution.
