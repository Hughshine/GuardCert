From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightFiniteRegion ClightStraightLine ClightLoopSyntax ClightRegionProgress
  ClightRectangularStore ClightRectangularGuard ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemorySequenceLoops
  GuardMemoryMultipleArrays GuardMemoryRegistryBackend GuardMemoryNamedRegistrySource GuardMemoryLayoutRegistry
  GuardMemoryNaryAffineExpressions GuardMemoryNaryAffineAccess GuardMemoryNaryAccessCheck
  GuardMemoryNarySourceValues GuardMemoryNaryCompute GuardMemoryNaryAnchors GuardMemoryNaryLoops GuardMemoryAccessAnchors GuardMemoryNaryRanges.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_nary_point_locations instruction values before after :
  memory_nary_point instruction values before after -> runtime_locations after = runtime_locations before.
Proof. intros [_ [_ [write [reads [_ [_ [SAME RUN]]]]]]]; exact SAME. Qed.
Inductive memory_nary_compute_sequence_physical ge locals values : list memory_nary_compute -> mem -> mem -> Prop :=
| NaryComputeSequenceNil : forall memory, memory_nary_compute_sequence_physical ge locals values [] memory memory
| NaryComputeSequenceCons : forall operation operations before middle final,
    memory_nary_compute_physical ge locals values operation before middle ->
    memory_nary_compute_sequence_physical ge locals values operations middle final ->
    memory_nary_compute_sequence_physical ge locals values (operation::operations) before final.
Definition memory_nary_compute_sequence_requests operations := flat_map memory_nary_compute_requests operations.
Definition memory_nary_compute_sequence_anchors operations := flat_map memory_nary_compute_anchors operations.
Lemma memory_nary_compute_sequence_normal operations body :
  flatten_region body = map memory_nary_compute_statement operations -> normal_statement body = true.
Proof.
  intro BODY; apply flatten_normal_certificate; rewrite BODY; apply Forall_map,Forall_forall.
  intros; apply memory_nary_compute_normal.
Qed.
Lemma memory_nary_compute_sequence_quiet operations body :
  flatten_region body = map memory_nary_compute_statement operations -> quiet_statement body = true.
Proof.
  intro BODY; apply flatten_quiet_certificate; rewrite BODY; apply Forall_map,Forall_forall.
  intros; apply memory_nary_compute_quiet.
Qed.
Lemma memory_nary_compute_sequence_writes operations body :
  flatten_region body = map memory_nary_compute_statement operations -> writes_only [] body.
Proof.
  intro BODY; apply flatten_writes_certificate; rewrite BODY; apply Forall_map,Forall_forall.
  intros; apply memory_nary_compute_writes.
Qed.
Lemma memory_nary_compute_sequence_tail_inverse limits operations layout fe ge locals valuation temps memory after final :
  Forall (memory_nary_compute_valid limits layout) operations ->
  memory_nary_ranges limits (map valuation layout) ->
  (forall identifier, In identifier layout -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  tail_execution fe ge locals (map memory_nary_compute_statement operations) temps memory after final ->
  memory_nary_compute_sequence_physical ge locals (map valuation layout) operations memory final /\ after = temps.
Proof.
  intros CERT RANGE; revert temps memory after final; induction CERT as [|operation operations HEAD CERT IH];
    intros temps memory after final WORDS RUN; cbn in RUN; inversion RUN; subst.
  - split; [constructor|reflexivity].
  - match goal with POINT : exec_stmt _ _ _ _ _ (memory_nary_compute_statement _) _ _ _ _ |- _ =>
      destruct (@memory_nary_compute_inverse limits layout operation fe ge locals temps memory _ _ valuation
        HEAD RANGE WORDS POINT) as [ACT TEMPS]; subst end.
    match goal with TAIL : tail_execution _ _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ _ _ WORDS TAIL) as [REST EXIT] end.
    split; [econstructor; eauto|exact EXIT].
Qed.
Lemma memory_nary_compute_sequence_anchor_bindings ge locals dimensions operations before after :
  memory_nary_compute_sequence_physical ge locals (repeat 0 dimensions) operations before after ->
  forall descriptor, In descriptor (memory_nary_compute_sequence_anchors operations) ->
    exists block, rect_array_binding (memory_descriptor_shape descriptor) ge locals
      (memory_descriptor_variable descriptor) block /\ Mem.valid_pointer before block 0 = true.
Proof.
  intro RUN; induction RUN as [memory|operation operations before middle final HEAD TAIL IH];
    intros descriptor MEMBER; [contradiction|].
  cbn [memory_nary_compute_sequence_anchors flat_map] in MEMBER; apply in_app_or in MEMBER as [MEMBER|MEMBER].
  - eapply memory_nary_compute_anchor_bindings; eassumption.
  - destruct (IH descriptor MEMBER) as [block [ARRAY POINTER]]; exists block; split; [exact ARRAY|].
    destruct (@memory_nary_compute_store ge locals (repeat 0 dimensions) operation before middle HEAD) as [wb [offset [value STORE]]].
    apply (proj2 (@memory_store_valid_pointer _ _ _ _ _ _ _ _ STORE)); exact POINTER.
Qed.
Lemma memory_nary_compute_request_valid limits layout operation :
  memory_nary_compute_valid limits layout operation ->
  Forall (fun descriptor => rectangle_layout_valid (memory_descriptor_shape descriptor)) (memory_nary_compute_requests operation).
Proof.
  intros [[WRITE REST] [READS REST']]; unfold memory_nary_compute_requests; cbn; constructor; [exact WRITE|].
  apply Forall_map; eapply Forall_impl; [|exact READS]; intros access [VALID OTHER]; exact VALID.
Qed.
Theorem memory_nary_compute_sequence_registry limits layout ge locals dimensions operations before after :
  Forall (memory_nary_compute_valid limits layout) operations ->
  memory_nary_compute_sequence_physical ge locals (repeat 0 dimensions) operations before after ->
  exists entries, Forall2 (memory_descriptor_binding ge locals)
      (memory_unique_descriptors (memory_nary_compute_sequence_anchors operations)) entries /\
    NoDup (map memory_array_id entries) /\
    Forall (fun entry => Mem.valid_pointer before (memory_array_block entry) 0 = true) entries.
Proof.
  intros CERT RUN; apply memory_descriptor_entries_exist.
  - apply Forall_forall; intros descriptor MEMBER; apply memory_unique_descriptors_member in MEMBER.
    apply in_flat_map in MEMBER as [operation [MEMBER ANCHOR]].
    apply memory_nary_compute_anchor_member in ANCHOR.
    apply Forall_forall with (x := operation) in CERT; [|exact MEMBER].
    pose proof (@memory_nary_compute_request_valid limits layout operation CERT) as VALID.
    apply Forall_forall with (x := descriptor) in VALID; assumption.
  - apply memory_unique_descriptor_ids.
  - intros descriptor MEMBER; apply memory_unique_descriptors_member in MEMBER.
    eapply memory_nary_compute_sequence_anchor_bindings; eassumption.
Qed.
Lemma memory_nary_compute_sequence_cover descriptors operations :
  memory_descriptors_cover descriptors (memory_nary_compute_sequence_requests operations) ->
  Forall (fun operation => memory_descriptors_cover descriptors (memory_nary_compute_requests operation)) operations.
Proof.
  intro COVER; apply Forall_forall; intros operation MEMBER; apply Forall_forall; intros descriptor REQUEST.
  apply Forall_forall with (x := descriptor) in COVER; [exact COVER|].
  apply in_flat_map; exists operation; split; assumption.
Qed.
Theorem memory_nary_compute_sequence_point_execution limits layout descriptors entries ge locals values operations :
  Forall2 (memory_descriptor_binding ge locals) descriptors entries -> NoDup (map memory_array_id entries) ->
  Forall (fun operation => memory_descriptors_cover descriptors (memory_nary_compute_requests operation)) operations ->
  Forall (memory_nary_compute_valid limits layout) operations ->
  memory_nary_ranges limits values -> forall before after,
    (memory_nary_compute_sequence_physical ge locals values operations before after <->
      memory_nary_sequence_point (map memory_nary_compute_instruction operations) values
        (RuntimeState (memory_array_registry entries) before) (RuntimeState (memory_array_registry entries) after)).
Proof.
  intros ARRAYS UNIQUE COVERS; induction COVERS as [|operation operations COVER COVERS IH];
    intros CERT RANGE before after; unfold memory_nary_sequence_point; cbn [map].
  - split; intro RUN; inversion RUN; subst; constructor.
  - inversion CERT as [|head tail HEAD REST]; subst.
    assert (WBOUND : 0 <= memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation)) values <
      rectangle_extent (memory_nary_access_shape (memory_nary_compute_write operation)))
      by (destruct HEAD as [[_ [_ BOUND]] _]; apply BOUND; exact RANGE).
    assert (RBOUNDS : Forall (fun access => 0 <= memory_nary_index_value (memory_nary_access_index access) values <
      rectangle_extent (memory_nary_access_shape access)) (memory_nary_compute_reads operation)).
    { destruct HEAD as [_ [READS _]]; eapply Forall_impl; [|exact READS]; intros access [_ [_ BOUND]]; apply BOUND; exact RANGE. }
    split; intro RUN.
    + inversion RUN; subst.
      eapply Iter.IProgress with (st2 := RuntimeState (memory_array_registry entries) middle).
      * apply (proj1 (@memory_nary_compute_registry descriptors entries ge locals values operation before middle
          ARRAYS UNIQUE COVER WBOUND RBOUNDS)); assumption.
      * apply IH; assumption.
    + inversion RUN; subst.
      match goal with POINT : memory_nary_point _ _ _ ?middle |- _ =>
        destruct middle as [locations middle_memory];
        assert (LOCATIONS : locations = memory_array_registry entries)
          by (exact (@memory_nary_point_locations _ values _ _ POINT)); subst locations end.
      eapply NaryComputeSequenceCons with (middle := middle_memory).
      * apply (proj2 (@memory_nary_compute_registry descriptors entries ge locals values operation before middle_memory
          ARRAYS UNIQUE COVER WBOUND RBOUNDS)); assumption.
      * apply IH; assumption.
Qed.
Print Assumptions memory_nary_compute_sequence_registry.
Print Assumptions memory_nary_compute_sequence_point_execution.
