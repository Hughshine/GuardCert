From Stdlib Require Import List ZArith Lia.
From compcert.common Require Import Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightRectangularStore.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRegistryBackend GuardMemoryLayoutRegistry
  GuardMemoryMultipleArrays GuardMemoryNamedRegistrySource GuardMemoryNaryAffineExpressions GuardMemoryNaryAffineAccess GuardMemoryNaryAccessCheck GuardMemoryNarySourceValues
  GuardMemoryNaryCompute GuardMemoryNaryAnchors GuardMemoryNarySequence GuardMemoryAccessAnchors
  GuardMemoryScalarAccess GuardMemoryScalarArrayCompute.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_scalar_array_anchor_index limits layout access values :
  memory_nary_access_valid limits layout access -> snd (memory_nary_access_index access) = 0 ->
  memory_nary_index_value (memory_nary_access_index access) (repeat 0 (length layout)++values) = 0.
Proof.
  intros [_ [ENCODE BOUND]] ZERO; rewrite memory_scalar_index_value.
  - apply memory_nary_zero_index; exact ZERO.
  - rewrite (@memory_encode_nary_index_length layout _ _ ENCODE),repeat_length; reflexivity.
Qed.
Theorem memory_scalar_array_compute_anchor_bindings limits layout scalars ge locals values operation before after :
  memory_scalar_array_compute_valid limits layout scalars operation ->
  memory_nary_compute_physical ge locals (repeat 0 (length layout)++values) operation before after ->
  forall descriptor, In descriptor (memory_nary_compute_anchors operation) ->
    exists block, rect_array_binding (memory_descriptor_shape descriptor) ge locals
      (memory_descriptor_variable descriptor) block /\ Mem.valid_pointer before block 0 = true.
Proof.
  intros [WRITE_VALID [READ_VALID _]] [wb [loaded [value [WRITE [LOADS [COMPUTE STORE]]]]]] descriptor MEMBER.
  apply in_flat_map in MEMBER as [access [MEMBER ANCHOR]].
  apply memory_nary_access_anchor_member in ANCHOR as [SAME ZERO]; subst descriptor; cbn.
  destruct MEMBER as [SAME|MEMBER].
  - subst access; exists wb; split; [exact WRITE|].
    rewrite (@memory_scalar_array_anchor_index limits layout _ values WRITE_VALID ZERO) in STORE; cbn in STORE.
    apply Mem.valid_pointer_nonempty_perm.
    pose proof (@Mem.store_valid_access_3 _ _ _ _ _ _ STORE) as [PERMISSION ALIGN].
    eapply Mem.perm_implies; [apply PERMISSION; change (0 <= 0 < 4); lia|constructor].
  - apply In_nth_error in MEMBER as [index LOOKUP].
    destruct (@memory_nary_source_values_lookup ge locals (repeat 0 (length layout)++values) before
      (memory_nary_compute_reads operation) loaded index access LOADS LOOKUP) as [old [LOOKED [rb [READ LOADED]]]].
    exists rb; split; [exact READ|].
    apply Forall_forall with (x := access) in READ_VALID; [|eapply nth_error_In; exact LOOKUP].
    rewrite (@memory_scalar_array_anchor_index limits layout access values READ_VALID ZERO) in LOADED; cbn in LOADED.
    apply Mem.valid_pointer_nonempty_perm.
    pose proof (@Mem.load_valid_access _ _ _ _ _ LOADED) as [PERMISSION ALIGN].
    eapply Mem.perm_implies; [apply PERMISSION; change (0 <= 0 < 4); lia|constructor].
Qed.
Lemma memory_scalar_array_sequence_anchor_bindings limits layout scalars ge locals values operations before after :
  Forall (memory_scalar_array_compute_valid limits layout scalars) operations ->
  memory_nary_compute_sequence_physical ge locals (repeat 0 (length layout)++values) operations before after ->
  forall descriptor, In descriptor (memory_nary_compute_sequence_anchors operations) ->
    exists block, rect_array_binding (memory_descriptor_shape descriptor) ge locals
      (memory_descriptor_variable descriptor) block /\ Mem.valid_pointer before block 0 = true.
Proof.
  intros CERT RUN; induction RUN as [memory|operation operations before middle final HEAD TAIL IH];
    intros descriptor MEMBER; [contradiction|].
  inversion CERT; subst.
  cbn [memory_nary_compute_sequence_anchors flat_map] in MEMBER; apply in_app_or in MEMBER as [MEMBER|MEMBER].
  - eapply memory_scalar_array_compute_anchor_bindings; eassumption.
  - destruct (IH ltac:(assumption) descriptor MEMBER) as [block [ARRAY POINTER]]; exists block; split; [exact ARRAY|].
    destruct (@memory_nary_compute_store ge locals (repeat 0 (length layout)++values) operation before middle HEAD)
      as [wb [offset [value STORE]]].
    apply (proj2 (@memory_store_valid_pointer _ _ _ _ _ _ _ _ STORE)); exact POINTER.
Qed.
Lemma memory_scalar_array_compute_request_valid limits layout scalars operation :
  memory_scalar_array_compute_valid limits layout scalars operation ->
  Forall (fun descriptor => rectangle_layout_valid (memory_descriptor_shape descriptor)) (memory_nary_compute_requests operation).
Proof.
  intros [[WRITE REST] [READS REST']]; unfold memory_nary_compute_requests; cbn; constructor; [exact WRITE|].
  apply Forall_map; eapply Forall_impl; [|exact READS]; intros access [VALID OTHER]; exact VALID.
Qed.
Theorem memory_scalar_array_sequence_registry limits layout scalars ge locals values operations before after :
  Forall (memory_scalar_array_compute_valid limits layout scalars) operations ->
  memory_nary_compute_sequence_physical ge locals (repeat 0 (length layout)++values) operations before after ->
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
    pose proof (@memory_scalar_array_compute_request_valid limits layout scalars operation CERT) as VALID.
    apply Forall_forall with (x := descriptor) in VALID; assumption.
  - apply memory_unique_descriptor_ids.
  - intros descriptor MEMBER; apply memory_unique_descriptors_member in MEMBER.
    eapply memory_scalar_array_sequence_anchor_bindings; eassumption.
Qed.
Print Assumptions memory_scalar_array_sequence_registry.
