From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightRectangularStore CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryMultipleArrays GuardMemoryRegistryBackend
  GuardMemoryLayoutRegistry GuardMemoryLayoutOperations GuardMemoryNamedRegistrySource
  GuardMemoryAffineAccessExpressions GuardMemoryAffineAccess GuardMemoryAffineCopy
  GuardMemoryGeneralLayoutOperations GuardMemoryGeneralLayoutSequence.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_affine_access_anchor access :=
  if memory_index_bias (memory_access_index access) =? 0 then [memory_access_descriptor access] else [].
Definition memory_general_layout_anchors operation := match operation with
  | MemoryGeneralLayout operation => memory_layout_operation_requests operation
  | MemoryGeneralAffineCopy write read => memory_affine_access_anchor write++memory_affine_access_anchor read end.
Definition memory_general_sequence_anchors operations := flat_map memory_general_layout_anchors operations.
Lemma memory_affine_access_anchor_member access descriptor :
  In descriptor (memory_affine_access_anchor access) ->
  descriptor = memory_access_descriptor access /\ memory_index_value (memory_access_index access) 0 0 = 0.
Proof.
  unfold memory_affine_access_anchor; destruct (memory_index_bias (memory_access_index access) =? 0) eqn:ZERO;
    [|contradiction].
  intros [SAME|[]]; subst descriptor; split; [reflexivity|].
  apply Z.eqb_eq in ZERO; unfold memory_index_value; rewrite ZERO; ring.
Qed.
Lemma memory_general_anchor_requested operation descriptor :
  In descriptor (memory_general_layout_anchors operation) -> In descriptor (memory_general_layout_requests operation).
Proof.
  destruct operation as [operation|write read]; cbn; [auto|].
  intro MEMBER; apply in_app_or in MEMBER as [MEMBER|MEMBER];
    apply memory_affine_access_anchor_member in MEMBER as [-> ZERO]; cbn; auto.
Qed.
Lemma memory_general_sequence_anchor_requested operations descriptor :
  In descriptor (memory_general_sequence_anchors operations) -> In descriptor (memory_general_sequence_requests operations).
Proof.
  intro MEMBER; apply in_flat_map in MEMBER as [operation [MEMBER ANCHOR]].
  apply in_flat_map; exists operation; split; [exact MEMBER|apply memory_general_anchor_requested; exact ANCHOR].
Qed.
Lemma memory_affine_copy_anchor_bindings ge locals write read before after :
  memory_affine_copy_physical ge locals write read 0 0 before after ->
  forall descriptor, In descriptor (memory_affine_access_anchor write++memory_affine_access_anchor read) ->
    exists block, rect_array_binding (memory_descriptor_shape descriptor) ge locals
      (memory_descriptor_variable descriptor) block /\ Mem.valid_pointer before block 0 = true.
Proof.
  intros [wb [rb [WRITE [READ [inputs [value [LOAD [_ STORE]]]]]]]] descriptor MEMBER.
  change (Mem.store Mint32 before wb (4*memory_index_value (memory_access_index write) 0 0) value = Some after) in STORE.
  change (match Mem.load Mint32 before rb (4*memory_index_value (memory_access_index read) 0 0) with
    Some old => Some [old] | None => None end = Some inputs) in LOAD.
  apply in_app_or in MEMBER as [MEMBER|MEMBER]; apply memory_affine_access_anchor_member in MEMBER as [SAME ZERO];
    subst descriptor; cbn.
  - exists wb; split; [exact WRITE|].
    rewrite ZERO in STORE; cbn in STORE; apply Mem.valid_pointer_nonempty_perm.
    pose proof (@Mem.store_valid_access_3 _ _ _ _ _ _ STORE) as [PERMISSION ALIGN].
    eapply Mem.perm_implies; [apply PERMISSION; change (0 <= 0 < 4); lia|constructor].
  - exists rb; split; [exact READ|].
    rewrite ZERO in LOAD; cbn in LOAD.
    destruct (Mem.load Mint32 before rb 0) as [old|] eqn:LOADED; [|discriminate].
    apply Mem.valid_pointer_nonempty_perm.
    pose proof (@Mem.load_valid_access _ _ _ _ _ LOADED) as [PERMISSION ALIGN].
    eapply Mem.perm_implies; [apply PERMISSION; change (0 <= 0 < 4); lia|constructor].
Qed.
Lemma memory_general_layout_anchor_bindings ge locals operation before after :
  memory_general_layout_physical ge locals 0 0 operation before after ->
  forall descriptor, In descriptor (memory_general_layout_anchors operation) ->
    exists block, rect_array_binding (memory_descriptor_shape descriptor) ge locals
      (memory_descriptor_variable descriptor) block /\ Mem.valid_pointer before block 0 = true.
Proof.
  destruct operation as [operation|write read]; cbn; intro RUN.
  - eapply memory_layout_operation_initial_bindings; exact RUN.
  - eapply memory_affine_copy_anchor_bindings; exact RUN.
Qed.
Lemma memory_general_sequence_anchor_bindings ge locals operations before after :
  memory_general_operations_physical ge locals 0 0 operations before after ->
  forall descriptor, In descriptor (memory_general_sequence_anchors operations) ->
    exists block, rect_array_binding (memory_descriptor_shape descriptor) ge locals
      (memory_descriptor_variable descriptor) block /\ Mem.valid_pointer before block 0 = true.
Proof.
  intro RUN; induction RUN as [memory|operation operations before middle final HEAD TAIL IH];
    intros descriptor MEMBER; [contradiction|].
  cbn [memory_general_sequence_anchors flat_map] in MEMBER; apply in_app_or in MEMBER as [MEMBER|MEMBER].
  - eapply memory_general_layout_anchor_bindings; eassumption.
  - destruct (IH descriptor MEMBER) as [block [BINDING POINTER]].
    exists block; split; [exact BINDING|].
    destruct (@memory_general_layout_physical_store ge locals operation 0 0 before middle HEAD) as [write [offset [value STORE]]].
    apply (proj2 (@memory_store_valid_pointer _ _ _ _ _ _ _ _ STORE)); exact POINTER.
Qed.
Theorem memory_general_anchors_registry ge locals operations before after :
  Forall (fun descriptor => rectangle_layout_valid (memory_descriptor_shape descriptor)) (memory_general_sequence_requests operations) ->
  memory_general_operations_physical ge locals 0 0 operations before after ->
  exists entries, Forall2 (memory_descriptor_binding ge locals)
      (memory_unique_descriptors (memory_general_sequence_anchors operations)) entries /\
    NoDup (map memory_array_id entries) /\
    Forall (fun entry => Mem.valid_pointer before (memory_array_block entry) 0 = true) entries.
Proof.
  intros VALID RUN; apply memory_descriptor_entries_exist.
  - apply Forall_forall; intros descriptor MEMBER; apply memory_unique_descriptors_member in MEMBER.
    apply memory_general_sequence_anchor_requested in MEMBER.
    apply Forall_forall with (x := descriptor) in VALID; assumption.
  - apply memory_unique_descriptor_ids.
  - intros descriptor MEMBER; apply memory_unique_descriptors_member in MEMBER.
    eapply memory_general_sequence_anchor_bindings; eassumption.
Qed.
Print Assumptions memory_affine_copy_anchor_bindings.
Print Assumptions memory_general_anchors_registry.
