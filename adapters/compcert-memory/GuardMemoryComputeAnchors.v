From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightRectangularStore.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRegistryBackend GuardMemoryAffineAccessExpressions
  GuardMemoryAffineAccess GuardMemoryAccessAnchors GuardMemorySourceValues GuardMemoryAffineCompute.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_compute_anchors operation :=
  flat_map memory_affine_access_anchor (memory_compute_write operation::memory_compute_reads operation).
Lemma memory_compute_anchor_member operation descriptor :
  In descriptor (memory_compute_anchors operation) -> In descriptor (memory_affine_compute_requests operation).
Proof.
  intro MEMBER; apply in_flat_map in MEMBER as [access [MEMBER ANCHOR]].
  apply memory_affine_access_anchor_member in ANCHOR as [SAME ZERO]; subst descriptor.
  apply in_map; exact MEMBER.
Qed.
Lemma memory_affine_compute_store ge locals i j operation before after :
  memory_affine_compute_physical ge locals i j operation before after ->
  exists block offset value, Mem.store Mint32 before block offset value = Some after.
Proof. intros [block [loaded [value [_ [_ [_ STORE]]]]]]; eauto. Qed.
Theorem memory_compute_anchor_bindings ge locals operation before after :
  memory_affine_compute_physical ge locals 0 0 operation before after ->
  forall descriptor, In descriptor (memory_compute_anchors operation) ->
    exists block, rect_array_binding (memory_descriptor_shape descriptor) ge locals
      (memory_descriptor_variable descriptor) block /\ Mem.valid_pointer before block 0 = true.
Proof.
  intros [wb [loaded [value [WRITE [LOADS [COMPUTE STORE]]]]]] descriptor MEMBER.
  apply in_flat_map in MEMBER as [access [MEMBER ANCHOR]].
  apply memory_affine_access_anchor_member in ANCHOR as [SAME ZERO]; subst descriptor; cbn.
  destruct MEMBER as [SAME|MEMBER].
  - subst access; exists wb; split; [exact WRITE|].
    rewrite ZERO in STORE; cbn in STORE; apply Mem.valid_pointer_nonempty_perm.
    pose proof (@Mem.store_valid_access_3 _ _ _ _ _ _ STORE) as [PERMISSION ALIGN].
    eapply Mem.perm_implies; [apply PERMISSION; change (0 <= 0 < 4); lia|constructor].
  - apply In_nth_error in MEMBER as [index LOOKUP].
    destruct (@memory_source_values_lookup ge locals 0 0 before (memory_compute_reads operation) loaded index access LOADS LOOKUP)
      as [old [LOOKED [rb [READ LOADED]]]].
    exists rb; split; [exact READ|].
    rewrite ZERO in LOADED; cbn in LOADED; apply Mem.valid_pointer_nonempty_perm.
    pose proof (@Mem.load_valid_access _ _ _ _ _ LOADED) as [PERMISSION ALIGN].
    eapply Mem.perm_implies; [apply PERMISSION; change (0 <= 0 < 4); lia|constructor].
Qed.
Print Assumptions memory_compute_anchor_bindings.
