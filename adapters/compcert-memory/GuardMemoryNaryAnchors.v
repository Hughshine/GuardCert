From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightRectangularStore.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRegistryBackend GuardMemoryNaryAffineExpressions
  GuardMemoryNaryAffineAccess GuardMemoryNarySourceValues GuardMemoryNaryCompute.
From polcert.lib Require Import Linalg.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_nary_access_anchor access :=
  if snd (memory_nary_access_index access) =? 0 then [memory_nary_access_descriptor access] else [].
Lemma memory_nary_access_anchor_member access descriptor :
  In descriptor (memory_nary_access_anchor access) ->
  descriptor = memory_nary_access_descriptor access /\ snd (memory_nary_access_index access) = 0.
Proof.
  unfold memory_nary_access_anchor; destruct (snd (memory_nary_access_index access) =? 0) eqn:ZERO; cbn;
    [intros [SAME|[]]; split; [symmetry; exact SAME|apply Z.eqb_eq; exact ZERO]|contradiction].
Qed.
Lemma memory_nary_zero_index term dimensions :
  snd term = 0 -> memory_nary_index_value term (repeat 0 dimensions) = 0.
Proof.
  intro ZERO; unfold memory_nary_index_value; rewrite dot_product_repeat_zero_right,ZERO; reflexivity.
Qed.

Definition memory_nary_compute_anchors operation :=
  flat_map memory_nary_access_anchor (memory_nary_compute_write operation::memory_nary_compute_reads operation).
Lemma memory_nary_compute_anchor_member operation descriptor :
  In descriptor (memory_nary_compute_anchors operation) -> In descriptor (memory_nary_compute_requests operation).
Proof.
  intro MEMBER; apply in_flat_map in MEMBER as [access [MEMBER ANCHOR]].
  apply memory_nary_access_anchor_member in ANCHOR as [SAME ZERO]; subst descriptor.
  apply in_map; exact MEMBER.
Qed.
Lemma memory_nary_compute_store ge locals values operation before after :
  memory_nary_compute_physical ge locals values operation before after ->
  exists block offset value, Mem.store Mint32 before block offset value = Some after.
Proof. intros [block [loaded [value [_ [_ [_ STORE]]]]]]; eauto. Qed.
Theorem memory_nary_compute_anchor_bindings ge locals dimensions operation before after :
  memory_nary_compute_physical ge locals (repeat 0 dimensions) operation before after ->
  forall descriptor, In descriptor (memory_nary_compute_anchors operation) ->
    exists block, rect_array_binding (memory_descriptor_shape descriptor) ge locals
      (memory_descriptor_variable descriptor) block /\ Mem.valid_pointer before block 0 = true.
Proof.
  intros [wb [loaded [value [WRITE [LOADS [COMPUTE STORE]]]]]] descriptor MEMBER.
  apply in_flat_map in MEMBER as [access [MEMBER ANCHOR]].
  apply memory_nary_access_anchor_member in ANCHOR as [SAME ZERO]; subst descriptor; cbn.
  destruct MEMBER as [SAME|MEMBER].
  - subst access; exists wb; split; [exact WRITE|].
    rewrite (@memory_nary_zero_index _ dimensions ZERO) in STORE; cbn in STORE; apply Mem.valid_pointer_nonempty_perm.
    pose proof (@Mem.store_valid_access_3 _ _ _ _ _ _ STORE) as [PERMISSION ALIGN].
    eapply Mem.perm_implies; [apply PERMISSION; change (0 <= 0 < 4); lia|constructor].
  - apply In_nth_error in MEMBER as [index LOOKUP].
    destruct (@memory_nary_source_values_lookup ge locals (repeat 0 dimensions) before (memory_nary_compute_reads operation) loaded index access LOADS LOOKUP)
      as [old [LOOKED [rb [READ LOADED]]]].
    exists rb; split; [exact READ|].
    rewrite (@memory_nary_zero_index _ dimensions ZERO) in LOADED; cbn in LOADED; apply Mem.valid_pointer_nonempty_perm.
    pose proof (@Mem.load_valid_access _ _ _ _ _ LOADED) as [PERMISSION ALIGN].
    eapply Mem.perm_implies; [apply PERMISSION; change (0 <= 0 < 4); lia|constructor].
Qed.
Print Assumptions memory_nary_compute_anchor_bindings.
