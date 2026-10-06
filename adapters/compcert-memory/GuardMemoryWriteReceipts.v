From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From Guard Require Import ClightCountedLoop.
From GuardMemory Require Import GuardMemoryNaryCompute GuardMemoryNaryAffineAccess
  GuardMemoryNaryAffineExpressions GuardMemoryBufferOffsets GuardMemoryMultiPointerCompute
  GuardMemoryMultiPointerSequence.
From GuardInterface Require Import ClightStorePermissions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Actual stores preserve access permissions in both directions. These
    receipts justify comparisons at the original entry; they do not execute
    stores in a guard and do not assert future source reachability. *)
Lemma memory_pointer_compute_accesses_back temps values operation before after :
  memory_multi_pointer_compute_physical temps values operation before after ->
  memory_accesses_back before after.
Proof.
  intros [block [base [loaded [value [POINTER [READS [VALUE STORE]]]]]]].
  intros chunk other offset permission ACCESS; eapply Mem.store_valid_access_2; eassumption.
Qed.

Lemma memory_pointer_sequence_accesses_back temps values operations before after :
  memory_multi_pointer_sequence_physical temps values operations before after ->
  memory_accesses_back before after.
Proof.
  intro RUN; induction RUN; [apply memory_accesses_back_refl|].
  eapply memory_accesses_back_trans; [eapply memory_pointer_compute_accesses_back; exact H|exact IHRUN].
Qed.

Definition memory_write_receipt temps values memory operation :=
  exists block base,
    temps ! (memory_nary_access_array (memory_nary_compute_write operation)) = Some (Vptr block base) /\
    Mem.valid_access memory Mint32 block (memory_pointer_buffer_offset base
      (memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation)) values)) Writable.

Lemma memory_pointer_compute_write_receipt temps values operation before after :
  memory_multi_pointer_compute_physical temps values operation before after ->
  memory_write_receipt temps values before operation.
Proof.
  intros [block [base [loaded [value [POINTER [READS [VALUE STORE]]]]]]].
  exists block,base; split; [exact POINTER|eapply Mem.store_valid_access_3; exact STORE].
Qed.

Lemma memory_write_receipt_back temps values before after operation :
  memory_accesses_back before after -> memory_write_receipt temps values after operation ->
  memory_write_receipt temps values before operation.
Proof.
  intros BACK [block [base [POINTER ACCESS]]]; exists block,base; split; [exact POINTER|apply BACK,ACCESS].
Qed.

Theorem memory_pointer_sequence_write_receipts temps values operations before after :
  memory_multi_pointer_sequence_physical temps values operations before after ->
  Forall (memory_write_receipt temps values before) operations.
Proof.
  intro RUN; induction RUN; [constructor|].
  constructor; [eapply memory_pointer_compute_write_receipt; exact H|].
  eapply Forall_impl; [|exact IHRUN].
  intros item RECEIPT; eapply memory_write_receipt_back;
    [eapply memory_pointer_compute_accesses_back; exact H|exact RECEIPT].
Qed.

(** A complete actual row supplies permissions for every operation in that
    row, even if one of its stores changes the outer memory-loaded bound.
    Moving to the next row needs a separate preservation argument. *)
Theorem counted_pointer_sequence_write_receipts temps values operations count start before after :
  counted_iterations (fun index => memory_multi_pointer_sequence_physical temps (values index) operations)
    count start before after ->
  forall index, start <= index < start + Z.of_nat count ->
    Forall (memory_write_receipt temps (values index) before) operations.
Proof.
  intro RUN; induction RUN as [x memory|n x first middle last STEP RUN IH]; intros index RANGE; [cbn in RANGE; lia|].
  destruct (Z.eq_dec index x) as [SAME|DIFFERENT].
  - subst index; eapply memory_pointer_sequence_write_receipts; exact STEP.
  - assert (NEXT : x+1 <= index < x+1+Z.of_nat n) by
      (rewrite Nat2Z.inj_succ in RANGE; lia).
    pose proof (IH index NEXT) as RECEIPTS.
    eapply Forall_impl; [|exact RECEIPTS].
    intros item RECEIPT; eapply memory_write_receipt_back;
      [eapply memory_pointer_sequence_accesses_back; exact STEP|exact RECEIPT].
Qed.

Print Assumptions memory_pointer_compute_accesses_back.
Print Assumptions memory_pointer_sequence_accesses_back.
Print Assumptions memory_pointer_sequence_write_receipts.
Print Assumptions counted_pointer_sequence_write_receipts.
