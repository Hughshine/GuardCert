From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Coqlib.
From compcert.common Require Import AST Values Memory.
From Guard Require Import ClightTempFrame.
From GuardMemory Require Import GuardMemoryNaryCompute GuardMemoryNaryAffineAccess
  GuardMemoryMultiPointerAccess GuardMemoryMultiPointerCompute GuardMemoryMultiPointerSequence.
Import ListNotations.
Set Implicit Arguments.

Definition memory_multi_pointer_operation_ids operation :=
  memory_nary_access_array (memory_nary_compute_write operation)::
    map memory_nary_access_array (memory_nary_compute_reads operation).
Definition memory_multi_pointer_operation_identifiers operations :=
  nodup peq (flat_map memory_multi_pointer_operation_ids operations).
Definition memory_multi_pointer_operation_covered pointers operation :=
  In (memory_nary_access_array (memory_nary_compute_write operation)) pointers /\
  Forall (fun access => In (memory_nary_access_array access) pointers) (memory_nary_compute_reads operation).
Definition memory_multi_pointer_operation_covered_check pointers operation :=
  existsb (Pos.eqb (memory_nary_access_array (memory_nary_compute_write operation))) pointers &&
    forallb (fun access => existsb (Pos.eqb (memory_nary_access_array access)) pointers)
      (memory_nary_compute_reads operation).
Lemma memory_multi_pointer_identifier_member identifier pointers :
  existsb (Pos.eqb identifier) pointers = true -> In identifier pointers.
Proof. intro CHECK; apply existsb_exists in CHECK as [key [MEMBER SAME]];
  apply Pos.eqb_eq in SAME; subst; exact MEMBER. Qed.
Lemma memory_multi_pointer_operation_covered_check_sound pointers operation :
  memory_multi_pointer_operation_covered_check pointers operation = true ->
  memory_multi_pointer_operation_covered pointers operation.
Proof.
  unfold memory_multi_pointer_operation_covered_check,memory_multi_pointer_operation_covered;
    rewrite andb_true_iff; intros [WRITE READS]; split.
  - apply memory_multi_pointer_identifier_member; exact WRITE.
  - apply Forall_forall; intros access MEMBER; apply memory_multi_pointer_identifier_member;
      apply forallb_forall with (x := access) in READS; assumption.
Qed.
Lemma memory_multi_pointer_loaded_frame pointers initial current values memory access value :
  temp_agree pointers initial current -> In (memory_nary_access_array access) pointers ->
  memory_multi_pointer_access_loaded initial values memory access value ->
  memory_multi_pointer_access_loaded current values memory access value.
Proof. intros FRAME MEMBER [block [base [POINTER LOAD]]]; exists block,base; split;
  [rewrite FRAME by exact MEMBER; exact POINTER|exact LOAD]. Qed.
Lemma memory_multi_pointer_loads_frame pointers initial current values memory accesses loaded :
  temp_agree pointers initial current ->
  Forall (fun access => In (memory_nary_access_array access) pointers) accesses ->
  Forall2 (memory_multi_pointer_access_loaded initial values memory) accesses loaded ->
  Forall2 (memory_multi_pointer_access_loaded current values memory) accesses loaded.
Proof.
  intros FRAME COVER LOADS; induction LOADS; [constructor|].
  inversion COVER; subst; constructor; [eapply memory_multi_pointer_loaded_frame; eassumption|apply IHLOADS; assumption].
Qed.
Lemma memory_multi_pointer_compute_frame pointers initial current values operation before after :
  memory_multi_pointer_operation_covered pointers operation -> temp_agree pointers initial current ->
  memory_multi_pointer_compute_physical initial values operation before after ->
  memory_multi_pointer_compute_physical current values operation before after.
Proof.
  intros [WRITE READS] FRAME [block [base [loaded [value [POINTER [LOADS [COMPUTE STORE]]]]]]].
  exists block,base,loaded,value; split; [rewrite FRAME by exact WRITE; exact POINTER|].
  split; [eapply memory_multi_pointer_loads_frame; eassumption|]; split; assumption.
Qed.
Theorem memory_multi_pointer_sequence_frame pointers initial current values operations before after :
  Forall (memory_multi_pointer_operation_covered pointers) operations -> temp_agree pointers initial current ->
  memory_multi_pointer_sequence_physical initial values operations before after ->
  memory_multi_pointer_sequence_physical current values operations before after.
Proof.
  intros COVER FRAME RUN; induction RUN; [constructor|].
  inversion COVER; subst; econstructor; [eapply memory_multi_pointer_compute_frame; eassumption|apply IHRUN; assumption].
Qed.
Print Assumptions memory_multi_pointer_operation_covered_check_sound.
Print Assumptions memory_multi_pointer_sequence_frame.
