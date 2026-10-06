From Stdlib Require Import List Bool.
From compcert.lib Require Import Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightTempFrame.
From GuardInterface Require Import ClightStorePermissions.
Set Implicit Arguments.

(** Permission transport depends on the actual stores, not on arithmetic
    modeling or the stability of a loaded value. Calls, allocation and free
    are excluded by the existing structured [writes_only] certificate. *)
Lemma storev_memory_accesses_back chunk memory block offset value final :
  Mem.storev chunk memory (Vptr block offset) value = Some final ->
  memory_accesses_back memory final.
Proof.
  cbn [Mem.storev]; destruct (zle (Ptrofs.unsigned offset + size_chunk chunk) Ptrofs.modulus);
    intro STORE; [eapply store_memory_accesses_back; exact STORE|discriminate].
Qed.

Theorem assignment_memory_accesses_back ce ty memory block offset field value final :
  assign_loc ce ty memory block offset field value final -> memory_accesses_back memory final.
Proof.
  intro ASSIGN; inversion ASSIGN; subst.
  - eapply storev_memory_accesses_back; eassumption.
  - intros chunk other address permission ACCESS; eapply Mem.storebytes_valid_access_2; eassumption.
  - match goal with BITFIELD : store_bitfield _ _ _ _ _ _ _ _ _ _ |- _ =>
      inversion BITFIELD; subst end.
    eapply storev_memory_accesses_back; eassumption.
Qed.

Theorem structured_memory_accesses_back fe ge locals temps memory code trace after final outcome :
  exec_stmt fe ge locals temps memory code trace after final outcome ->
  forall written, writes_only written code -> memory_accesses_back memory final.
Proof.
  intro SOURCE; induction SOURCE; intros written WRITES; inversion WRITES; subst;
    try apply memory_accesses_back_refl.
  - eapply assignment_memory_accesses_back; eassumption.
  - eapply memory_accesses_back_trans; [eapply IHSOURCE1|eapply IHSOURCE2]; eassumption.
  - eapply IHSOURCE; eassumption.
  - destruct b; eapply IHSOURCE; eassumption.
  - eapply IHSOURCE; eassumption.
  - eapply memory_accesses_back_trans; [eapply IHSOURCE1|eapply IHSOURCE2]; eassumption.
  - eapply memory_accesses_back_trans; [eapply IHSOURCE1|].
    + eassumption.
    + eapply memory_accesses_back_trans; [eapply IHSOURCE2|eapply IHSOURCE3]; eassumption.
Qed.

Print Assumptions assignment_memory_accesses_back.
Print Assumptions structured_memory_accesses_back.
