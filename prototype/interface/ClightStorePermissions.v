From Stdlib Require Import ZArith.
From compcert.common Require Import AST Values Memory.
From Guard Require Import ClightCountedLoop.
Set Implicit Arguments.

Definition memory_accesses_back before after :=
  forall chunk block offset permission,
    Mem.valid_access after chunk block offset permission ->
    Mem.valid_access before chunk block offset permission.

Lemma memory_accesses_back_refl memory : memory_accesses_back memory memory.
Proof. intros chunk block offset permission ACCESS; exact ACCESS. Qed.
Lemma memory_accesses_back_trans before middle after :
  memory_accesses_back before middle -> memory_accesses_back middle after ->
  memory_accesses_back before after.
Proof. intros FIRST SECOND chunk block offset permission ACCESS; apply FIRST,SECOND,ACCESS. Qed.

Lemma store_memory_accesses_back chunk memory block offset value final :
  Mem.store chunk memory block offset value = Some final -> memory_accesses_back memory final.
Proof.
  intros STORE other other_block other_offset permission ACCESS;
    eapply Mem.store_valid_access_2; eassumption.
Qed.

Lemma counted_memory_accesses_back (point : Z -> mem -> mem -> Prop) count start before after :
  (forall index first last, point index first last -> memory_accesses_back first last) ->
  counted_iterations point count start before after -> memory_accesses_back before after.
Proof.
  intros POINT RUN; induction RUN; [apply memory_accesses_back_refl|].
  eapply memory_accesses_back_trans; [eapply POINT; exact H|exact IHRUN].
Qed.

Print Assumptions store_memory_accesses_back.
Print Assumptions counted_memory_accesses_back.
