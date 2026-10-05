From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memdata Memory.
From Guard Require Import CompCertStoreSchedule.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma repeated_store_bytes bytes start contents :
  Mem.setN bytes start (Mem.setN bytes start contents) = Mem.setN bytes start contents.
Proof.
  revert start contents; induction bytes as [|head tail IH]; intros start contents; [reflexivity|].
  cbn [Mem.setN].
  rewrite <- (@store_bytes_point_commute tail (start+1) start head (ZMap.set start head contents)) by lia.
  assert (SAME : ZMap.set start head (ZMap.set start head contents) = ZMap.set start head contents)
    by (unfold ZMap.set; apply PMap.set2).
  rewrite SAME.
  apply IH.
Qed.

Theorem store_result_fixed chunk before block offset value after :
  Mem.store chunk before block offset value = Some after ->
  Mem.store chunk after block offset value = Some after.
Proof.
  intro STORE.
  assert (VALID : Mem.valid_access after chunk block offset Writable).
  { eapply Mem.store_valid_access_1; [exact STORE|eapply Mem.store_valid_access_3; exact STORE]. }
  destruct (Mem.valid_access_store _ _ _ _ value VALID) as [final AGAIN].
  assert (CONTENTS : Mem.mem_contents final = Mem.mem_contents after).
  { rewrite (Mem.store_mem_contents _ _ _ _ _ _ AGAIN), (Mem.store_mem_contents _ _ _ _ _ _ STORE).
    rewrite PMap.gss,repeated_store_bytes,PMap.set2; reflexivity. }
  assert (ACCESS : Mem.mem_access final = Mem.mem_access after)
    by (eapply Mem.store_access; exact AGAIN).
  assert (NEXT : Mem.nextblock final = Mem.nextblock after)
    by (eapply Mem.nextblock_store; exact AGAIN).
  assert (SAME : final = after) by (destruct final,after; apply Mem.mkmem_ext; assumption).
  subst final; exact AGAIN.
Qed.
Theorem storev_result_fixed chunk before block offset value after :
  Mem.storev chunk before (Vptr block offset) value = Some after ->
  Mem.storev chunk after (Vptr block offset) value = Some after.
Proof.
  cbn [Mem.storev]; destruct (zle _ _); [apply store_result_fixed|discriminate].
Qed.
Print Assumptions store_result_fixed.
Print Assumptions storev_result_fixed.
