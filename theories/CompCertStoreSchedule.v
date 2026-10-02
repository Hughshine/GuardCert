From Stdlib Require Import List ZArith Lia RelationClasses.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memdata Memory.
From Guard Require Import AbstractSchedule.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A direct CompCert language instance. Instruction execution is Mem.store;
    no CInstr state or abstract instruction execution axiom is introduced. *)
Record store_action := StoreAction {
  action_chunk : memory_chunk;
  action_block : Values.block;
  action_offset : Z;
  action_value : val
}.
Definition store_action_run action before after :=
  Mem.store (action_chunk action) before (action_block action) (action_offset action)
    (action_value action) = Some after.
Definition stores_disjoint first second :=
  action_block first <> action_block second \/
  action_offset first + size_chunk (action_chunk first) <= action_offset second \/
  action_offset second + size_chunk (action_chunk second) <= action_offset first.

(** The elementary byte-update proof follows the same decomposition as
    PolCert's CState.disjoint_store_commute, generalized to distinct chunks. *)
Lemma store_pmap_updates_commute (A : Type) (i j : positive) (x y : A) (map : PMap.t A) :
  i <> j -> PMap.set i x (PMap.set j y map) = PMap.set j y (PMap.set i x map).
Proof.
  intros DIFFERENT; destruct map as [default tree]; unfold PMap.set; cbn; f_equal.
  apply PTree.extensionality; intro key; rewrite !PTree.gsspec.
  destruct (peq key i), (peq key j); subst; try congruence; reflexivity.
Qed.
Lemma store_zmap_updates_commute (A : Type) i j (x y : A) (map : ZMap.t A) :
  i <> j -> ZMap.set i x (ZMap.set j y map) = ZMap.set j y (ZMap.set i x map).
Proof.
  intros DIFFERENT; unfold ZMap.set; apply store_pmap_updates_commute.
  intro EQ; apply DIFFERENT, ZIndexed.index_inj; exact EQ.
Qed.
Lemma store_bytes_point_commute bytes start point value (contents : ZMap.t memval) :
  point < start \/ start + Z.of_nat (length bytes) <= point ->
  Mem.setN bytes start (ZMap.set point value contents) =
  ZMap.set point value (Mem.setN bytes start contents).
Proof.
  revert start contents; induction bytes as [|head tail IH]; intros start contents OUTSIDE; [reflexivity|].
  cbn in *; rewrite store_zmap_updates_commute by lia; rewrite IH by lia; reflexivity.
Qed.
Lemma store_byte_ranges_commute first second start_first start_second (contents : ZMap.t memval) :
  start_first + Z.of_nat (length first) <= start_second \/
  start_second + Z.of_nat (length second) <= start_first ->
  Mem.setN second start_second (Mem.setN first start_first contents) =
  Mem.setN first start_first (Mem.setN second start_second contents).
Proof.
  revert start_first start_second contents; induction second as [|head tail IH];
    intros start_first start_second contents DISJOINT; [reflexivity|].
  cbn in *; rewrite <- store_bytes_point_commute by lia; rewrite IH by lia; reflexivity.
Qed.

Lemma disjoint_store_results_equal first second initial left original right candidate :
  store_action_run first initial left -> store_action_run second left original ->
  store_action_run second initial right -> store_action_run first right candidate ->
  stores_disjoint first second -> original = candidate.
Proof.
  destruct first as [chunk1 b1 ofs1 value1], second as [chunk2 b2 ofs2 value2].
  cbn [store_action_run stores_disjoint action_chunk action_block action_offset action_value].
  intros LEFT ORIGINAL RIGHT CANDIDATE DISJOINT.
  unfold store_action_run, stores_disjoint in *; cbn [action_chunk action_block action_offset action_value] in *.
  assert (CONTENTS : Mem.mem_contents original = Mem.mem_contents candidate).
  { rewrite (Mem.store_mem_contents _ _ _ _ _ _ ORIGINAL),
      (Mem.store_mem_contents _ _ _ _ _ _ LEFT),
      (Mem.store_mem_contents _ _ _ _ _ _ CANDIDATE),
      (Mem.store_mem_contents _ _ _ _ _ _ RIGHT).
    destruct (peq b1 b2) as [SAME|DIFFERENT].
    - subst b2; rewrite !PMap.gss, !PMap.set2; f_equal.
      apply store_byte_ranges_commute. rewrite !encode_val_length, <- !size_chunk_conv.
      cbn [action_chunk action_offset]; tauto.
    - rewrite !PMap.gso by congruence; apply store_pmap_updates_commute; congruence. }
  assert (ACCESS : Mem.mem_access original = Mem.mem_access candidate).
  { rewrite (Mem.store_access _ _ _ _ _ _ ORIGINAL), (Mem.store_access _ _ _ _ _ _ LEFT),
      (Mem.store_access _ _ _ _ _ _ CANDIDATE), (Mem.store_access _ _ _ _ _ _ RIGHT); reflexivity. }
  assert (NEXT : Mem.nextblock original = Mem.nextblock candidate).
  { rewrite (Mem.nextblock_store _ _ _ _ _ _ ORIGINAL), (Mem.nextblock_store _ _ _ _ _ _ LEFT),
      (Mem.nextblock_store _ _ _ _ _ _ CANDIDATE), (Mem.nextblock_store _ _ _ _ _ _ RIGHT); reflexivity. }
  destruct original, candidate; apply Mem.mkmem_ext; assumption.
Qed.

Lemma disjoint_stores_reorder first second initial middle final :
  stores_disjoint first second -> store_action_run first initial middle ->
  store_action_run second middle final ->
  exists swapped_middle, store_action_run second initial swapped_middle /\
    store_action_run first swapped_middle final.
Proof.
  intros INDEPENDENT FIRST SECOND.
  assert (SECOND_VALID : Mem.valid_access initial (action_chunk second) (action_block second)
    (action_offset second) Writable).
  { eapply Mem.store_valid_access_2; [exact FIRST|eapply Mem.store_valid_access_3; exact SECOND]. }
  destruct (Mem.valid_access_store _ _ _ _ (action_value second) SECOND_VALID) as [swapped SWAPPED].
  assert (FIRST_VALID : Mem.valid_access swapped (action_chunk first) (action_block first)
    (action_offset first) Writable).
  { eapply Mem.store_valid_access_1; [exact SWAPPED|eapply Mem.store_valid_access_3; exact FIRST]. }
  destruct (Mem.valid_access_store _ _ _ _ (action_value first) FIRST_VALID) as [candidate CANDIDATE].
  pose proof (@disjoint_store_results_equal first second initial middle final swapped candidate
    FIRST SECOND SWAPPED CANDIDATE INDEPENDENT) as SAME.
  subst candidate; exists swapped; auto.
Qed.

Definition compcert_store_scheduling : scheduling_model mem store_action.
Proof.
  refine {| schedule_invariant := fun _ => True;
    state_equivalent := @eq mem; state_equivalence := eq_equivalence;
    instruction_run := store_action_run; independent := stores_disjoint |}.
  - intros; exact I.
  - intros action before after before' SAME RUN; subst before'; exists after; auto.
  - intros first second initial middle final _ INDEPENDENT FIRST SECOND.
    destruct (disjoint_stores_reorder INDEPENDENT FIRST SECOND) as [swapped [SWAPPED CANDIDATE]].
    exists swapped, final; auto.
Defined.

Definition matrix_cell b index value := StoreAction Mint32 b (4 * index) (Vint (Int.repr value)).
Definition matrix_rows b := [matrix_cell b 0 1; matrix_cell b 1 2; matrix_cell b 2 11; matrix_cell b 3 12].
Definition matrix_columns b := [matrix_cell b 0 1; matrix_cell b 2 11; matrix_cell b 1 2; matrix_cell b 3 12].
Lemma matrix_interchange_certificate b :
  schedule_certificate compcert_store_scheduling (matrix_rows b) (matrix_columns b).
Proof.
  apply certificate_head, certificate_swap.
  change (stores_disjoint (matrix_cell b 1 2) (matrix_cell b 2 11)).
  unfold stores_disjoint, matrix_cell; cbn; right; left; lia.
Qed.
Theorem matrix_interchange_preserves_actual_memory b initial final :
  schedule_run compcert_store_scheduling (matrix_rows b) initial final ->
  schedule_run compcert_store_scheduling (matrix_columns b) initial final.
Proof.
  intro RUN; destruct (certified_schedule_preserves (matrix_interchange_certificate b) I RUN)
    as [candidate [EXEC SAME]]. change (final = candidate) in SAME; subst candidate; exact EXEC.
Qed.

Print Assumptions disjoint_stores_reorder.
Print Assumptions matrix_interchange_preserves_actual_memory.

Lemma four_store_schedule_decode a b c d initial final :
  schedule_run compcert_store_scheduling [a;b;c;d] initial final ->
  exists first second third,
    store_action_run a initial first /\ store_action_run b first second /\
    store_action_run c second third /\ store_action_run d third final.
Proof.
  intro RUN; inversion RUN; subst; clear RUN.
  do 3 match goal with TAIL : schedule_run _ (_ :: _) _ _ |- _ =>
    inversion TAIL; subst; clear TAIL end.
  match goal with TAIL : schedule_run _ [] _ _ |- _ => inversion TAIL; subst end.
  do 3 eexists; repeat split; eassumption.
Qed.
