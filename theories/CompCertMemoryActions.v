From Stdlib Require Import List Bool ZArith Lia RelationClasses.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST Values Memdata Memory.
From Guard Require Import AbstractSchedule CompCertStoreSchedule.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Record memory_location := MemoryLocation {
  location_chunk : memory_chunk;
  location_block : Values.block;
  location_offset : Z
}.
Definition location_disjoint first second :=
  location_block first <> location_block second \/
  location_offset first + size_chunk (location_chunk first) <= location_offset second \/
  location_offset second + size_chunk (location_chunk second) <= location_offset first.
Definition location_load location memory :=
  Mem.load (location_chunk location) memory (location_block location) (location_offset location).
Definition location_store location value :=
  StoreAction (location_chunk location) (location_block location) (location_offset location) value.
Fixpoint load_locations locations memory : option (list val) :=
  match locations with
  | [] => Some []
  | loc :: rest => match location_load loc memory, load_locations rest memory with
      | Some value, Some values => Some (value :: values) | _, _ => None end
  end.

(** Addresses are fixed by the instruction operands. The computation consumes
    actual loaded values; it may fail, and need not preserve mathematical
    integer arithmetic. These are semantic footprints, not C observations. *)
Record memory_action := MemoryAction {
  memory_reads : list memory_location;
  memory_write : memory_location;
  memory_compute : list val -> option val
}.
Definition memory_action_run action before after := exists operands value,
  load_locations (memory_reads action) before = Some operands /\
  memory_compute action operands = Some value /\
  store_action_run (location_store (memory_write action) value) before after.
Definition memory_actions_independent first second :=
  location_disjoint (memory_write first) (memory_write second) /\
  Forall (location_disjoint (memory_write first)) (memory_reads second) /\
  Forall (location_disjoint (memory_write second)) (memory_reads first).

Lemma location_disjoint_symmetric first second : location_disjoint first second -> location_disjoint second first.
Proof. unfold location_disjoint; intuition congruence. Qed.
Lemma location_load_store_other write value before after read :
  store_action_run (location_store write value) before after -> location_disjoint write read ->
  location_load read after = location_load read before.
Proof.
  intros STORE DISJOINT; unfold location_load; eapply Mem.load_store_other; [exact STORE|].
  unfold location_disjoint in DISJOINT; cbn [location_store action_chunk action_block action_offset]; intuition congruence.
Qed.
Lemma locations_load_store_other write value before after reads :
  store_action_run (location_store write value) before after -> Forall (location_disjoint write) reads ->
  load_locations reads after = load_locations reads before.
Proof.
  intros STORE DISJOINT; induction DISJOINT; cbn; [reflexivity|].
  rewrite (location_load_store_other STORE H), IHDISJOINT; reflexivity.
Qed.

Theorem independent_memory_actions_reorder first second before middle after :
  memory_actions_independent first second -> memory_action_run first before middle ->
  memory_action_run second middle after ->
  exists swapped, memory_action_run second before swapped /\ memory_action_run first swapped after.
Proof.
  intros [WW [WR RW]] [inputs1 [value1 [LOAD1 [COMPUTE1 STORE1]]]]
    [inputs2 [value2 [LOAD2 [COMPUTE2 STORE2]]]].
  assert (DISJOINT : stores_disjoint (location_store (memory_write first) value1)
      (location_store (memory_write second) value2)) by exact WW.
  destruct (disjoint_stores_reorder DISJOINT STORE1 STORE2) as [swapped [SECOND FIRST]].
  exists swapped; split.
  - exists inputs2,value2; split.
    + rewrite <- (locations_load_store_other STORE1 WR); exact LOAD2.
    + auto.
  - exists inputs1,value1; split.
    + rewrite (locations_load_store_other SECOND RW); exact LOAD1.
    + auto.
Qed.
Definition compcert_memory_scheduling : scheduling_model mem memory_action.
Proof.
  refine {| schedule_invariant := fun _ => True;
    state_equivalent := @eq mem; state_equivalence := eq_equivalence;
    instruction_run := memory_action_run; independent := memory_actions_independent |}.
  - intros; exact I.
  - intros action before after before' SAME RUN; subst before'; exists after; auto.
  - intros first second before middle after _ INDEPENDENT FIRST SECOND.
    destruct (independent_memory_actions_reorder INDEPENDENT FIRST SECOND) as [swapped [SWAPPED RESULT]].
    exists swapped,after; auto.
Defined.

Definition location_disjointb first second :=
  if peq (location_block first) (location_block second) then
    Z.leb (location_offset first + size_chunk (location_chunk first)) (location_offset second) ||
    Z.leb (location_offset second + size_chunk (location_chunk second)) (location_offset first)
  else true.
Lemma location_disjointb_correct first second : location_disjointb first second = true <-> location_disjoint first second.
Proof.
  unfold location_disjointb, location_disjoint; destruct (peq (location_block first) (location_block second));
    [rewrite orb_true_iff, !Z.leb_le|]; intuition congruence.
Qed.
Definition memory_actions_independentb first second :=
  location_disjointb (memory_write first) (memory_write second) &&
  forallb (location_disjointb (memory_write first)) (memory_reads second) &&
  forallb (location_disjointb (memory_write second)) (memory_reads first).
Lemma forall_location_disjointb_correct write reads : forallb (location_disjointb write) reads = true <->
  Forall (location_disjoint write) reads.
Proof.
  induction reads; cbn; [split; auto; constructor|].
  rewrite andb_true_iff, location_disjointb_correct, IHreads.
  split; [intros [HEAD REST]; constructor; assumption|intro ALL; inversion ALL; auto].
Qed.
Lemma memory_actions_independentb_correct first second : memory_actions_independentb first second = true <->
  memory_actions_independent first second.
Proof.
  unfold memory_actions_independentb, memory_actions_independent; rewrite !andb_true_iff,
    location_disjointb_correct, !forall_location_disjointb_correct; tauto.
Qed.
Print Assumptions independent_memory_actions_reorder.
Print Assumptions memory_actions_independentb_correct.
