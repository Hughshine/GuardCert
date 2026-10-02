From Stdlib Require Import List Bool ZArith Lia RelationClasses.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST Values Memory.
From Guard Require Import AbstractSchedule AbstractScheduleChecker CompCertStoreSchedule.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A language property library: distinct element indices name disjoint
    signed32 stores in a fixed array block. Payloads may depend on the immutable
    entry snapshot; the schedule checker itself receives only indices. *)
Definition indexed_store_action block (values : nat -> Int.int) index :=
  StoreAction Mint32 block (4 * Z.of_nat index) (Vint (values index)).

Lemma indexed_stores_disjoint block values first second : first <> second ->
  stores_disjoint (indexed_store_action block values first) (indexed_store_action block values second).
Proof.
  intro DIFFERENT; change (block <> block \/
    4 * Z.of_nat first + 4 <= 4 * Z.of_nat second \/ 4 * Z.of_nat second + 4 <= 4 * Z.of_nat first).
  assert (DISTINCT : Z.of_nat first <> Z.of_nat second) by
    (intro SAME; apply DIFFERENT, Nat2Z.inj; exact SAME).
  destruct (Z_le_dec (Z.of_nat first) (Z.of_nat second)); right; [left|right]; lia.
Qed.

Definition indexed_store_model (block : Values.block) (values : nat -> Int.int) : scheduling_model mem nat.
Proof.
  refine {| schedule_invariant := fun _ => True; state_equivalent := @eq mem;
    state_equivalence := eq_equivalence;
    instruction_run := fun index => store_action_run (indexed_store_action block values index);
    independent := fun first second => first <> second |}.
  - intros; exact I.
  - intros index before after before' SAME RUN; subst before'; exists after; auto.
  - intros first second initial middle final _ DIFFERENT FIRST SECOND.
    destruct (@disjoint_stores_reorder (indexed_store_action block values first)
      (indexed_store_action block values second) initial middle final
      (indexed_stores_disjoint block values DIFFERENT) FIRST SECOND) as [swapped [LEFT RIGHT]].
    exists swapped, final; auto.
Defined.

Definition index_independentb first second := negb (Nat.eqb first second).
Lemma index_independentb_sound first second : index_independentb first second = true -> first <> second.
Proof. unfold index_independentb; rewrite Bool.negb_true_iff, Nat.eqb_neq; auto. Qed.
Definition check_index_schedule := @check_schedule nat Nat.eq_dec index_independentb.

Lemma indexed_store_schedule_map block values indices initial final :
  schedule_run (indexed_store_model block values) indices initial final ->
  schedule_run compcert_store_scheduling (map (indexed_store_action block values) indices) initial final.
Proof.
  intro RUN; induction RUN; cbn [map]; [constructor|].
  econstructor; [exact H|exact IHRUN].
Qed.
Lemma indexed_store_schedule_unmap block values indices : forall initial final,
  schedule_run compcert_store_scheduling (map (indexed_store_action block values) indices) initial final ->
  schedule_run (indexed_store_model block values) indices initial final.
Proof.
  induction indices as [|head tail IH]; intros initial final RUN; inversion RUN; subst; [constructor|].
  econstructor.
  - match goal with HEAD : instruction_run _ _ _ _ |- _ => exact HEAD end.
  - eapply IH; eassumption.
Qed.

Theorem checked_index_schedule_preserves_actual_memory block values source target initial final :
  check_index_schedule source target = true ->
  schedule_run compcert_store_scheduling (map (indexed_store_action block values) source) initial final ->
  schedule_run compcert_store_scheduling (map (indexed_store_action block values) target) initial final.
Proof.
  intros CHECK RUN; apply indexed_store_schedule_unmap in RUN.
  destruct (@check_schedule_preserves mem nat (indexed_store_model block values) Nat.eq_dec index_independentb
    index_independentb_sound source target initial final CHECK I RUN) as [candidate [EXEC SAME]].
  change (final = candidate) in SAME; subst candidate; apply indexed_store_schedule_map; exact EXEC.
Qed.

Definition matrix_index_values index := Int.repr (Z.of_nat (nth index [1%nat;2%nat;11%nat;12%nat] 0%nat)).
Definition row_index_order := [0%nat;1%nat;2%nat;3%nat].
Definition column_index_order := [0%nat;2%nat;1%nat;3%nat].
Example matrix_index_order_checked : check_index_schedule row_index_order column_index_order = true.
Proof. vm_compute; reflexivity. Qed.
Example missing_store_refused : check_index_schedule row_index_order [0%nat;2%nat;1%nat] = false.
Proof. vm_compute; reflexivity. Qed.
Example duplicated_store_refused : check_index_schedule row_index_order [0%nat;2%nat;1%nat;1%nat] = false.
Proof. vm_compute; reflexivity. Qed.

Theorem checked_matrix_interchange_preserves_actual_memory block initial final :
  check_index_schedule row_index_order column_index_order = true ->
  schedule_run compcert_store_scheduling (matrix_rows block) initial final ->
  schedule_run compcert_store_scheduling (matrix_columns block) initial final.
Proof.
  intros CHECK RUN; change (schedule_run compcert_store_scheduling
    (map (indexed_store_action block matrix_index_values) column_index_order) initial final).
  eapply checked_index_schedule_preserves_actual_memory; [exact CHECK|exact RUN].
Qed.

Print Assumptions checked_index_schedule_preserves_actual_memory.
Print Assumptions checked_matrix_interchange_preserves_actual_memory.
