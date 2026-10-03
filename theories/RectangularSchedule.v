From Stdlib Require Import List ZArith Lia RelationClasses Sorting.Permutation.
From compcert.common Require Import AST Values Memdata Memory.
From Guard Require Import AbstractSchedule SchedulePermutation CompCertStoreSchedule.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint zseq start (count : nat) : list Z :=
  match count with O => [] | S rest => start :: zseq (start + 1) rest end.

Lemma zseq_bounds start count x : In x (zseq start count) ->
  start <= x < start + Z.of_nat count.
Proof.
  revert start; induction count as [|count IH]; intros start MEMBER; cbn in MEMBER; [contradiction|].
  rewrite Nat2Z.inj_succ; destruct MEMBER as [EQ|MEMBER]; [subst; lia|].
  specialize (IH (start + 1) MEMBER); lia.
Qed.

Definition rectangle_rows rows columns :=
  flat_map (fun i => map (fun j => (i,j)) (zseq 0 columns)) (zseq 0 rows).
Definition rectangle_columns rows columns :=
  flat_map (fun j => map (fun i => (i,j)) (zseq 0 rows)) (zseq 0 columns).

Lemma rectangle_member rows columns i j : In (i,j) (rectangle_rows rows columns) ->
  0 <= i < Z.of_nat rows /\ 0 <= j < Z.of_nat columns.
Proof.
  intro MEMBER; apply in_flat_map in MEMBER as [x [ROW COL]].
  apply in_map_iff in COL as [y [EQ COL]]; inversion EQ; subst.
  pose proof (@zseq_bounds 0 rows i ROW); pose proof (@zseq_bounds 0 columns j COL); lia.
Qed.

Lemma rectangle_permutation rows columns :
  Permutation (rectangle_rows rows columns) (rectangle_columns rows columns).
Proof. apply rectangular_order_permutation. Qed.

Definition rectangle_action block stride (value : Z -> Z -> val) (point : Z * Z) :=
  StoreAction Mint32 block (4 * (fst point * stride + snd point))
    (value (fst point) (snd point)).

Definition rectangle_scheduling (block : Values.block) (stride : Z)
  (value : Z -> Z -> val) : scheduling_model mem (Z * Z).
Proof.
  refine {| schedule_invariant := fun _ => True;
    state_equivalent := @eq mem; state_equivalence := eq_equivalence;
    instruction_run := fun point => store_action_run (rectangle_action block stride value point);
    independent := fun p q => stores_disjoint (rectangle_action block stride value p)
      (rectangle_action block stride value q) |}.
  - intros; exact I.
  - intros point before after before' SAME RUN; subst before'; exists after; auto.
  - intros first second initial middle final _ DISJOINT FIRST SECOND.
    destruct (disjoint_stores_reorder DISJOINT FIRST SECOND) as [swapped [SWAP NEXT]].
    exists swapped, final; auto.
Defined.

Lemma rectangle_cells_disjoint block stride value i j i' j' :
  0 <= j < stride -> 0 <= j' < stride -> (i,j) <> (i',j') ->
  stores_disjoint (rectangle_action block stride value (i,j))
    (rectangle_action block stride value (i',j')).
Proof.
  intros J J' DIFFERENT.
  assert (OFFSET : i * stride + j <> i' * stride + j').
  { intro EQ; destruct (Z.eq_dec i i') as [SAME|NE].
    - subst i'; apply DIFFERENT; f_equal; nia.
    - destruct (Z.lt_trichotomy i i') as [LT|[SAME|GT]]; nia. }
  change (block <> block \/
    4 * (i * stride + j) + 4 <= 4 * (i' * stride + j') \/
    4 * (i' * stride + j') + 4 <= 4 * (i * stride + j)).
  right; destruct (Z.lt_trichotomy (i * stride + j) (i' * stride + j')) as [LT|[EQ|GT]];
    [left|exfalso|right]; nia.
Qed.

Definition rectangle_point_eq (a b : Z * Z) : {a = b} + {a <> b}.
Proof. decide equality; apply Z.eq_dec. Defined.

Theorem rectangle_interchange_preserves_memory block stride value rows columns initial final :
  Z.of_nat columns <= stride ->
  schedule_run (rectangle_scheduling block stride value) (rectangle_rows rows columns) initial final ->
  schedule_run (rectangle_scheduling block stride value) (rectangle_columns rows columns) initial final.
Proof.
  intros STRIDE RUN.
  assert (CERT : schedule_certificate (rectangle_scheduling block stride value)
    (rectangle_rows rows columns) (rectangle_columns rows columns)).
  { apply independent_permutation_certificate with (eq_instruction := rectangle_point_eq).
    - apply rectangle_permutation.
    - intros [i j] [i' j'] FIRST SECOND DIFFERENT.
      destruct (@rectangle_member rows columns i j FIRST) as [_ J].
      destruct (@rectangle_member rows columns i' j' SECOND) as [_ J'].
      apply rectangle_cells_disjoint; auto; lia. }
  destruct (certified_schedule_preserves CERT I RUN) as [candidate [EXEC SAME]].
  change (final = candidate) in SAME; subst candidate; exact EXEC.
Qed.

Print Assumptions rectangle_interchange_preserves_memory.
