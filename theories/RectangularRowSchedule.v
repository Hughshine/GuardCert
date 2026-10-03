From Stdlib Require Import List ZArith Lia RelationClasses.
From compcert.common Require Import AST Values Memory.
From Guard Require Import AbstractSchedule ScheduleInterleave CompCertMemoryActions RectangularSchedule RectangularMemorySchedule.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma zseq_nodup start count : NoDup (zseq start count).
Proof.
  revert start; induction count; intro start; cbn; constructor.
  - intro MEMBER; pose proof (@zseq_bounds (start+1) count start MEMBER); lia.
  - apply IHcount.
Qed.
Definition rectangle_row_action block stride (compute : Z -> Z -> list val -> option val) (point : Z * Z) :=
  MemoryAction [rectangle_location block stride (fst point,0)] (rectangle_location block stride point)
    (compute (fst point) (snd point)).
Definition rectangle_row_scheduling (block : Values.block) (stride : Z)
  (compute : Z -> Z -> list val -> option val) : scheduling_model mem (Z * Z).
Proof.
  refine {| schedule_invariant := fun _ => True;
    state_equivalent := @eq mem; state_equivalence := eq_equivalence;
    instruction_run := fun point => memory_action_run (rectangle_row_action block stride compute point);
    independent := fun p q => memory_actions_independent
      (rectangle_row_action block stride compute p) (rectangle_row_action block stride compute q) |}.
  - intros; exact I.
  - intros point before after before' SAME RUN; subst before'; exists after; auto.
  - intros first second initial middle final _ INDEPENDENT FIRST SECOND.
    destruct (independent_memory_actions_reorder INDEPENDENT FIRST SECOND) as [swapped [SWAP NEXT]].
    exists swapped,final; auto.
Defined.
Lemma rectangle_different_rows_independent block stride compute i j i' j' :
  0 < stride -> 0 <= j < stride -> 0 <= j' < stride -> i <> i' ->
  memory_actions_independent (rectangle_row_action block stride compute (i,j))
    (rectangle_row_action block stride compute (i',j')).
Proof.
  intros POS J J' DISTINCT.
  unfold memory_actions_independent; cbn; split.
  - apply rectangle_memory_cells_disjoint; auto; congruence.
  - split; constructor.
    + apply rectangle_memory_cells_disjoint; auto; [lia|congruence].
    + constructor.
    + apply rectangle_memory_cells_disjoint; auto; [lia|congruence].
    + constructor.
Qed.
Theorem rectangle_row_interchange_preserves_memory block stride compute rows columns initial final :
  0 < stride -> Z.of_nat columns <= stride ->
  schedule_run (rectangle_row_scheduling block stride compute) (rectangle_rows rows columns) initial final ->
  schedule_run (rectangle_row_scheduling block stride compute) (rectangle_columns rows columns) initial final.
Proof.
  intros POS STRIDE RUN.
  assert (CERT : schedule_certificate (rectangle_row_scheduling block stride compute)
    (rectangle_rows rows columns) (rectangle_columns rows columns)).
  { apply rectangular_row_order_certificate; [apply zseq_nodup|].
    intros i i' j j' I I' DISTINCT J J'.
    pose proof (@zseq_bounds 0 columns j J); pose proof (@zseq_bounds 0 columns j' J').
    apply rectangle_different_rows_independent; auto; lia. }
  destruct (certified_schedule_preserves CERT I RUN) as [candidate [EXEC SAME]].
  change (final = candidate) in SAME; subst candidate; exact EXEC.
Qed.
Print Assumptions zseq_nodup.
Print Assumptions rectangle_row_interchange_preserves_memory.
