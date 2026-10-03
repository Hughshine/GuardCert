From Stdlib Require Import List ZArith Lia RelationClasses.
From compcert.common Require Import AST Values Memory.
From Guard Require Import AbstractSchedule SchedulePermutation CompCertMemoryActions RectangularSchedule.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition rectangle_location block stride (point : Z * Z) :=
  MemoryLocation Mint32 block (4 * (fst point * stride + snd point)).
Definition rectangle_memory_action block stride (compute : Z -> Z -> list val -> option val) point :=
  MemoryAction [rectangle_location block stride point] (rectangle_location block stride point)
    (compute (fst point) (snd point)).
Definition rectangle_memory_scheduling (block : Values.block) (stride : Z)
  (compute : Z -> Z -> list val -> option val) : scheduling_model mem (Z * Z).
Proof.
  refine {| schedule_invariant := fun _ => True;
    state_equivalent := @eq mem; state_equivalence := eq_equivalence;
    instruction_run := fun point => memory_action_run (rectangle_memory_action block stride compute point);
    independent := fun p q => memory_actions_independent
      (rectangle_memory_action block stride compute p) (rectangle_memory_action block stride compute q) |}.
  - intros; exact I.
  - intros point before after before' SAME RUN; subst before'; exists after; auto.
  - intros first second initial middle final _ INDEPENDENT FIRST SECOND.
    destruct (independent_memory_actions_reorder INDEPENDENT FIRST SECOND) as [swapped [SWAP NEXT]].
    exists swapped,final; auto.
Defined.
Lemma rectangle_memory_cells_disjoint block stride i j i' j' :
  0 <= j < stride -> 0 <= j' < stride -> (i,j) <> (i',j') ->
  location_disjoint (rectangle_location block stride (i,j)) (rectangle_location block stride (i',j')).
Proof.
  intros J J' DISTINCT; exact (@rectangle_cells_disjoint block stride (fun _ _ => Vundef)
    i j i' j' J J' DISTINCT).
Qed.
Lemma rectangle_memory_actions_independent block stride compute i j i' j' :
  0 <= j < stride -> 0 <= j' < stride -> (i,j) <> (i',j') ->
  memory_actions_independent (rectangle_memory_action block stride compute (i,j))
    (rectangle_memory_action block stride compute (i',j')).
Proof.
  intros J J' DISTINCT.
  pose proof (@rectangle_memory_cells_disjoint block stride i j i' j' J J' DISTINCT) as DISJOINT.
  unfold memory_actions_independent; cbn; split; [exact DISJOINT|]; split.
  - constructor; [exact DISJOINT|constructor].
  - constructor; [apply location_disjoint_symmetric; exact DISJOINT|constructor].
Qed.
Theorem rectangle_memory_interchange_preserves_memory block stride compute rows columns initial final :
  Z.of_nat columns <= stride ->
  schedule_run (rectangle_memory_scheduling block stride compute) (rectangle_rows rows columns) initial final ->
  schedule_run (rectangle_memory_scheduling block stride compute) (rectangle_columns rows columns) initial final.
Proof.
  intros STRIDE RUN.
  assert (CERT : schedule_certificate (rectangle_memory_scheduling block stride compute)
    (rectangle_rows rows columns) (rectangle_columns rows columns)).
  { apply independent_permutation_certificate with (eq_instruction := rectangle_point_eq).
    - apply rectangle_permutation.
    - intros [i j] [i' j'] FIRST SECOND DIFFERENT.
      destruct (@rectangle_member rows columns i j FIRST) as [_ J].
      destruct (@rectangle_member rows columns i' j' SECOND) as [_ J'].
      apply rectangle_memory_actions_independent; auto; lia. }
  destruct (certified_schedule_preserves CERT I RUN) as [candidate [EXEC SAME]].
  change (final = candidate) in SAME; subst candidate; exact EXEC.
Qed.
Print Assumptions rectangle_memory_interchange_preserves_memory.
