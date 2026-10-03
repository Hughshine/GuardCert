From Stdlib Require Import List ZArith Lia.
From polcert.lib Require Import Misc.
From Guard Require Import ClightCountedLoop RectangularIteration.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryPolyhedral
  GuardMemoryLoops GuardMemorySequenceLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_counted_map_nonnegative {S} (p q : Z -> S -> S -> Prop) :
  (forall x before after, 0 <= x -> p x before after -> q x before after) ->
  forall count x before after, counted_iterations p count x before after ->
    0 <= x -> counted_iterations q count x before after.
Proof.
  intros MAP count x before after RUN; induction RUN; intro FLOOR; [constructor|].
  econstructor; [apply MAP; [exact FLOOR|eassumption]|apply IHRUN; lia].
Qed.
Definition memory_ragged_sequence instructions :=
  L.Loop (L.Constant 0) (L.Var 0)
    (L.Loop (L.Constant 0) (L.Sum (L.Var 0) (L.Var 2))
      (L.Seq (memory_instruction_sequence instructions))).
Definition memory_ragged_iterations {S} (point : Z -> Z -> S -> S -> Prop) rows columns :=
  counted_iterations (fun i => counted_iterations (point i) (Z.to_nat (i+Z.of_nat columns)) 0) rows 0.
Lemma memory_ragged_row_loop instructions i rows columns before after :
  0 <= i ->
  (L.loop_semantics (L.Loop (L.Constant 0) (L.Sum (L.Var 0) (L.Var 2))
    (L.Seq (memory_instruction_sequence instructions))) [i;Z.of_nat rows;Z.of_nat columns] before after <->
   counted_iterations (memory_sequence_point instructions i) (Z.to_nat (i+Z.of_nat columns)) 0 before after).
Proof.
  intro POSITIVE; assert (LENGTH : i+Z.of_nat columns = 0+Z.of_nat (Z.to_nat (i+Z.of_nat columns)))
    by (rewrite Z2Nat.id by lia; lia).
  split.
  - intro EXEC; inversion EXEC as [| | | | | env' lower upper code before' after' RUN]; subst.
    change (Iter.iter_semantics (fun j => L.loop_semantics
      (L.Seq (memory_instruction_sequence instructions)) [j;i;Z.of_nat rows;Z.of_nat columns])
      (Zrange 0 (i+Z.of_nat columns)) before after) in RUN.
    apply (proj1 (@memory_range_iterations (Z.to_nat (i+Z.of_nat columns)) _ 0 (i+Z.of_nat columns)
      before after LENGTH)) in RUN.
    eapply counted_iterations_map; [|exact RUN]; intros j first final STEP.
    apply (proj1 (@memory_instruction_sequence_execution instructions i j [Z.of_nat rows;Z.of_nat columns] first final)); exact STEP.
  - intro EXEC; apply L.LLoop.
    apply (proj2 (@memory_range_iterations (Z.to_nat (i+Z.of_nat columns)) _ 0 (i+Z.of_nat columns) _ _ LENGTH)).
    eapply counted_iterations_map; [|exact EXEC]; intros j first final STEP.
    apply (proj2 (@memory_instruction_sequence_execution instructions i j [Z.of_nat rows;Z.of_nat columns] first final)); exact STEP.
Qed.
Theorem memory_ragged_sequence_iterations instructions rows columns before after :
  L.loop_semantics (memory_ragged_sequence instructions) [Z.of_nat rows;Z.of_nat columns] before after <->
  memory_ragged_iterations (memory_sequence_point instructions) rows columns before after.
Proof.
  unfold memory_ragged_sequence,memory_ragged_iterations; split.
  - intro EXEC; inversion EXEC as [| | | | | env' lower upper code before' after' RUN]; subst.
    change (Iter.iter_semantics (fun i => L.loop_semantics
      (L.Loop (L.Constant 0) (L.Sum (L.Var 0) (L.Var 2)) (L.Seq (memory_instruction_sequence instructions)))
      [i;Z.of_nat rows;Z.of_nat columns]) (Zrange 0 (Z.of_nat rows)) before after) in RUN.
    apply (proj1 (@memory_range_iterations rows _ 0 (Z.of_nat rows) before after ltac:(lia))) in RUN.
    eapply memory_counted_map_nonnegative; [|exact RUN|lia]; intros i first final FLOOR STEP.
    apply (proj1 (@memory_ragged_row_loop instructions i rows columns first final FLOOR)); exact STEP.
  - intro EXEC; apply L.LLoop.
    apply (proj2 (@memory_range_iterations rows _ 0 (Z.of_nat rows) _ _ ltac:(lia))).
    eapply memory_counted_map_nonnegative; [|exact EXEC|lia]; intros i first final FLOOR STEP.
    apply (proj2 (@memory_ragged_row_loop instructions i rows columns first final FLOOR)); exact STEP.
Qed.
Theorem memory_ragged_sequence_lift locations instructions physical rows columns before after :
  (forall i j first final, 0 <= i < Z.of_nat rows -> 0 <= j < i+Z.of_nat columns ->
    (physical i j first final <-> memory_sequence_point instructions i j
      (RuntimeState locations first) (RuntimeState locations final))) ->
  (memory_ragged_iterations physical rows columns before after <->
   L.loop_semantics (memory_ragged_sequence instructions) [Z.of_nat rows;Z.of_nat columns]
     (RuntimeState locations before) (RuntimeState locations after)).
Proof.
  intro POINT; rewrite memory_ragged_sequence_iterations; unfold memory_ragged_iterations.
  apply (@counted_memory_lift locations
    (fun i => counted_iterations (physical i) (Z.to_nat (i+Z.of_nat columns)) 0)
    (fun i => counted_iterations (memory_sequence_point instructions i) (Z.to_nat (i+Z.of_nat columns)) 0)
    0 (Z.of_nat rows)).
  - intros i first final IBOUND; apply counted_memory_lift with (floor := 0) (upper := i+Z.of_nat columns).
    + intros; apply POINT; assumption.
    + intros; eapply memory_sequence_point_locations; eauto.
    + lia.
    + rewrite Z2Nat.id by lia; lia.
  - intros i first final ROW; eapply counted_locations; [|exact ROW].
    intros; eapply memory_sequence_point_locations; eauto.
  - lia.
  - lia.
Qed.
Print Assumptions memory_ragged_sequence_lift.
