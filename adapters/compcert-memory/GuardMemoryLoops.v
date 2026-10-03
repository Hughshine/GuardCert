From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import Misc.
From Guard Require Import ClightCountedLoop ClightLoopSyntax ClightTempFrame
  RectangularIteration ClightRectangularStore ClightRectangularGuard
  ClightRectangularLoops ClightRectangularRegion CompCertStoreSchedule.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr
  GuardMemoryRectangles GuardMemoryPolyhedral.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Module L := GuardMemoryIRs.Loop.
Module Iter := GuardMemoryInstr.IterSem.

Lemma memory_range_iterations count : forall relation lower upper before after,
  upper = lower + Z.of_nat count ->
  (Iter.iter_semantics relation (Zrange lower upper) before after <->
   counted_iterations relation count lower before after).
Proof.
  induction count; intros relation lower upper before after LENGTH.
  - cbn in LENGTH; assert (EQ : upper = lower) by lia; subst upper.
    rewrite Zrange_empty by lia; split; intro EXEC; inversion EXEC; subst; constructor.
  - assert (LT : lower < upper) by (rewrite Nat2Z.inj_succ in LENGTH; lia).
    rewrite Zrange_begin by exact LT.
    assert (TAIL : upper = lower + 1 + Z.of_nat count) by (rewrite Nat2Z.inj_succ in LENGTH; lia).
    split; intro EXEC; inversion EXEC; subst; econstructor; eauto.
    + apply (proj1 (IHcount _ _ _ _ _ TAIL)); eauto.
    + apply (proj2 (IHcount _ _ _ _ _ TAIL)); eauto.
Qed.

Definition memory_point instruction i j before after :=
  GuardMemoryInstr.instr_semantics instruction [i;j]
    (memory_write_cells instruction [i;j]) (memory_read_cells instruction [i;j]) before after.
Lemma memory_instruction_loop instruction i j env before after :
  L.loop_semantics (L.Instr instruction [L.Var 1;L.Var 0]) (j::i::env) before after <->
  memory_point instruction i j before after.
Proof.
  split.
  - intro EXEC; inversion EXEC as [inst args env' before' after' writes reads RUN| | | | | ]; subst.
    change (GuardMemoryInstr.instr_semantics instruction [i;j] writes reads before after) in RUN.
    destruct RUN as [WRITES [READS RUN]]; subst writes reads; repeat split; assumption || reflexivity.
  - intro EXEC; apply L.LInstr with
      (wcs := memory_write_cells instruction [i;j]) (rcs := memory_read_cells instruction [i;j]); exact EXEC.
Qed.

Definition memory_rectangle_loop instruction :=
  L.Loop (L.Constant 0) (L.Var 0)
    (L.Loop (L.Constant 0) (L.Var 2) (L.Instr instruction [L.Var 1;L.Var 0])).

Lemma memory_row_loop instruction i rows columns before after :
  L.loop_semantics (L.Loop (L.Constant 0) (L.Var 2) (L.Instr instruction [L.Var 1;L.Var 0]))
    [i;Z.of_nat rows;Z.of_nat columns] before after <->
  counted_iterations (memory_point instruction i) columns 0 before after.
Proof.
  split.
  - intro EXEC; inversion EXEC as [| | | | | env' lower upper code before' after' RUN]; subst.
      change (Iter.iter_semantics (fun j => L.loop_semantics
        (L.Instr instruction [L.Var 1;L.Var 0]) [j;i;Z.of_nat rows;Z.of_nat columns])
        (Zrange 0 (Z.of_nat columns)) before after) in RUN.
      apply (proj1 (@memory_range_iterations columns _ 0 (Z.of_nat columns) before after ltac:(lia))) in RUN.
      eapply counted_iterations_map; [|exact RUN]; intros j first final STEP.
      apply (proj1 (@memory_instruction_loop instruction i j [Z.of_nat rows;Z.of_nat columns] first final)); exact STEP.
  - intro EXEC; apply L.LLoop.
    apply (proj2 (@memory_range_iterations columns _ 0 (Z.of_nat columns) _ _ ltac:(lia))).
    eapply counted_iterations_map; [|exact EXEC]; intros j first final STEP.
    apply (proj2 (@memory_instruction_loop instruction i j [Z.of_nat rows;Z.of_nat columns] first final)); exact STEP.
Qed.

Theorem memory_rectangle_loop_iterations instruction rows columns before after :
  L.loop_semantics (memory_rectangle_loop instruction) [Z.of_nat rows;Z.of_nat columns] before after <->
  rectangular_iterations (memory_point instruction) rows columns before after.
Proof.
  unfold memory_rectangle_loop, rectangular_iterations; split.
  - intro EXEC; inversion EXEC as [| | | | | env' lower upper code before' after' RUN]; subst.
      change (Iter.iter_semantics (fun i => L.loop_semantics
        (L.Loop (L.Constant 0) (L.Var 2) (L.Instr instruction [L.Var 1;L.Var 0]))
        [i;Z.of_nat rows;Z.of_nat columns]) (Zrange 0 (Z.of_nat rows)) before after) in RUN.
      apply (proj1 (@memory_range_iterations rows _ 0 (Z.of_nat rows) before after ltac:(lia))) in RUN.
      eapply counted_iterations_map; [|exact RUN]; intros i first final STEP.
      apply (proj1 (@memory_row_loop instruction i rows columns first final)); exact STEP.
  - intro EXEC; apply L.LLoop.
    apply (proj2 (@memory_range_iterations rows _ 0 (Z.of_nat rows) _ _ ltac:(lia))).
    eapply counted_iterations_map; [|exact EXEC]; intros i first final STEP.
    apply (proj2 (@memory_row_loop instruction i rows columns first final)); exact STEP.
Qed.

Lemma memory_point_locations instruction i j before after :
  memory_point instruction i j before after -> runtime_locations after = runtime_locations before.
Proof. intros [_ [_ [write [reads [_ [_ [SAME RUN]]]]]]]; exact SAME. Qed.
Lemma counted_locations relation :
  (forall x before after, relation x before after -> runtime_locations after = runtime_locations before) ->
  forall count start before after, counted_iterations relation count start before after ->
    runtime_locations after = runtime_locations before.
Proof. intros FRAME count start before after EXEC; induction EXEC; [reflexivity|].
  rewrite IHEXEC; apply FRAME with (x := x); exact H. Qed.

Lemma counted_memory_lift (locations : cell_locations)
  (physical : Z -> mem -> mem -> Prop) (logical : Z -> runtime_state -> runtime_state -> Prop)
  floor upper :
  (forall x before after, floor <= x < upper ->
    (physical x before after <-> logical x (RuntimeState locations before) (RuntimeState locations after))) ->
  (forall x before after, logical x before after -> runtime_locations after = runtime_locations before) ->
  forall count start before after, floor <= start -> upper = start + Z.of_nat count ->
  (counted_iterations physical count start before after <->
   counted_iterations logical count start (RuntimeState locations before) (RuntimeState locations after)).
Proof.
  intros POINT FRAME count; induction count; intros start before after FLOOR LENGTH; split; intro EXEC.
  - inversion EXEC; subst; constructor.
  - inversion EXEC; subst; constructor.
  - rewrite Nat2Z.inj_succ in LENGTH.
    inversion EXEC as [|n x first middle last HEAD TAIL]; subst.
    eapply iterations_next with (s1 := RuntimeState locations middle).
    + apply (proj1 (POINT start before middle ltac:(lia))); exact HEAD.
    + apply (proj1 (IHcount (start + 1) middle after ltac:(lia) ltac:(lia))); exact TAIL.
  - rewrite Nat2Z.inj_succ in LENGTH.
    inversion EXEC as [|n x first middle last HEAD TAIL]; subst.
    destruct middle as [middle_locations middle_memory].
    assert (SAME : middle_locations = locations) by (exact (FRAME _ _ _ HEAD)); subst middle_locations.
    eapply iterations_next with (s1 := middle_memory).
    + apply (proj2 (POINT start before middle_memory ltac:(lia))); exact HEAD.
    + apply (proj2 (IHcount (start + 1) middle_memory after ltac:(lia) ltac:(lia))); exact TAIL.
Qed.

Theorem memory_rectangle_lift locations instruction physical rows columns before after :
  (forall i j first final, 0 <= i < Z.of_nat rows -> 0 <= j < Z.of_nat columns ->
    (physical i j first final <-> memory_point instruction i j
      (RuntimeState locations first) (RuntimeState locations final))) ->
  (rectangular_iterations physical rows columns before after <->
   L.loop_semantics (memory_rectangle_loop instruction) [Z.of_nat rows;Z.of_nat columns]
     (RuntimeState locations before) (RuntimeState locations after)).
Proof.
  intro POINT; rewrite memory_rectangle_loop_iterations; unfold rectangular_iterations.
  apply (@counted_memory_lift locations
    (fun i => counted_iterations (physical i) columns 0)
    (fun i => counted_iterations (memory_point instruction i) columns 0)
    0 (Z.of_nat rows)).
  - intros i first final IBOUND; apply counted_memory_lift with (floor := 0) (upper := Z.of_nat columns).
    + intros; apply POINT; assumption.
    + intros; eapply memory_point_locations; eauto.
    + lia.
    + lia.
  - intros i first final ROW; eapply counted_locations; [|exact ROW].
    intros; eapply memory_point_locations; eauto.
  - lia.
  - lia.
Qed.

Print Assumptions memory_rectangle_loop_iterations.
Print Assumptions memory_rectangle_lift.

Theorem memory_rectangle_columns_lift locations instruction physical rows columns before after :
  (forall i j first final, 0 <= i < Z.of_nat rows -> 0 <= j < Z.of_nat columns ->
    (physical i j first final <-> memory_point instruction i j
      (RuntimeState locations first) (RuntimeState locations final))) ->
  (rectangular_iterations (fun j i => physical i j) columns rows before after <->
   rectangular_iterations (fun j i => memory_point instruction i j) columns rows
     (RuntimeState locations before) (RuntimeState locations after)).
Proof.
  intro POINT; unfold rectangular_iterations.
  apply (@counted_memory_lift locations
    (fun j => counted_iterations (fun i => physical i j) rows 0)
    (fun j => counted_iterations (fun i => memory_point instruction i j) rows 0)
    0 (Z.of_nat columns)).
  - intros j first final JBOUND; apply counted_memory_lift with (floor := 0) (upper := Z.of_nat rows).
    + intros; apply POINT; assumption.
    + intros; eapply memory_point_locations; eauto.
    + lia.
    + lia.
  - intros j first final COLUMN; eapply counted_locations; [|exact COLUMN].
    intros i first' final' STEP; exact (@memory_point_locations instruction i j first' final' STEP).
  - lia.
  - lia.
Qed.
Print Assumptions memory_rectangle_columns_lift.
