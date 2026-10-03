From Stdlib Require Import List ZArith Lia.
From polcert.lib Require Import Misc.
From Guard Require Import ClightCountedLoop RectangularIteration.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryPolyhedral
  GuardMemoryLoops GuardMemoryLoopTrace GuardMemoryIndexedTrace GuardMemoryTiledRectangles.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint memory_instruction_sequence instructions : L.stmt_list :=
  match instructions with
  | [] => L.SNil
  | instruction::rest => L.SCons (L.Instr instruction [L.Var 1;L.Var 0]) (memory_instruction_sequence rest)
  end.
Definition memory_sequence_point instructions i j :=
  Iter.iter_semantics (fun instruction => memory_point instruction i j) instructions.
Definition memory_rectangle_sequence instructions :=
  L.Loop (L.Constant 0) (L.Var 0)
    (L.Loop (L.Constant 0) (L.Var 2) (L.Seq (memory_instruction_sequence instructions))).
Lemma memory_instruction_sequence_execution instructions i j rest before after :
  L.loop_semantics (L.Seq (memory_instruction_sequence instructions)) (j::i::rest) before after <->
  memory_sequence_point instructions i j before after.
Proof.
  unfold memory_sequence_point; revert before after; induction instructions; intros before after; cbn; split; intro RUN.
  - inversion RUN; subst; constructor.
  - inversion RUN; subst; constructor.
  - inversion RUN; subst; econstructor.
    + apply (proj1 (@memory_instruction_loop a i j rest _ _)); eassumption.
    + apply IHinstructions; eassumption.
  - inversion RUN; subst; eapply L.LSeq.
    + apply (proj2 (@memory_instruction_loop a i j rest _ _)); eassumption.
    + apply IHinstructions; eassumption.
Qed.
Lemma memory_sequence_row_loop instructions i rows columns before after :
  L.loop_semantics (L.Loop (L.Constant 0) (L.Var 2) (L.Seq (memory_instruction_sequence instructions)))
    [i;Z.of_nat rows;Z.of_nat columns] before after <->
  counted_iterations (memory_sequence_point instructions i) columns 0 before after.
Proof.
  split.
  - intro EXEC; inversion EXEC as [| | | | | env' lower upper code before' after' RUN]; subst.
      change (Iter.iter_semantics (fun j => L.loop_semantics
        (L.Seq (memory_instruction_sequence instructions)) [j;i;Z.of_nat rows;Z.of_nat columns])
        (Zrange 0 (Z.of_nat columns)) before after) in RUN.
      apply (proj1 (@memory_range_iterations columns _ 0 (Z.of_nat columns) before after ltac:(lia))) in RUN.
      eapply counted_iterations_map; [|exact RUN]; intros j first final STEP.
      apply (proj1 (@memory_instruction_sequence_execution instructions i j [Z.of_nat rows;Z.of_nat columns] first final)); exact STEP.
  - intro EXEC; apply L.LLoop.
    apply (proj2 (@memory_range_iterations columns _ 0 (Z.of_nat columns) _ _ ltac:(lia))).
    eapply counted_iterations_map; [|exact EXEC]; intros j first final STEP.
    apply (proj2 (@memory_instruction_sequence_execution instructions i j [Z.of_nat rows;Z.of_nat columns] first final)); exact STEP.
Qed.

Theorem memory_rectangle_sequence_iterations instructions rows columns before after :
  L.loop_semantics (memory_rectangle_sequence instructions) [Z.of_nat rows;Z.of_nat columns] before after <->
  rectangular_iterations (memory_sequence_point instructions) rows columns before after.
Proof.
  unfold memory_rectangle_sequence, rectangular_iterations; split.
  - intro EXEC; inversion EXEC as [| | | | | env' lower upper code before' after' RUN]; subst.
      change (Iter.iter_semantics (fun i => L.loop_semantics
        (L.Loop (L.Constant 0) (L.Var 2) (L.Seq (memory_instruction_sequence instructions)))
        [i;Z.of_nat rows;Z.of_nat columns]) (Zrange 0 (Z.of_nat rows)) before after) in RUN.
      apply (proj1 (@memory_range_iterations rows _ 0 (Z.of_nat rows) before after ltac:(lia))) in RUN.
      eapply counted_iterations_map; [|exact RUN]; intros i first final STEP.
      apply (proj1 (@memory_sequence_row_loop instructions i rows columns first final)); exact STEP.
  - intro EXEC; apply L.LLoop.
    apply (proj2 (@memory_range_iterations rows _ 0 (Z.of_nat rows) _ _ ltac:(lia))).
    eapply counted_iterations_map; [|exact EXEC]; intros i first final STEP.
    apply (proj2 (@memory_sequence_row_loop instructions i rows columns first final)); exact STEP.
Qed.


Lemma memory_sequence_point_locations instructions i j before after :
  memory_sequence_point instructions i j before after -> runtime_locations after = runtime_locations before.
Proof.
  intro RUN; induction RUN; [reflexivity|rewrite IHRUN; eapply memory_point_locations; eauto].
Qed.
Theorem memory_rectangle_sequence_lift locations instructions physical rows columns before after :
  (forall i j first final, 0 <= i < Z.of_nat rows -> 0 <= j < Z.of_nat columns ->
    (physical i j first final <-> memory_sequence_point instructions i j
      (RuntimeState locations first) (RuntimeState locations final))) ->
  (rectangular_iterations physical rows columns before after <->
   L.loop_semantics (memory_rectangle_sequence instructions) [Z.of_nat rows;Z.of_nat columns]
     (RuntimeState locations before) (RuntimeState locations after)).
Proof.
  intro POINT; rewrite memory_rectangle_sequence_iterations; unfold rectangular_iterations.
  apply (@counted_memory_lift locations
    (fun i => counted_iterations (physical i) columns 0)
    (fun i => counted_iterations (memory_sequence_point instructions i) columns 0)
    0 (Z.of_nat rows)).
  - intros i first final IBOUND; apply counted_memory_lift with (floor := 0) (upper := Z.of_nat columns).
    + intros; apply POINT; assumption.
    + intros; eapply memory_sequence_point_locations; eauto.
    + lia.
    + lia.
  - intros i first final ROW; eapply counted_locations; [|exact ROW].
    intros; eapply memory_sequence_point_locations; eauto.
  - lia.
  - lia.
Qed.
Definition memory_tiled_sequence_body instructions :=
  L.Guard rectangle_tiled_tail (L.Seq (memory_instruction_sequence instructions)).
Definition memory_tiled_sequence_j instructions bj :=
  L.Loop (L.Mult bj (L.Var 1)) (L.Sum (L.Mult bj (L.Var 1)) (L.Constant bj))
    (memory_tiled_sequence_body instructions).
Definition memory_tiled_sequence_i instructions bi bj :=
  L.Loop (L.Mult bi (L.Var 1)) (L.Sum (L.Mult bi (L.Var 1)) (L.Constant bi))
    (memory_tiled_sequence_j instructions bj).
Definition memory_tiled_sequence_tj instructions bi bj :=
  L.Loop (L.Constant 0) (L.Div (L.Sum (L.Var 2) (L.Constant (bj-1))) bj)
    (memory_tiled_sequence_i instructions bi bj).
Definition memory_tiled_sequence instructions bi bj :=
  L.Loop (L.Constant 0) (L.Div (L.Sum (L.Var 0) (L.Constant (bi-1))) bi)
    (memory_tiled_sequence_tj instructions bi bj).

Lemma memory_sequence_leaf_count instructions :
  memory_list_leaf_count (memory_instruction_sequence instructions) = length instructions.
Proof. induction instructions; cbn; auto. Qed.
Lemma indexed_memory_sequence_member instructions : forall base env event,
  In event (indexed_memory_list_trace base (memory_instruction_sequence instructions) env) <->
  exists position instruction, nth_error instructions position = Some instruction /\
    event = IndexedMemoryEvent (base+position)%nat
      (MemoryLoopEvent instruction env [L.eval_expr env (L.Var 1);L.eval_expr env (L.Var 0)]).
Proof.
  induction instructions as [|instruction instructions IH]; intros base env event; cbn; split.
  - contradiction.
  - intros [position [inst [ABSENT _]]]; rewrite nth_error_nil in ABSENT; discriminate.
  - intros [FIRST|REST].
    + exists O,instruction; split; [reflexivity|]; rewrite Nat.add_0_r; symmetry; exact FIRST.
    + apply IH in REST as [position [inst [NTH ->]]].
      exists (S position),inst; split; [exact NTH|f_equal; lia].
  - intros [position [inst [NTH ->]]]; destruct position.
    + inversion NTH; subst inst; left; rewrite Nat.add_0_r; reflexivity.
    + right; apply IH; exists position,inst; split; [exact NTH|f_equal; lia].
Qed.
Print Assumptions memory_rectangle_sequence_lift.
Print Assumptions indexed_memory_sequence_member.
