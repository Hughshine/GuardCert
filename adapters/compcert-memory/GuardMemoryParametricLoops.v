From Stdlib Require Import List ZArith Lia.
From polcert.lib Require Import Misc.
From Guard Require Import ClightCountedLoop RectangularIteration.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryPolyhedral
  GuardMemoryLoops GuardMemorySequenceLoops GuardMemoryRaggedLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_counted_map_bounded {S} (p q : Z -> S -> S -> Prop) floor upper :
  (forall value before after, floor <= value < upper -> p value before after -> q value before after) ->
  forall count value before after, counted_iterations p count value before after ->
    floor <= value -> value + Z.of_nat count <= upper -> counted_iterations q count value before after.
Proof.
  intros MAP count value before after RUN; induction RUN; intros FLOOR END.
  - constructor.
  - econstructor.
    + apply MAP; [rewrite Nat2Z.inj_succ in END; lia|eassumption].
    + apply IHRUN; [lia|rewrite Nat2Z.inj_succ in END; lia].
Qed.

Definition memory_parametric_sequence bound_expression instructions :=
  L.Loop (L.Constant 0) (L.Var 0)
    (L.Loop (L.Constant 0) bound_expression
      (L.Seq (memory_instruction_sequence instructions))).
Definition memory_parametric_iterations {S} (point : Z -> Z -> S -> S -> Prop)
  rows parameters bound_expression :=
  counted_iterations (fun i => counted_iterations (point i)
    (Z.to_nat (L.eval_expr (i::Z.of_nat rows::parameters) bound_expression)) 0) rows 0.
Lemma memory_parametric_row_loop instructions expression i rows parameters before after :
  0 <= L.eval_expr (i::Z.of_nat rows::parameters) expression ->
  (L.loop_semantics (L.Loop (L.Constant 0) expression
    (L.Seq (memory_instruction_sequence instructions))) (i::Z.of_nat rows::parameters) before after <->
   counted_iterations (memory_sequence_point instructions i)
    (Z.to_nat (L.eval_expr (i::Z.of_nat rows::parameters) expression)) 0 before after).
Proof.
  intro NONNEGATIVE.
  set (upper := L.eval_expr (i::Z.of_nat rows::parameters) expression).
  assert (LENGTH : upper = 0+Z.of_nat (Z.to_nat upper)) by (rewrite Z2Nat.id by assumption; lia).
  split.
  - intro EXEC; inversion EXEC as [| | | | | env' lower upper' code before' after' RUN]; subst.
    change (Iter.iter_semantics (fun j => L.loop_semantics
      (L.Seq (memory_instruction_sequence instructions)) (j::i::Z.of_nat rows::parameters))
      (Zrange 0 upper) before after) in RUN.
    apply (proj1 (@memory_range_iterations (Z.to_nat upper) _ 0 upper before after LENGTH)) in RUN.
    eapply counted_iterations_map; [|exact RUN]; intros j first final STEP.
    apply (proj1 (@memory_instruction_sequence_execution instructions i j (Z.of_nat rows::parameters) first final)); exact STEP.
  - intro EXEC; apply L.LLoop.
    apply (proj2 (@memory_range_iterations (Z.to_nat upper) _ 0 upper before after LENGTH)).
    eapply counted_iterations_map; [|exact EXEC]; intros j first final STEP.
    apply (proj2 (@memory_instruction_sequence_execution instructions i j (Z.of_nat rows::parameters) first final)); exact STEP.
Qed.
Theorem memory_parametric_sequence_iterations instructions expression rows parameters before after :
  (forall i, 0 <= i < Z.of_nat rows -> 0 <= L.eval_expr (i::Z.of_nat rows::parameters) expression) ->
  (L.loop_semantics (memory_parametric_sequence expression instructions) (Z.of_nat rows::parameters) before after <->
   memory_parametric_iterations (memory_sequence_point instructions) rows parameters expression before after).
Proof.
  intro NONNEGATIVE; unfold memory_parametric_sequence,memory_parametric_iterations; split.
  - intro EXEC; inversion EXEC as [| | | | | env' lower upper code before' after' RUN]; subst.
    change (Iter.iter_semantics (fun i => L.loop_semantics
      (L.Loop (L.Constant 0) expression (L.Seq (memory_instruction_sequence instructions)))
      (i::Z.of_nat rows::parameters)) (Zrange 0 (Z.of_nat rows)) before after) in RUN.
    apply (proj1 (@memory_range_iterations rows _ 0 (Z.of_nat rows) before after ltac:(lia))) in RUN.
    eapply memory_counted_map_bounded with (floor := 0) (upper := Z.of_nat rows); [|exact RUN|lia|lia].
    intros i first final RANGE STEP.
    apply (proj1 (@memory_parametric_row_loop instructions expression i rows parameters first final (NONNEGATIVE i RANGE))); exact STEP.
  - intro EXEC; apply L.LLoop.
    apply (proj2 (@memory_range_iterations rows _ 0 (Z.of_nat rows) before after ltac:(lia))).
    eapply memory_counted_map_bounded with (floor := 0) (upper := Z.of_nat rows); [|exact EXEC|lia|lia].
    intros i first final RANGE STEP.
    apply (proj2 (@memory_parametric_row_loop instructions expression i rows parameters first final (NONNEGATIVE i RANGE))); exact STEP.
Qed.
Print Assumptions memory_parametric_sequence_iterations.

Lemma memory_parametric_first {State} (point : Z -> Z -> State -> State -> Prop) rows parameters expression before after :
  rows <> O -> 0 < L.eval_expr (0::Z.of_nat rows::parameters) expression ->
  memory_parametric_iterations point rows parameters expression before after ->
  exists middle, point 0 0 before middle.
Proof.
  intros ROWS WIDTH RUN; destruct rows as [|rows]; [contradiction|].
  unfold memory_parametric_iterations in RUN; inversion RUN; subst.
  assert (NONZERO : Z.to_nat (L.eval_expr (0::Z.of_nat (S rows)::parameters) expression) <> O)
    by (intro ZERO; pose proof (Z2Nat.id (L.eval_expr (0::Z.of_nat (S rows)::parameters) expression) ltac:(lia)) as SAME;
      rewrite ZERO in SAME; cbn in SAME; lia).
  match goal with ROW : counted_iterations _ (Z.to_nat _) _ _ _ |- _ =>
    destruct (Z.to_nat (L.eval_expr (0::Z.of_nat (S rows)::parameters) expression)) as [|columns];
    [contradiction|]; inversion ROW; subst; eexists; eassumption end.
Qed.
Theorem memory_parametric_sequence_lift locations instructions physical rows parameters expression before after :
  (forall i, 0 <= i < Z.of_nat rows -> 0 <= L.eval_expr (i::Z.of_nat rows::parameters) expression) ->
  (forall i j first final, 0 <= i < Z.of_nat rows ->
    0 <= j < L.eval_expr (i::Z.of_nat rows::parameters) expression ->
    (physical i j first final <-> memory_sequence_point instructions i j
      (RuntimeState locations first) (RuntimeState locations final))) ->
  (memory_parametric_iterations physical rows parameters expression before after <->
   L.loop_semantics (memory_parametric_sequence expression instructions) (Z.of_nat rows::parameters)
     (RuntimeState locations before) (RuntimeState locations after)).
Proof.
  intros NONNEGATIVE POINT; rewrite memory_parametric_sequence_iterations by exact NONNEGATIVE.
  unfold memory_parametric_iterations.
  apply (@counted_memory_lift locations
    (fun i => counted_iterations (physical i) (Z.to_nat (L.eval_expr (i::Z.of_nat rows::parameters) expression)) 0)
    (fun i => counted_iterations (memory_sequence_point instructions i)
      (Z.to_nat (L.eval_expr (i::Z.of_nat rows::parameters) expression)) 0) 0 (Z.of_nat rows)).
  - intros i first final RANGE; apply counted_memory_lift with
      (floor := 0) (upper := L.eval_expr (i::Z.of_nat rows::parameters) expression).
    + intros; apply POINT; assumption.
    + intros; eapply memory_sequence_point_locations; eauto.
    + lia.
    + rewrite Z2Nat.id by (apply NONNEGATIVE; exact RANGE); lia.
  - intros i first final RUN; eapply counted_locations; [|exact RUN].
    intros; eapply memory_sequence_point_locations; eauto.
  - lia.
  - lia.
Qed.
Print Assumptions memory_parametric_sequence_lift.
