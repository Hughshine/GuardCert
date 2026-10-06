From Stdlib Require Import List ZArith Lia.
From polcert.lib Require Import Misc.
From Guard Require Import ClightCountedLoop RectangularIteration.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles GuardMemoryPolyhedral GuardMemoryLoops
  GuardMemoryNaryCompute GuardMemoryNaryLoops GuardMemoryNaryLift GuardMemoryScalarLoops
  GuardMemoryParametricLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Actual loop arguments contain two coordinates followed by the original
    entry context. The inner affine bound can depend on the outer coordinate;
    there is no invented independent inner-count parameter. *)
Definition memory_affine_parameter_arguments arity :=
  [L.Var 1; L.Var 0] ++ memory_variables_from 2 arity.
Lemma memory_affine_parameter_arguments_value i j context :
  map (L.eval_expr (j::i::context))
    (memory_affine_parameter_arguments (length context)) = [i;j]++context.
Proof.
  unfold memory_affine_parameter_arguments; rewrite map_app; cbn.
  change (i::j::map (L.eval_expr ([j;i]++context))
    (memory_variables_from (length [j;i]) (length context)) = i::j::context).
  rewrite memory_variables_from_values; reflexivity.
Qed.
Fixpoint memory_affine_parameter_instructions arity instructions : L.stmt_list :=
  match instructions with
  | [] => L.SNil
  | instruction::rest => L.SCons
      (L.Instr instruction (memory_affine_parameter_arguments arity))
      (memory_affine_parameter_instructions arity rest)
  end.
Definition memory_affine_parameter_sequence arity expression instructions :=
  L.Loop (L.Constant 0) (L.Var 0)
    (L.Loop (L.Constant 0) expression
      (L.Seq (memory_affine_parameter_instructions arity instructions))).
Definition memory_affine_parameter_point instructions context i j :=
  memory_nary_sequence_point instructions ([i;j]++context).
Lemma memory_affine_parameter_instruction_execution instruction i j context before after :
  (L.loop_semantics (L.Instr instruction (memory_affine_parameter_arguments (length context)))
    (j::i::context) before after <->
    memory_nary_point instruction ([i;j]++context) before after).
Proof.
  split; intro RUN.
  - inversion RUN as [inst args env' first final writes reads EXEC| | | | | ]; subst.
    rewrite memory_affine_parameter_arguments_value in EXEC.
    change (GuardMemoryInstr.instr_semantics instruction ([i;j]++context) writes reads before after) in EXEC.
    destruct EXEC as [WRITES [READS EXEC]]; subst; repeat split; assumption || reflexivity.
  - apply L.LInstr with (wcs := memory_write_cells instruction ([i;j]++context))
      (rcs := memory_read_cells instruction ([i;j]++context)).
    rewrite memory_affine_parameter_arguments_value; exact RUN.
Qed.
Lemma memory_affine_parameter_instructions_execution instructions i j context before after :
  (L.loop_semantics (L.Seq (memory_affine_parameter_instructions (length context) instructions))
    (j::i::context) before after <-> memory_affine_parameter_point instructions context i j before after).
Proof.
  unfold memory_affine_parameter_point,memory_nary_sequence_point.
  revert before after; induction instructions; intros before after; cbn; split; intro RUN.
  - inversion RUN; subst; constructor.
  - inversion RUN; subst; constructor.
  - inversion RUN; subst; econstructor.
    + apply (proj1 (@memory_affine_parameter_instruction_execution a i j context before _)); eassumption.
    + apply IHinstructions; eassumption.
  - inversion RUN; subst; eapply L.LSeq.
    + apply (proj2 (@memory_affine_parameter_instruction_execution a i j context before _)); eassumption.
    + apply IHinstructions; eassumption.
Qed.
Lemma memory_affine_parameter_row_execution instructions expression i context before after :
  0 <= L.eval_expr (i::context) expression ->
  (L.loop_semantics (L.Loop (L.Constant 0) expression
    (L.Seq (memory_affine_parameter_instructions (length context) instructions)))
    (i::context) before after <->
   counted_iterations (memory_affine_parameter_point instructions context i)
    (Z.to_nat (L.eval_expr (i::context) expression)) 0 before after).
Proof.
  intro NONNEGATIVE; set (upper := L.eval_expr (i::context) expression).
  assert (LENGTH : upper = 0+Z.of_nat (Z.to_nat upper)) by (rewrite Z2Nat.id by assumption; lia).
  split.
  - intro EXEC; inversion EXEC as [| | | | | env' lower upper' code before' after' RUN]; subst.
    change (Iter.iter_semantics (fun j => L.loop_semantics
      (L.Seq (memory_affine_parameter_instructions (length context) instructions)) (j::i::context))
      (Zrange 0 upper) before after) in RUN.
    apply (proj1 (@memory_range_iterations (Z.to_nat upper) _ 0 upper before after LENGTH)) in RUN.
    eapply counted_iterations_map; [|exact RUN]; intros j first final STEP.
    apply (proj1 (@memory_affine_parameter_instructions_execution instructions i j context first final)); exact STEP.
  - intro EXEC; apply L.LLoop.
    apply (proj2 (@memory_range_iterations (Z.to_nat upper) _ 0 upper before after LENGTH)).
    eapply counted_iterations_map; [|exact EXEC]; intros j first final STEP.
    apply (proj2 (@memory_affine_parameter_instructions_execution instructions i j context first final)); exact STEP.
Qed.
Theorem memory_affine_parameter_sequence_iterations instructions expression rows parameters before after :
  (forall i, 0 <= i < Z.of_nat rows -> 0 <= L.eval_expr (i::Z.of_nat rows::parameters) expression) ->
  (L.loop_semantics (memory_affine_parameter_sequence (length (Z.of_nat rows::parameters)) expression instructions)
    (Z.of_nat rows::parameters) before after <->
   memory_parametric_iterations (memory_affine_parameter_point instructions (Z.of_nat rows::parameters))
    rows parameters expression before after).
Proof.
  intro NONNEGATIVE; unfold memory_affine_parameter_sequence,memory_parametric_iterations; split.
  - intro EXEC; inversion EXEC as [| | | | | env' lower upper code before' after' RUN]; subst.
    change (Iter.iter_semantics (fun i => L.loop_semantics
      (L.Loop (L.Constant 0) expression
        (L.Seq (memory_affine_parameter_instructions (length (Z.of_nat rows::parameters)) instructions)))
      (i::Z.of_nat rows::parameters)) (Zrange 0 (Z.of_nat rows)) before after) in RUN.
    apply (proj1 (@memory_range_iterations rows _ 0 (Z.of_nat rows) before after ltac:(lia))) in RUN.
    eapply memory_counted_map_bounded with (floor := 0) (upper := Z.of_nat rows); [|exact RUN|lia|lia].
    intros i first final RANGE STEP.
    apply (proj1 (@memory_affine_parameter_row_execution instructions expression i _ first final (NONNEGATIVE i RANGE))); exact STEP.
  - intro EXEC; apply L.LLoop.
    apply (proj2 (@memory_range_iterations rows _ 0 (Z.of_nat rows) before after ltac:(lia))).
    eapply memory_counted_map_bounded with (floor := 0) (upper := Z.of_nat rows); [|exact EXEC|lia|lia].
    intros i first final RANGE STEP.
    apply (proj2 (@memory_affine_parameter_row_execution instructions expression i _ first final (NONNEGATIVE i RANGE))); exact STEP.
Qed.
Theorem memory_affine_parameter_sequence_lift locations instructions physical rows parameters expression before after :
  (forall i, 0 <= i < Z.of_nat rows -> 0 <= L.eval_expr (i::Z.of_nat rows::parameters) expression) ->
  (forall i j first final, 0 <= i < Z.of_nat rows ->
    0 <= j < L.eval_expr (i::Z.of_nat rows::parameters) expression ->
    (physical i j first final <-> memory_affine_parameter_point instructions (Z.of_nat rows::parameters) i j
      (RuntimeState locations first) (RuntimeState locations final))) ->
  (memory_parametric_iterations physical rows parameters expression before after <->
   L.loop_semantics (memory_affine_parameter_sequence (length (Z.of_nat rows::parameters)) expression instructions)
    (Z.of_nat rows::parameters) (RuntimeState locations before) (RuntimeState locations after)).
Proof.
  intros NONNEGATIVE POINT; rewrite memory_affine_parameter_sequence_iterations by exact NONNEGATIVE.
  unfold memory_parametric_iterations.
  apply (@counted_memory_lift locations
    (fun i => counted_iterations (physical i) (Z.to_nat (L.eval_expr (i::Z.of_nat rows::parameters) expression)) 0)
    (fun i => counted_iterations (memory_affine_parameter_point instructions (Z.of_nat rows::parameters) i)
      (Z.to_nat (L.eval_expr (i::Z.of_nat rows::parameters) expression)) 0) 0 (Z.of_nat rows)).
  - intros i first final RANGE; apply counted_memory_lift with
      (floor := 0) (upper := L.eval_expr (i::Z.of_nat rows::parameters) expression).
    + intros; apply POINT; assumption.
    + intros; eapply memory_nary_sequence_locations; eauto.
    + lia.
    + rewrite Z2Nat.id by (apply NONNEGATIVE; exact RANGE); lia.
  - intros i first final RUN; eapply counted_locations; [|exact RUN].
    intros; eapply memory_nary_sequence_locations; eauto.
  - lia.
  - lia.
Qed.

Print Assumptions memory_affine_parameter_sequence_iterations.
Print Assumptions memory_affine_parameter_sequence_lift.
