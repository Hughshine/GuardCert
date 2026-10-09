From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Memory Values Globalenvs.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import Misc.
From Guard Require Import ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryValueInstr GuardMemoryDoubleLocations
  GuardMemoryDoubleSourceInstruction GuardMemoryDoubleSourceTransport GuardMemoryDoubleSourceLoopModel
  GuardMemoryDoubleInitializedNestModel GuardMemoryDoubleInitializedNestExit
  GuardMemoryDoubleMatmulLoopModel GuardMemoryLoops GuardMemoryLongLoopSettle GuardMemoryDoubleNestControl.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma double_header_instruction_Loop instruction prefix count before after :
  SL.loop_semantics (SL.Instr instruction (double_source_arguments (S (length prefix))))
    (rev prefix++[Z.of_nat count]) before after <->
  double_source_model_point instruction (Z.of_nat count::prefix) before after.
Proof.
  replace (rev prefix++[Z.of_nat count]) with (rev (Z.of_nat count::prefix)++[])
    by (cbn [rev]; rewrite app_nil_r; reflexivity).
  change (SL.loop_semantics (SL.Instr instruction (double_source_arguments (length (Z.of_nat count::prefix))))
    (rev (Z.of_nat count::prefix)++[]) before after <->
    double_source_model_point instruction (Z.of_nat count::prefix) before after).
  apply double_source_instruction_Loop.
Qed.

Fixpoint double_header_nest_model instruction depth dimensions :=
  match depth with
  | O => SL.Instr instruction (double_source_arguments (S dimensions))
  | S rest => SL.Loop (SL.Constant 0) (SL.Var dimensions)
      (double_header_nest_model instruction rest (S dimensions)) end.
Lemma double_header_nest_iterations instruction depth prefix count before after :
  SL.loop_semantics (double_header_nest_model instruction (S depth) (length prefix))
    (rev prefix++[Z.of_nat count]) before after <->
  counted_iterations (fun value => SL.loop_semantics
    (double_header_nest_model instruction depth (S (length prefix)))
    (value::rev prefix++[Z.of_nat count])) count 0 before after.
Proof.
  assert (BOUND : nth (length prefix) (rev prefix++[Z.of_nat count]) 0=Z.of_nat count)
    by (rewrite <- (length_rev prefix); apply nth_middle).
  cbn [double_header_nest_model]; split.
  - intro RUN; inversion RUN as [| | | | | env lower upper body first final ITER]; subst.
    cbn [SL.eval_expr] in ITER; rewrite BOUND in ITER.
    apply (proj1 (@double_matmul_range_iterations count _ 0 (Z.of_nat count) before after ltac:(lia))); exact ITER.
  - intro ITER; apply SL.LLoop; cbn [SL.eval_expr]; rewrite BOUND.
    apply (proj2 (@double_matmul_range_iterations count _ 0 (Z.of_nat count) before after ltac:(lia))); exact ITER.
Qed.
Lemma double_header_nest_frame instruction depth : forall prefix count before after,
  SL.loop_semantics (double_header_nest_model instruction depth (length prefix))
    (rev prefix++[Z.of_nat count]) before after -> runtime_locations after=runtime_locations before.
Proof.
  induction depth as [|depth IH]; intros prefix count before after.
  - cbn [double_header_nest_model]; apply double_source_instruction_Loop_frame.
  - rewrite double_header_nest_iterations; intro RUN; eapply counted_locations; [|exact RUN].
    intros value first final CHILD.
    replace (S (length prefix)) with (length (prefix++[value])) in CHILD
      by (rewrite app_length; cbn [length]; lia).
    rewrite <- double_source_extended_environment in CHILD; eapply IH; exact CHILD.
Qed.
Theorem double_header_nest_memory instruction depth prefix count locations before after :
  SL.loop_semantics (double_header_nest_model instruction (S depth) (length prefix))
    (rev prefix++[Z.of_nat count]) (RuntimeState locations before) (RuntimeState locations after) <->
  counted_iterations (fun value first final => SL.loop_semantics
    (double_header_nest_model instruction depth (length (prefix++[value])))
    (rev (prefix++[value])++[Z.of_nat count])
    (RuntimeState locations first) (RuntimeState locations final)) count 0 before after.
Proof.
  rewrite double_header_nest_iterations; symmetry.
  apply counted_memory_lift with (floor:=0) (upper:=Z.of_nat count); try lia.
  - intros value first final RANGE; rewrite app_length; cbn [length]; rewrite Nat.add_1_r.
    rewrite double_source_extended_environment; reflexivity.
  - intros value first final RUN.
    replace (S (length prefix)) with (length (prefix++[value])) in RUN
      by (rewrite app_length; cbn [length]; lia).
    rewrite <- double_source_extended_environment in RUN; eapply double_header_nest_frame; exact RUN.
Qed.
Theorem double_header_nest_preserves_global depth description prefix count (ge : genv) layouts
  before after header header_block chunk offset :
  Genv.find_symbol ge header=Some header_block ->
  fst (value_instruction_write (double_source_instruction_model description))<>header ->
  SL.loop_semantics (double_header_nest_model (double_source_instruction_model description) depth (length prefix))
    (rev prefix++[Z.of_nat count]) (RuntimeState (global_double_locations ge layouts) before)
    (RuntimeState (global_double_locations ge layouts) after) ->
  Mem.load chunk after header_block offset=Mem.load chunk before header_block offset.
Proof.
  revert prefix before after; induction depth as [|depth IH]; intros prefix before after HEADER WRITE RUN.
  - cbn [double_header_nest_model] in RUN; apply double_header_instruction_Loop in RUN.
    unfold double_source_model_point in RUN; eapply double_source_model_preserves_global; eassumption.
  - rewrite double_header_nest_memory in RUN; eapply counted_memory_load_frame; [|exact RUN].
    intros value first final CHILD; exact (@IH (prefix++[value]) first final HEADER WRITE CHILD).
Qed.


Print Assumptions double_header_instruction_Loop.
Print Assumptions double_header_nest_iterations.
Print Assumptions double_header_nest_frame.
Print Assumptions double_header_nest_memory.
Print Assumptions double_header_nest_preserves_global.
