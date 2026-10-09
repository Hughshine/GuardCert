From Stdlib Require Import List ZArith Lia.
From compcert.common Require Import AST Memory Values Globalenvs.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import Misc.
From Guard Require Import ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryValueInstr GuardMemoryDoubleLocations
  GuardMemoryDoubleMatmulInstr GuardMemoryDoubleMatmulLoopModel GuardMemoryDoubleNestControl
  GuardMemoryLoops GuardMemoryDoubleSourceInstruction GuardMemoryDoubleSourceTransport
  GuardMemoryDoubleSourceLoopModel GuardMemoryDoubleInitializedReductionData.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint double_source_initialized_nest_model initializer reduction depth dimensions :=
  match depth with
  | O => double_source_initialized_reduction_model initializer reduction dimensions
  | S rest => SL.Loop (SL.Constant 0) (SL.Var dimensions)
      (double_source_initialized_nest_model initializer reduction rest (S dimensions)) end.
Lemma double_source_extended_environment (prefix : list Z) (value : Z) (parameters : list Z) :
  rev (prefix++[value])++parameters=value::rev prefix++parameters.
Proof. rewrite rev_app_distr; cbn [rev app]; reflexivity. Qed.
Lemma double_source_initialized_nest_iterations initializer reduction depth prefix count before after :
  SL.loop_semantics (double_source_initialized_nest_model initializer reduction (S depth) (length prefix))
    (rev prefix++[Z.of_nat count]) before after <->
  counted_iterations (fun value => SL.loop_semantics
    (double_source_initialized_nest_model initializer reduction depth (S (length prefix)))
    (value::rev prefix++[Z.of_nat count])) count 0 before after.
Proof.
  assert (BOUND : nth (length prefix) (rev prefix++[Z.of_nat count]) 0=Z.of_nat count).
  { rewrite <- (length_rev prefix); apply nth_middle. }
  cbn [double_source_initialized_nest_model]; split.
  - intro RUN; inversion RUN as [| | | | | env lower upper body first final ITER]; subst.
    cbn [SL.eval_expr] in ITER; rewrite BOUND in ITER.
    apply (proj1 (@double_matmul_range_iterations count _ 0 (Z.of_nat count) before after ltac:(lia))); exact ITER.
  - intro ITER; apply SL.LLoop; cbn [SL.eval_expr]; rewrite BOUND.
    apply (proj2 (@double_matmul_range_iterations count _ 0 (Z.of_nat count) before after ltac:(lia))); exact ITER.
Qed.
Lemma double_source_initialized_nest_frame initializer reduction depth : forall prefix count before after,
  SL.loop_semantics (double_source_initialized_nest_model initializer reduction depth (length prefix))
    (rev prefix++[Z.of_nat count]) before after -> runtime_locations after=runtime_locations before.
Proof.
  induction depth as [|depth IH]; intros prefix count before after.
  - cbn [double_source_initialized_nest_model]; unfold double_source_initialized_reduction_model.
    rewrite double_source_model_sequence; intros [middle [INITIAL LOOP]].
    rewrite double_source_reduction_loop_iterations in LOOP.
    assert (SAME : runtime_locations after=runtime_locations middle).
    { eapply counted_locations; [|exact LOOP].
      intros value first final RUN; eapply double_source_instruction_Loop_frame; exact RUN. }
    rewrite SAME; eapply double_source_instruction_Loop_frame; exact INITIAL.
  - rewrite double_source_initialized_nest_iterations; intro LOOP.
    eapply counted_locations; [|exact LOOP].
    intros value first final RUN.
    replace (S (length prefix)) with (length (prefix++[value])) in RUN
      by (rewrite app_length; cbn [length]; lia).
    rewrite <- double_source_extended_environment in RUN; eapply IH; exact RUN.
Qed.
Theorem double_source_initialized_nest_memory initializer reduction depth prefix count locations before after :
  SL.loop_semantics (double_source_initialized_nest_model initializer reduction (S depth) (length prefix))
    (rev prefix++[Z.of_nat count]) (RuntimeState locations before) (RuntimeState locations after) <->
  counted_iterations (fun value first final => SL.loop_semantics
    (double_source_initialized_nest_model initializer reduction depth (length (prefix++[value])))
    (rev (prefix++[value])++[Z.of_nat count])
    (RuntimeState locations first) (RuntimeState locations final)) count 0 before after.
Proof.
  rewrite double_source_initialized_nest_iterations; symmetry.
  apply counted_memory_lift with (floor:=0) (upper:=Z.of_nat count); try lia.
  - intros value first final RANGE; rewrite app_length; cbn [length]; rewrite Nat.add_1_r.
    rewrite double_source_extended_environment; reflexivity.
  - intros value first final RUN.
    replace (S (length prefix)) with (length (prefix++[value])) in RUN
      by (rewrite app_length; cbn [length]; lia).
    rewrite <- double_source_extended_environment in RUN; eapply double_source_initialized_nest_frame; exact RUN.
Qed.

Theorem double_source_initialized_nest_preserves_global depth description prefix count (ge : genv) layouts
  before after header header_block chunk offset :
  Genv.find_symbol ge header=Some header_block ->
  fst (value_instruction_write (double_source_instruction_model (initialized_reduction_initial_instruction description)))<>header ->
  fst (value_instruction_write (double_source_instruction_model (initialized_reduction_body_instruction description)))<>header ->
  SL.loop_semantics (double_source_initialized_nest_model
    (double_source_instruction_model (initialized_reduction_initial_instruction description))
    (double_source_instruction_model (initialized_reduction_body_instruction description)) depth (length prefix))
    (rev prefix++[Z.of_nat count])
    (RuntimeState (global_double_locations ge layouts) before)
    (RuntimeState (global_double_locations ge layouts) after) ->
  Mem.load chunk after header_block offset=Mem.load chunk before header_block offset.
Proof.
  revert prefix before after; induction depth as [|depth IH]; intros prefix before after HEADER IW RW RUN.
  - cbn [double_source_initialized_nest_model] in RUN; rewrite double_source_initialized_reduction_model_memory in RUN.
    destruct RUN as [middle [INITIAL LOOP]].
    rewrite (@counted_memory_load_frame _ header_block chunk offset
      ltac:(intros value first final ACTION; unfold double_source_model_point in ACTION;
        eapply double_source_model_preserves_global; [exact HEADER|exact RW|exact ACTION])
      count 0 middle after LOOP).
    unfold double_source_model_point in INITIAL;
      eapply double_source_model_preserves_global; [exact HEADER|exact IW|exact INITIAL].
  - rewrite double_source_initialized_nest_memory in RUN.
    eapply counted_memory_load_frame; [|exact RUN].
    intros value first final ACTION; exact (@IH (prefix++[value]) first final HEADER IW RW ACTION).
Qed.

Print Assumptions double_source_extended_environment.
Print Assumptions double_source_initialized_nest_iterations.
Print Assumptions double_source_initialized_nest_frame.
Print Assumptions double_source_initialized_nest_memory.
Print Assumptions double_source_initialized_nest_preserves_global.
