From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import Values Memory.
From polcert.lib Require Import Misc.
From Guard Require Import ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryValueInstr GuardMemoryLoops
  GuardMemoryDoubleSourceLoopModel GuardMemoryDoubleMatmulLoopModel GuardMemoryDoubleNestControl
  GuardMemoryLongRangeSource GuardMemoryLongLoopSettle.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition double_signed_range_model instruction lower dimensions :=
  SL.Loop (SL.Constant lower) (SL.Var dimensions)
    (SL.Instr instruction (double_source_arguments (S dimensions))).
Lemma double_signed_range_domain lower upper : Zrange lower upper=Zrange lower (Z.max lower upper).
Proof.
  destruct (Z_le_dec lower upper).
  - rewrite Z.max_r by lia; reflexivity.
  - rewrite Z.max_l by lia; rewrite !Zrange_empty by lia; reflexivity.
Qed.
Lemma double_signed_range_model_iterations instruction prefix lower upper before after :
  SL.loop_semantics (double_signed_range_model instruction lower (length prefix))
    (rev prefix++[upper]) before after <->
  counted_iterations (fun value => SL.loop_semantics
    (SL.Instr instruction (double_source_arguments (S (length prefix))))
    (value::rev prefix++[upper])) (memory_long_range_count lower upper) lower before after.
Proof.
  assert (BOUND : nth (length prefix) (rev prefix++[upper]) 0=upper).
  { rewrite <- (length_rev prefix); apply nth_middle. }
  unfold double_signed_range_model; split.
  - intro RUN; inversion RUN as [| | | | | env lo hi body first final ITER]; subst.
    cbn [SL.eval_expr] in ITER; rewrite BOUND,double_signed_range_domain in ITER.
    apply (proj1 (@double_matmul_range_iterations (memory_long_range_count lower upper) _ lower
      (Z.max lower upper) before after ltac:(symmetry; apply memory_long_range_end))); exact ITER.
  - intro ITER; apply SL.LLoop; cbn [SL.eval_expr]; rewrite BOUND,double_signed_range_domain.
    apply (proj2 (@double_matmul_range_iterations (memory_long_range_count lower upper) _ lower
      (Z.max lower upper) before after ltac:(symmetry; apply memory_long_range_end))); exact ITER.
Qed.
Theorem double_signed_range_model_memory instruction prefix lower upper locations before after :
  SL.loop_semantics (double_signed_range_model instruction lower (length prefix))
    (rev prefix++[upper]) (RuntimeState locations before) (RuntimeState locations after) <->
  counted_iterations (fun value first final => double_source_model_point instruction (prefix++[value])
    (RuntimeState locations first) (RuntimeState locations final))
    (memory_long_range_count lower upper) lower before after.
Proof.
  rewrite double_signed_range_model_iterations; symmetry.
  apply counted_memory_lift with (floor:=lower) (upper:=Z.max lower upper).
  - intros value first final RANGE.
    rewrite <- (double_source_instruction_Loop instruction (prefix++[value]) [upper]).
    rewrite rev_app_distr; cbn [rev app]; rewrite app_length; cbn [length]; rewrite Nat.add_1_r; reflexivity.
  - intros value first final RUN; eapply double_source_instruction_Loop_frame; exact RUN.
  - lia.
  - rewrite memory_long_range_end; lia.
Qed.
Theorem memory_long_range_identity_exit iterator lower upper temps :
  memory_long_settled_exit iterator (fun _ le=>le) (memory_long_range_count lower upper) lower
    (PTree.set iterator (Vlong (Int64.repr lower)) temps)=
  PTree.set iterator (Vlong (Int64.repr (Z.max lower upper))) temps.
Proof.
  remember (memory_long_range_count lower upper) as count eqn:COUNT.
  assert (END : lower+Z.of_nat count=Z.max lower upper) by (rewrite COUNT; apply memory_long_range_end).
  destruct count as [|count].
  - cbn [memory_long_settled_exit]; rewrite <- END; cbn; rewrite Z.add_0_r; reflexivity.
  - rewrite (@memory_long_constant_settle_exit iterator (fun le=>le) ltac:(reflexivity)
      ltac:(reflexivity) count lower),PTree.set2,END; reflexivity.
Qed.

Print Assumptions double_signed_range_domain.
Print Assumptions double_signed_range_model_iterations.
Print Assumptions double_signed_range_model_memory.
Print Assumptions memory_long_range_identity_exit.
