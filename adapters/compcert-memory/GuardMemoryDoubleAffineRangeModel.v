From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import Values Memory.
From polcert.lib Require Import Misc.
From Guard Require Import ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryValueInstr GuardMemoryLoops
  GuardMemoryDoubleSourceLoopModel GuardMemoryDoubleMatmulLoopModel GuardMemoryDoubleNestControl
  GuardMemoryLongRangeSource GuardMemoryDoubleRangeModel.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Keep the original shared parameter vector. In particular, N-2 and N-3
    remain expressions over one N instead of unrelated bound parameters.
    Actual machine encoding still requires separate range certificates. *)
Definition double_signed_affine_range_model instruction lower bound dimensions :=
  SL.Loop (SL.Constant lower) bound (SL.Instr instruction (double_source_arguments (S dimensions))).
Theorem double_signed_affine_range_model_memory instruction prefix parameters lower bound upper locations before after :
  SL.eval_expr (rev prefix++parameters) bound=upper ->
  (SL.loop_semantics (double_signed_affine_range_model instruction lower bound (length prefix))
    (rev prefix++parameters) (RuntimeState locations before) (RuntimeState locations after) <->
   counted_iterations (fun value first final => double_source_model_point instruction (prefix++[value])
     (RuntimeState locations first) (RuntimeState locations final))
     (memory_long_range_count lower upper) lower before after).
Proof.
  intro BOUND.
  assert (ITER : forall first final,
    SL.loop_semantics (double_signed_affine_range_model instruction lower bound (length prefix))
      (rev prefix++parameters) first final <->
    counted_iterations (fun value => SL.loop_semantics
      (SL.Instr instruction (double_source_arguments (S (length prefix))))
      (value::rev prefix++parameters)) (memory_long_range_count lower upper) lower first final).
  { intros first final; unfold double_signed_affine_range_model; split.
    - intro RUN; inversion RUN as [| | | | | env lo hi body initial last STEPS]; subst env lo hi body initial last.
      cbn [SL.eval_expr] in STEPS; rewrite BOUND,double_signed_range_domain in STEPS.
      apply (proj1 (@double_matmul_range_iterations (memory_long_range_count lower upper) _ lower
        (Z.max lower upper) first final ltac:(symmetry; apply memory_long_range_end))); exact STEPS.
    - intro STEPS; apply SL.LLoop; cbn [SL.eval_expr]; rewrite BOUND,double_signed_range_domain.
      apply (proj2 (@double_matmul_range_iterations (memory_long_range_count lower upper) _ lower
        (Z.max lower upper) first final ltac:(symmetry; apply memory_long_range_end))); exact STEPS. }
  rewrite ITER; symmetry; apply counted_memory_lift with (floor:=lower) (upper:=Z.max lower upper).
  - intros value first final RANGE.
    rewrite <- (double_source_instruction_Loop instruction (prefix++[value]) parameters).
    rewrite rev_app_distr; cbn [rev app]; rewrite app_length; cbn [length]; rewrite Nat.add_1_r; reflexivity.
  - intros value first final RUN; eapply double_source_instruction_Loop_frame; exact RUN.
  - lia.
  - rewrite memory_long_range_end; lia.
Qed.
Definition double_shared_header_offset_model instruction lower offset dimensions :=
  double_signed_affine_range_model instruction lower (SL.Sum (SL.Var dimensions) (SL.Constant (-offset))) dimensions.
Theorem double_shared_header_offset_model_memory instruction prefix lower offset header locations before after :
  SL.loop_semantics (double_shared_header_offset_model instruction lower offset (length prefix))
    (rev prefix++[header]) (RuntimeState locations before) (RuntimeState locations after) <->
  counted_iterations (fun value first final => double_source_model_point instruction (prefix++[value])
    (RuntimeState locations first) (RuntimeState locations final))
    (memory_long_range_count lower (header-offset)) lower before after.
Proof.
  unfold double_shared_header_offset_model; apply double_signed_affine_range_model_memory.
  cbn [SL.eval_expr]; rewrite <- (length_rev prefix),nth_middle; lia.
Qed.

Print Assumptions double_signed_affine_range_model_memory.
Print Assumptions double_shared_header_offset_model_memory.
