From Stdlib Require Import List ZArith Lia.
From compcert.common Require Import Values Memory.
From polcert.lib Require Import Misc.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryValueInstr GuardMemoryDoubleValue GuardMemoryDoubleAssignment
  GuardMemoryDoubleMatmulInstr GuardMemoryDoubleMatmulLoopModel GuardMemoryLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Module SL := DoubleAssignmentLoop.

Fixpoint double_source_arguments dimensions : list SL.expr :=
  match dimensions with O => [] | S rest => SL.Var rest::double_source_arguments rest end.
Lemma double_source_arguments_value prefix parameters :
  map (SL.eval_expr (rev prefix++parameters)) (double_source_arguments (length prefix))=prefix.
Proof.
  revert parameters; induction prefix as [|value rest IH]; intro parameters; cbn; [reflexivity|].
  rewrite <- app_assoc; cbn [app].
  rewrite <- (length_rev rest) at 1; rewrite nth_middle; f_equal; apply IH.
Qed.
Definition double_source_model_point instruction parameters before after :=
  DoubleAssignmentInstr.instr_semantics instruction parameters
    [exact_cell (value_instruction_write instruction) parameters]
    (map (fun access => exact_cell access parameters) (value_instruction_reads instruction)) before after.
Lemma double_source_model_point_frame instruction parameters before after :
  double_source_model_point instruction parameters before after -> runtime_locations after=runtime_locations before.
Proof. intros [_ [_ [write [reads [_ [_ [SAME RUN]]]]]]]; exact SAME. Qed.
Lemma double_source_instruction_Loop instruction prefix parameters before after :
  SL.loop_semantics (SL.Instr instruction (double_source_arguments (length prefix)))
    (rev prefix++parameters) before after <-> double_source_model_point instruction prefix before after.
Proof.
  split.
  - intro RUN; inversion RUN as [inst args env first final writes reads EXEC| | | | |]; subst.
    rewrite double_source_arguments_value in EXEC.
    destruct EXEC as [WRITES [READS EXEC]]; subst writes reads; repeat split; assumption || reflexivity.
  - intro RUN; apply SL.LInstr with (wcs:=[exact_cell (value_instruction_write instruction) prefix])
      (rcs:=map (fun access => exact_cell access prefix) (value_instruction_reads instruction)).
    rewrite double_source_arguments_value; exact RUN.
Qed.
Lemma double_source_instruction_Loop_frame instruction args env before after :
  SL.loop_semantics (SL.Instr instruction args) env before after -> runtime_locations after=runtime_locations before.
Proof.
  intro RUN; inversion RUN as [inst es values first final writes reads EXEC| | | | |]; subst.
  destruct EXEC as [_ [_ [actual_write [actual_reads [_ [_ [SAME ACTION]]]]]]]; exact SAME.
Qed.
Definition double_source_reduction_loop instruction dimensions :=
  SL.Loop (SL.Constant 0) (SL.Var dimensions)
    (SL.Instr instruction (double_source_arguments (S dimensions))).
Lemma double_source_reduction_loop_iterations instruction prefix count before after :
  SL.loop_semantics (double_source_reduction_loop instruction (length prefix))
    (rev prefix++[Z.of_nat count]) before after <->
  counted_iterations (fun value => SL.loop_semantics
    (SL.Instr instruction (double_source_arguments (S (length prefix))))
    (value::rev prefix++[Z.of_nat count])) count 0 before after.
Proof.
  assert (BOUND : nth (length prefix) (rev prefix++[Z.of_nat count]) 0=Z.of_nat count).
  { rewrite <- (length_rev prefix); apply nth_middle. }
  unfold double_source_reduction_loop; split.
  - intro RUN; inversion RUN as [| | | | | env lower upper body first final ITER]; subst.
    cbn [SL.eval_expr] in ITER; rewrite BOUND in ITER.
    apply (proj1 (@double_matmul_range_iterations count _ 0 (Z.of_nat count) before after ltac:(lia))); exact ITER.
  - intro ITER; apply SL.LLoop; cbn [SL.eval_expr].
    rewrite BOUND.
    apply (proj2 (@double_matmul_range_iterations count _ 0 (Z.of_nat count) before after ltac:(lia))); exact ITER.
Qed.
Theorem double_source_reduction_loop_memory instruction prefix count locations before after :
  SL.loop_semantics (double_source_reduction_loop instruction (length prefix))
    (rev prefix++[Z.of_nat count]) (RuntimeState locations before) (RuntimeState locations after) <->
  counted_iterations (fun value first final => double_source_model_point instruction (prefix++[value])
    (RuntimeState locations first) (RuntimeState locations final)) count 0 before after.
Proof.
  rewrite double_source_reduction_loop_iterations; symmetry.
  apply counted_memory_lift with (floor:=0) (upper:=Z.of_nat count); try lia.
  - intros value first final RANGE.
    rewrite <- (double_source_instruction_Loop instruction (prefix++[value]) [Z.of_nat count]).
    rewrite rev_app_distr; cbn [rev app]; rewrite app_length; cbn [length].
    rewrite Nat.add_1_r; reflexivity.
  - intros value first final RUN; eapply double_source_instruction_Loop_frame; exact RUN.
Qed.

Definition double_source_initialized_reduction_model initializer reduction dimensions :=
  SL.Seq (SL.SCons (SL.Instr initializer (double_source_arguments dimensions))
    (SL.SCons (double_source_reduction_loop reduction dimensions) SL.SNil)).
Lemma double_source_model_sequence first second env before after :
  SL.loop_semantics (SL.Seq (SL.SCons first (SL.SCons second SL.SNil))) env before after <->
  exists middle, SL.loop_semantics first env before middle /\ SL.loop_semantics second env middle after.
Proof.
  split.
  - intro RUN; inversion RUN; subst.
    match goal with TAIL : SL.loop_semantics (SL.Seq (SL.SCons second SL.SNil)) _ _ _ |- _ =>
      inversion TAIL; subst end.
    match goal with LAST : SL.loop_semantics (SL.Seq SL.SNil) _ _ _ |- _ => inversion LAST; subst end.
    eexists; split; eassumption.
  - intros [middle [FIRST SECOND]]; eapply SL.LSeq; [exact FIRST|].
    eapply SL.LSeq; [exact SECOND|constructor].
Qed.
Theorem double_source_initialized_reduction_model_memory initializer reduction prefix count locations before after :
  SL.loop_semantics (double_source_initialized_reduction_model initializer reduction (length prefix))
    (rev prefix++[Z.of_nat count]) (RuntimeState locations before) (RuntimeState locations after) <->
  exists middle, double_source_model_point initializer prefix (RuntimeState locations before) (RuntimeState locations middle) /\
    counted_iterations (fun value first final => double_source_model_point reduction (prefix++[value])
      (RuntimeState locations first) (RuntimeState locations final)) count 0 middle after.
Proof.
  unfold double_source_initialized_reduction_model; rewrite double_source_model_sequence; split.
  - intros [middle [FIRST SECOND]]; apply double_source_instruction_Loop in FIRST.
    destruct middle as [registry memory]; pose proof (double_source_model_point_frame FIRST) as SAME;
      cbn [runtime_locations] in SAME; subst registry.
    exists memory; split; [exact FIRST|].
    apply (proj1 (@double_source_reduction_loop_memory reduction prefix count locations memory after)); exact SECOND.
  - intros [middle [FIRST SECOND]]; exists (RuntimeState locations middle); split.
    + apply double_source_instruction_Loop; exact FIRST.
    + apply (proj2 (@double_source_reduction_loop_memory reduction prefix count locations middle after)); exact SECOND.
Qed.

Print Assumptions double_source_arguments_value.
Print Assumptions double_source_instruction_Loop.
Print Assumptions double_source_model_point_frame.
Print Assumptions double_source_reduction_loop_memory.
Print Assumptions double_source_model_sequence.
Print Assumptions double_source_initialized_reduction_model_memory.
