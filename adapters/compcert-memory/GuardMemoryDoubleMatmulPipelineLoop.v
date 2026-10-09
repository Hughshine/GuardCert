From Stdlib Require Import List ZArith Lia.
From compcert.common Require Import AST.
From polcert.lib Require Import Misc.
From Guard Require Import ClightCountedLoop RectangularIteration.
From GuardMemory Require Import GuardMemoryDoubleAssignment GuardMemoryDoubleMatmulInstr
  GuardMemoryDoubleMatmulLoopModel GuardMemoryDoubleMatmulNestModel GuardMemoryDoublePolyhedral.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Module PL := DoubleAssignmentIRs.Loop.
Module SL := DoubleAssignmentLoop.

(** POLIRS exposes a separate generative Loop AST. Use its actual constructors
    at the extractor/codegen boundary and prove execution correspondence. *)
Definition double_matmul_pipeline_body site := PL.Instr (double_matmul_instruction site) [PL.Var 2;PL.Var 1;PL.Var 0].
Definition double_matmul_pipeline_inner site := PL.Loop (PL.Constant 0) (PL.Var 4) (double_matmul_pipeline_body site).
Definition double_matmul_pipeline_middle site := PL.Loop (PL.Constant 0) (PL.Var 2) (double_matmul_pipeline_inner site).
Definition double_matmul_pipeline_nest site := PL.Loop (PL.Constant 0) (PL.Var 0) (double_matmul_pipeline_middle site).

Lemma double_pipeline_body_correspondence site i j k parameters before after :
  SL.loop_semantics (double_matmul_loop_body site) (k::j::i::parameters) before after <->
  PL.loop_semantics (double_matmul_pipeline_body site) (k::j::i::parameters) before after.
Proof.
  rewrite double_matmul_loop_body_execution; split; intro RUN.
  - apply PL.LInstr with (wcs:=[double_matmul_write_cell site i j]) (rcs:=double_matmul_read_cells site i j k); exact RUN.
  - inversion RUN as [inst args env first final writes reads EXEC| | | | | ]; subst.
    change (DoubleAssignmentInstr.instr_semantics (double_matmul_instruction site) [i;j;k] writes reads before after) in EXEC.
    destruct EXEC as [WRITES [READS EXEC]]; rewrite double_matmul_exact_write in WRITES;
      rewrite double_matmul_exact_reads in READS; subst writes reads.
    rewrite double_matmul_exact_write in EXEC.
    unfold DoubleAssignmentInstr.instr_semantics; rewrite double_matmul_exact_write,double_matmul_exact_reads;
      repeat split; assumption || reflexivity.
Qed.
Lemma double_pipeline_range_iterations count : forall relation lower upper before after,
  upper=lower+Z.of_nat count ->
  (DoubleAssignmentIRs.Instr.IterSem.iter_semantics relation (Zrange lower upper) before after <->
   counted_iterations relation count lower before after).
Proof.
  induction count; intros relation lower upper before after LENGTH.
  - cbn in LENGTH; assert (SAME : upper=lower) by lia; subst upper.
    rewrite Zrange_empty by lia; split; intro RUN; inversion RUN; subst; constructor.
  - assert (LT : lower<upper) by (rewrite Nat2Z.inj_succ in LENGTH; lia).
    rewrite Zrange_begin by exact LT.
    assert (TAIL : upper=lower+1+Z.of_nat count) by (rewrite Nat2Z.inj_succ in LENGTH; lia).
    split; intro RUN; inversion RUN; subst; econstructor; eauto.
    + apply (proj1 (IHcount _ _ _ _ _ TAIL)); eauto.
    + apply (proj2 (IHcount _ _ _ _ _ TAIL)); eauto.
Qed.

Lemma double_pipeline_inner_correspondence site i j rows columns depth before after :
  SL.loop_semantics (double_matmul_inner_model site) [j;i;Z.of_nat rows;Z.of_nat columns;Z.of_nat depth] before after <->
  PL.loop_semantics (double_matmul_pipeline_inner site) [j;i;Z.of_nat rows;Z.of_nat columns;Z.of_nat depth] before after.
Proof.
  rewrite (@double_matmul_inner_model_iterations site i j (Z.of_nat rows) (Z.of_nat columns) depth (Z.of_nat depth) before after eq_refl).
  unfold double_matmul_pipeline_inner; split; intro RUN.
  - apply PL.LLoop; apply (proj2 (@double_pipeline_range_iterations depth _ 0 (Z.of_nat depth) before after ltac:(lia))).
    eapply counted_iterations_map; [|exact RUN]; intros k first final POINT.
    apply (proj1 (@double_pipeline_body_correspondence site i j k [Z.of_nat rows;Z.of_nat columns;Z.of_nat depth] first final)); exact POINT.
  - inversion RUN as [| | | | | env lower upper body first final ITER]; subst.
    change (DoubleAssignmentIRs.Instr.IterSem.iter_semantics (fun k=>PL.loop_semantics (double_matmul_pipeline_body site)
      [k;j;i;Z.of_nat rows;Z.of_nat columns;Z.of_nat depth]) (Zrange 0 (Z.of_nat depth)) before after) in ITER.
    apply (proj1 (@double_pipeline_range_iterations depth _ 0 (Z.of_nat depth) before after ltac:(lia))) in ITER.
    eapply counted_iterations_map; [|exact ITER]; intros k first final POINT.
    apply (proj2 (@double_pipeline_body_correspondence site i j k [Z.of_nat rows;Z.of_nat columns;Z.of_nat depth] first final)); exact POINT.
Qed.
Lemma double_pipeline_middle_correspondence site i rows columns depth before after :
  SL.loop_semantics (double_matmul_middle_model site) [i;Z.of_nat rows;Z.of_nat columns;Z.of_nat depth] before after <->
  PL.loop_semantics (double_matmul_pipeline_middle site) [i;Z.of_nat rows;Z.of_nat columns;Z.of_nat depth] before after.
Proof.
  rewrite double_matmul_middle_model_iterations; unfold double_matmul_pipeline_middle; split; intro RUN.
  - apply PL.LLoop; apply (proj2 (@double_pipeline_range_iterations columns _ 0 (Z.of_nat columns) before after ltac:(lia))).
    eapply counted_iterations_map; [|exact RUN]; intros j first final POINT.
    apply (proj1 (@double_pipeline_inner_correspondence site i j rows columns depth first final)); exact POINT.
  - inversion RUN as [| | | | | env lower upper body first final ITER]; subst.
    change (DoubleAssignmentIRs.Instr.IterSem.iter_semantics (fun j=>PL.loop_semantics (double_matmul_pipeline_inner site)
      [j;i;Z.of_nat rows;Z.of_nat columns;Z.of_nat depth]) (Zrange 0 (Z.of_nat columns)) before after) in ITER.
    apply (proj1 (@double_pipeline_range_iterations columns _ 0 (Z.of_nat columns) before after ltac:(lia))) in ITER.
    eapply counted_iterations_map; [|exact ITER]; intros j first final POINT.
    apply (proj2 (@double_pipeline_inner_correspondence site i j rows columns depth first final)); exact POINT.
Qed.
Theorem double_pipeline_nest_correspondence site rows columns depth before after :
  SL.loop_semantics (double_matmul_nest_model site) [Z.of_nat rows;Z.of_nat columns;Z.of_nat depth] before after <->
  PL.loop_semantics (double_matmul_pipeline_nest site) [Z.of_nat rows;Z.of_nat columns;Z.of_nat depth] before after.
Proof.
  rewrite double_matmul_nest_model_iterations; unfold double_matmul_pipeline_nest; split; intro RUN.
  - apply PL.LLoop; apply (proj2 (@double_pipeline_range_iterations rows _ 0 (Z.of_nat rows) before after ltac:(lia))).
    eapply counted_iterations_map; [|exact RUN]; intros i first final POINT.
    apply (proj1 (@double_pipeline_middle_correspondence site i rows columns depth first final)); exact POINT.
  - inversion RUN as [| | | | | env lower upper body first final ITER]; subst.
    change (DoubleAssignmentIRs.Instr.IterSem.iter_semantics (fun i=>PL.loop_semantics (double_matmul_pipeline_middle site)
      [i;Z.of_nat rows;Z.of_nat columns;Z.of_nat depth]) (Zrange 0 (Z.of_nat rows)) before after) in ITER.
    apply (proj1 (@double_pipeline_range_iterations rows _ 0 (Z.of_nat rows) before after ltac:(lia))) in ITER.
    eapply counted_iterations_map; [|exact ITER]; intros i first final POINT.
    apply (proj2 (@double_pipeline_middle_correspondence site i rows columns depth first final)); exact POINT.
Qed.

Print Assumptions double_pipeline_body_correspondence.
Print Assumptions double_pipeline_range_iterations.
Print Assumptions double_pipeline_nest_correspondence.
