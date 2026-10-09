From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import Misc.
From Guard Require Import ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryDoubleAssignment GuardMemoryDoubleLocations
  GuardMemoryDoubleMatmul GuardMemoryDoubleMatmulInstr GuardMemoryDoubleMatmulLoops
  GuardMemoryDoubleMatmulLoopModel GuardMemoryDoubleNestControl GuardMemoryDoubleMatmulNest.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Module NL := DoubleAssignmentLoop.

Definition double_matmul_middle_model site :=
  NL.Loop (NL.Constant 0) (NL.Var 2) (double_matmul_inner_model site).
Definition double_matmul_nest_model site :=
  NL.Loop (NL.Constant 0) (NL.Var 0) (double_matmul_middle_model site).

Lemma double_matmul_middle_model_iterations site i rows columns depth before after :
  NL.loop_semantics (double_matmul_middle_model site) [i;Z.of_nat rows;Z.of_nat columns;Z.of_nat depth] before after <->
  counted_iterations (fun j => NL.loop_semantics (double_matmul_inner_model site)
    [j;i;Z.of_nat rows;Z.of_nat columns;Z.of_nat depth]) columns 0 before after.
Proof.
  unfold double_matmul_middle_model; split.
  - intro RUN; inversion RUN as [| | | | | env lower upper body first final ITER]; subst.
    change (DoubleAssignmentInstr.IterSem.iter_semantics (fun j => NL.loop_semantics (double_matmul_inner_model site)
      [j;i;Z.of_nat rows;Z.of_nat columns;Z.of_nat depth]) (Zrange 0 (Z.of_nat columns)) before after) in ITER.
    apply (proj1 (@double_matmul_range_iterations columns _ 0 (Z.of_nat columns) before after ltac:(lia))); exact ITER.
  - intro ITER; apply NL.LLoop.
    apply (proj2 (@double_matmul_range_iterations columns _ 0 (Z.of_nat columns) before after ltac:(lia))); exact ITER.
Qed.
Lemma double_matmul_nest_model_iterations site rows columns depth before after :
  NL.loop_semantics (double_matmul_nest_model site) [Z.of_nat rows;Z.of_nat columns;Z.of_nat depth] before after <->
  counted_iterations (fun i => NL.loop_semantics (double_matmul_middle_model site)
    [i;Z.of_nat rows;Z.of_nat columns;Z.of_nat depth]) rows 0 before after.
Proof.
  unfold double_matmul_nest_model; split.
  - intro RUN; inversion RUN as [| | | | | env lower upper body first final ITER]; subst.
    change (DoubleAssignmentInstr.IterSem.iter_semantics (fun i => NL.loop_semantics (double_matmul_middle_model site)
      [i;Z.of_nat rows;Z.of_nat columns;Z.of_nat depth]) (Zrange 0 (Z.of_nat rows)) before after) in ITER.
    apply (proj1 (@double_matmul_range_iterations rows _ 0 (Z.of_nat rows) before after ltac:(lia))); exact ITER.
  - intro ITER; apply NL.LLoop.
    apply (proj2 (@double_matmul_range_iterations rows _ 0 (Z.of_nat rows) before after ltac:(lia))); exact ITER.
Qed.
Lemma double_matmul_inner_model_frame site i j rows columns depth before after :
  NL.loop_semantics (double_matmul_inner_model site) [j;i;Z.of_nat rows;Z.of_nat columns;Z.of_nat depth] before after ->
  runtime_locations after=runtime_locations before.
Proof.
  rewrite (@double_matmul_inner_model_iterations site i j (Z.of_nat rows) (Z.of_nat columns) depth (Z.of_nat depth) before after eq_refl).
  intro ITER; eapply counted_locations; [|exact ITER].
  intros value first final RUN; exact (@double_matmul_body_registry_frame site i j value
    [Z.of_nat rows;Z.of_nat columns;Z.of_nat depth] first final RUN).
Qed.
Lemma double_matmul_middle_model_frame site i rows columns depth before after :
  NL.loop_semantics (double_matmul_middle_model site) [i;Z.of_nat rows;Z.of_nat columns;Z.of_nat depth] before after ->
  runtime_locations after=runtime_locations before.
Proof.
  rewrite double_matmul_middle_model_iterations; intro ITER; eapply counted_locations; [|exact ITER].
  intros j first final RUN; exact (@double_matmul_inner_model_frame site i j rows columns depth first final RUN).
Qed.

Theorem double_matmul_row_model_lift ge locals site blocks layouts rows columns depth i before after :
  double_matmul_static ge locals site blocks -> double_matmul_layout_certificate site layouts ->
  0<=matmul_padding site -> Z.of_nat rows+matmul_padding site<=matmul_extent site ->
  Z.of_nat columns+matmul_padding site<=matmul_extent site -> Z.of_nat depth+matmul_padding site<=matmul_extent site ->
  0<=i<Z.of_nat rows ->
  (double_matmul_row_action site blocks columns depth i before after <->
   NL.loop_semantics (double_matmul_middle_model site) [i;Z.of_nat rows;Z.of_nat columns;Z.of_nat depth]
     (RuntimeState (global_double_locations ge layouts) before)
     (RuntimeState (global_double_locations ge layouts) after)).
Proof.
  intros STATIC LAYOUT PAD MS NS KS I; rewrite double_matmul_middle_model_iterations; unfold double_matmul_row_action.
  apply counted_memory_lift with (floor:=0) (upper:=Z.of_nat columns).
  - intros j first final J; eapply double_matmul_inner_model_lift with (locals:=locals); eauto; lia.
  - intros j first final RUN; eapply double_matmul_inner_model_frame; exact RUN.
  - lia.
  - lia.
Qed.
Theorem double_matmul_nest_model_lift ge locals site blocks layouts rows columns depth before after :
  double_matmul_static ge locals site blocks -> double_matmul_layout_certificate site layouts ->
  0<=matmul_padding site -> Z.of_nat rows+matmul_padding site<=matmul_extent site ->
  Z.of_nat columns+matmul_padding site<=matmul_extent site -> Z.of_nat depth+matmul_padding site<=matmul_extent site ->
  (double_matmul_nest_action site blocks rows columns depth before after <->
   NL.loop_semantics (double_matmul_nest_model site) [Z.of_nat rows;Z.of_nat columns;Z.of_nat depth]
     (RuntimeState (global_double_locations ge layouts) before)
     (RuntimeState (global_double_locations ge layouts) after)).
Proof.
  intros STATIC LAYOUT PAD MS NS KS; rewrite double_matmul_nest_model_iterations; unfold double_matmul_nest_action.
  apply counted_memory_lift with (floor:=0) (upper:=Z.of_nat rows).
  - intros i first final I; eapply double_matmul_row_model_lift with (locals:=locals); eassumption.
  - intros i first final RUN; eapply double_matmul_middle_model_frame; exact RUN.
  - lia.
  - lia.
Qed.

Theorem double_matmul_original_nest_Loop fe ge locals site blocks layouts m_bound n_bound k_bound
  m_block n_block k_block rows columns depth temps memory after final :
  double_matmul_static ge locals site blocks -> double_matmul_layout_certificate site layouts ->
  double_global_binding ge locals m_bound m_block -> double_global_binding ge locals n_bound n_block ->
  double_global_binding ge locals k_bound k_block ->
  matmul_C site<>m_bound -> matmul_C site<>n_bound -> matmul_C site<>k_bound ->
  matmul_i site<>matmul_j site -> matmul_i site<>matmul_k site -> matmul_j site<>matmul_k site ->
  0<=matmul_padding site -> Z.of_nat rows+matmul_padding site<=matmul_extent site ->
  Z.of_nat columns+matmul_padding site<=matmul_extent site -> Z.of_nat depth+matmul_padding site<=matmul_extent site ->
  Z.of_nat rows<=Int64.max_signed -> Z.of_nat columns<=Int64.max_signed -> Z.of_nat depth<=Int64.max_signed ->
  matmul_nest_invariant m_block n_block k_block rows columns depth temps memory ->
  (exec_stmt fe ge locals temps memory (double_matmul_source_nest site m_bound n_bound k_bound) E0 after final Out_normal <->
   NL.loop_semantics (double_matmul_nest_model site) [Z.of_nat rows;Z.of_nat columns;Z.of_nat depth]
     (RuntimeState (global_double_locations ge layouts) memory)
     (RuntimeState (global_double_locations ge layouts) final) /\
   after=double_matmul_nest_exit site rows columns depth temps).
Proof.
  intros STATIC LAYOUT MB NB KB MO NO KO IJ IK JK PAD MS NS KS MR NR KR INV.
  rewrite (@double_matmul_source_nest_equivalence fe ge locals site blocks m_bound n_bound k_bound
    m_block n_block k_block rows columns depth STATIC MB NB KB MO NO KO IJ IK JK PAD MS NS KS MR NR KR
    temps memory after final INV).
  rewrite (@double_matmul_nest_model_lift ge locals site blocks layouts rows columns depth memory final STATIC LAYOUT PAD MS NS KS).
  reflexivity.
Qed.

Print Assumptions double_matmul_nest_model_iterations.
Print Assumptions double_matmul_inner_model_frame.
Print Assumptions double_matmul_middle_model_frame.
Print Assumptions double_matmul_row_model_lift.
Print Assumptions double_matmul_nest_model_lift.
Print Assumptions double_matmul_original_nest_Loop.
