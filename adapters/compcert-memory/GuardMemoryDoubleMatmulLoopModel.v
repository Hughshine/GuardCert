From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import Misc.
From Guard Require Import CompCertMemoryActions ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops
  GuardMemoryDoubleLocations GuardMemoryDoubleAssignment GuardMemoryDoubleMatmul
  GuardMemoryDoubleMatmulInstr GuardMemoryDoubleMatmulLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Module DL := DoubleAssignmentLoop.

(** Registry interpretation is independent of program temporaries. It uses the
    same static global facts and reached-coordinate ranges as source decoding. *)
Lemma double_matmul_static_registry_resolution ge locals site blocks layouts i j k :
  double_matmul_static ge locals site blocks -> double_matmul_layout_certificate site layouts ->
  0<=i+matmul_padding site<matmul_extent site -> 0<=j+matmul_padding site<matmul_extent site ->
  0<=k+matmul_padding site<matmul_extent site ->
  global_double_locations ge layouts (double_matmul_write_cell site i j)=
    Some (double_matmul_location site (matmul_C_block blocks) i j) /\
  resolve_cells (double_matmul_read_cells site i j k) (global_double_locations ge layouts)=
    Some (double_matmul_locations site blocks i j k).
Proof.
  intros [[_ A] [_ B] [_ C] [_ ALPHA] [_ BETA] PAD SPAN] [LA [LB [LC [LALPHA LBETA]]]] I J K.
  assert (CW : global_double_locations ge layouts (double_matmul_write_cell site i j)=
    Some (double_matmul_location site (matmul_C_block blocks) i j)).
  { unfold double_matmul_write_cell,double_matmul_location; eapply double_global_matrix_resolution; eauto. }
  split; [exact CW|]; unfold double_matmul_read_cells,double_matmul_locations; cbn [resolve_cells].
  rewrite (@double_global_scalar_resolution ge layouts (matmul_beta site) (matmul_beta_block blocks) BETA LBETA), CW,
    (@double_global_scalar_resolution ge layouts (matmul_alpha site) (matmul_alpha_block blocks) ALPHA LALPHA),
    (@double_global_matrix_resolution ge layouts (matmul_A site) (matmul_A_block blocks) (matmul_extent site)
      (i+matmul_padding site) (k+matmul_padding site) A LA I K),
    (@double_global_matrix_resolution ge layouts (matmul_B site) (matmul_B_block blocks) (matmul_extent site)
      (k+matmul_padding site) (j+matmul_padding site) B LB K J); reflexivity.
Qed.

Theorem double_matmul_action_Loop ge locals site blocks layouts i j k parameters before after :
  double_matmul_static ge locals site blocks -> double_matmul_layout_certificate site layouts ->
  0<=i+matmul_padding site<matmul_extent site -> 0<=j+matmul_padding site<matmul_extent site ->
  0<=k+matmul_padding site<matmul_extent site ->
  (double_matmul_inner_action site blocks i j k before after <->
   DL.loop_semantics (double_matmul_loop_body site) (k::j::i::parameters)
     (RuntimeState (global_double_locations ge layouts) before)
     (RuntimeState (global_double_locations ge layouts) after)).
Proof.
  intros STATIC LAYOUT I J K; rewrite double_matmul_loop_body_execution.
  destruct (@double_matmul_static_registry_resolution ge locals site blocks layouts i j k STATIC LAYOUT I J K) as [WRITE READ].
  rewrite <- (double_matmul_exact_write site i j k), <- (double_matmul_exact_reads site i j k).
  rewrite <- (double_matmul_exact_write site i j k) in WRITE;
    rewrite <- (double_matmul_exact_reads site i j k) in READ.
  rewrite (@double_assignment_resolved_instruction (double_matmul_instruction site) [i;j;k]
    (global_double_locations ge layouts) (double_matmul_location site (matmul_C_block blocks) i j)
    (double_matmul_locations site blocks i j k) before after WRITE READ); reflexivity.
Qed.

Lemma double_matmul_body_registry_frame site i j k parameters before after :
  DL.loop_semantics (double_matmul_loop_body site) (k::j::i::parameters) before after ->
  runtime_locations after=runtime_locations before.
Proof.
  rewrite double_matmul_loop_body_execution;
  intros [_ [_ [write [reads [_ [_ [SAME RUN]]]]]]]; exact SAME.
Qed.

Definition double_matmul_inner_model site := DL.Loop (DL.Constant 0) (DL.Var 4) (double_matmul_loop_body site).
Lemma double_matmul_range_iterations count : forall relation lower upper before after,
  upper=lower+Z.of_nat count ->
  (DoubleAssignmentInstr.IterSem.iter_semantics relation (Zrange lower upper) before after <->
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
Lemma double_matmul_inner_model_iterations site i j m n count upper before after :
  upper=Z.of_nat count ->
  (DL.loop_semantics (double_matmul_inner_model site) [j;i;m;n;upper] before after <->
   counted_iterations (fun k => DL.loop_semantics (double_matmul_loop_body site) [k;j;i;m;n;upper])
     count 0 before after).
Proof.
  intro LENGTH; subst upper; unfold double_matmul_inner_model; split.
  - intro RUN; inversion RUN as [| | | | | env lower upper' body first final ITER]; subst.
    change (DoubleAssignmentInstr.IterSem.iter_semantics
      (fun k => DL.loop_semantics (double_matmul_loop_body site) [k;j;i;m;n;Z.of_nat count])
      (Zrange 0 (Z.of_nat count)) before after) in ITER.
    apply (proj1 (@double_matmul_range_iterations count _ 0 (Z.of_nat count) before after ltac:(lia))); exact ITER.
  - intro ITER; apply DL.LLoop.
    apply (proj2 (@double_matmul_range_iterations count _ 0 (Z.of_nat count) before after ltac:(lia))); exact ITER.
Qed.

Theorem double_matmul_inner_model_lift ge locals site blocks layouts i j m n count upper before after :
  double_matmul_static ge locals site blocks -> double_matmul_layout_certificate site layouts ->
  0<=i+matmul_padding site<matmul_extent site -> 0<=j+matmul_padding site<matmul_extent site ->
  0<=matmul_padding site /\ upper+matmul_padding site<=matmul_extent site -> upper=Z.of_nat count ->
  (counted_iterations (double_matmul_inner_action site blocks i j) count 0 before after <->
   DL.loop_semantics (double_matmul_inner_model site) [j;i;m;n;upper]
     (RuntimeState (global_double_locations ge layouts) before)
     (RuntimeState (global_double_locations ge layouts) after)).
Proof.
  intros STATIC LAYOUT I J K LENGTH;
    rewrite (@double_matmul_inner_model_iterations site i j m n count upper _ _ LENGTH).
  apply counted_memory_lift with (floor:=0) (upper:=upper).
  - intros value first final VALUE; eapply double_matmul_action_Loop; eauto; lia.
  - intros value first final RUN; eapply double_matmul_body_registry_frame; exact RUN.
  - lia.
  - lia.
Qed.

Theorem double_matmul_original_inner_Loop fe ge locals temps memory site blocks layouts bound bound_block
  i j m n count upper after final :
  double_matmul_static ge locals site blocks -> double_matmul_layout_certificate site layouts ->
  double_global_binding ge locals bound bound_block -> matmul_C site<>bound ->
  matmul_k site<>matmul_i site -> matmul_k site<>matmul_j site ->
  0<=i+matmul_padding site<matmul_extent site -> 0<=j+matmul_padding site<matmul_extent site ->
  0<=matmul_padding site /\ upper+matmul_padding site<=matmul_extent site ->
  0<=upper<=Int64.max_signed -> upper=Z.of_nat count ->
  temps ! (matmul_i site)=Some (Vlong (Int64.repr i)) -> temps ! (matmul_j site)=Some (Vlong (Int64.repr j)) ->
  Mem.load Mint64 memory bound_block 0=Some (Vlong (Int64.repr upper)) ->
  (exec_stmt fe ge locals temps memory (double_matmul_inner_source site bound) E0 after final Out_normal <->
   DL.loop_semantics (double_matmul_inner_model site) [j;i;m;n;upper]
     (RuntimeState (global_double_locations ge layouts) memory)
     (RuntimeState (global_double_locations ge layouts) final) /\
   after=PTree.set (matmul_k site) (Vlong (Int64.repr upper)) temps).
Proof.
  intros STATIC LAYOUT BOUND OTHER_GLOBAL OTHER_I OTHER_J I J K RANGE LENGTH IV JV LOAD.
  rewrite (@double_matmul_initialized_inner_equivalence fe ge locals site blocks bound bound_block i j upper
    STATIC BOUND OTHER_GLOBAL OTHER_I OTHER_J I J K RANGE count temps memory after final LENGTH ltac:(repeat split; assumption)).
  rewrite (@double_matmul_inner_model_lift ge locals site blocks layouts i j m n count upper memory final STATIC LAYOUT I J K LENGTH).
  reflexivity.
Qed.

Print Assumptions double_matmul_static_registry_resolution.
Print Assumptions double_matmul_action_Loop.
Print Assumptions double_matmul_body_registry_frame.
Print Assumptions double_matmul_range_iterations.
Print Assumptions double_matmul_inner_model_iterations.
Print Assumptions double_matmul_inner_model_lift.
Print Assumptions double_matmul_original_inner_Loop.
