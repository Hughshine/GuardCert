From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightLoopSyntax.
From GuardMemory Require Import GuardMemoryLongControl GuardMemoryLongLoopControl GuardMemoryLongLoopSettle
  GuardMemoryDoubleLocations GuardMemoryDoubleMatmul GuardMemoryDoubleMatmulLoops GuardMemoryDoubleNestControl.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma matmul_temp_set_commute (temps : temp_env) first second a b : first<>second ->
  PTree.set first a (PTree.set second b temps)=PTree.set second b (PTree.set first a temps).
Proof.
  intro DISTINCT; apply PTree.extensionality; intro key; rewrite !PTree.gsspec.
  repeat destruct (peq _ _); subst; try congruence; reflexivity.
Qed.
Lemma matmul_middle_settled_exit site columns depth temps : matmul_j site<>matmul_k site ->
  memory_long_settled_exit (matmul_j site)
    (fun _ => PTree.set (matmul_k site) (Vlong (Int64.repr (Z.of_nat depth)))) columns 0
    (PTree.set (matmul_j site) (Vlong Int64.zero) temps)=double_matmul_middle_exit site columns depth temps.
Proof.
  intro DISTINCT; destruct columns as [|columns]; [reflexivity|].
  rewrite (@memory_long_constant_settle_exit (matmul_j site)
    (PTree.set (matmul_k site) (Vlong (Int64.repr (Z.of_nat depth))))
    ltac:(intro le; apply PTree.set2)
    ltac:(intros le word; apply matmul_temp_set_commute; congruence) columns 0).
  unfold double_matmul_middle_exit; rewrite Z.add_0_l.
  rewrite (@matmul_temp_set_commute temps (matmul_k site) (matmul_j site)
    (Vlong (Int64.repr (Z.of_nat depth))) (Vlong Int64.zero) ltac:(congruence)),PTree.set2; reflexivity.
Qed.
Lemma matmul_middle_exit_idempotent site columns depth temps :
  double_matmul_middle_exit site columns depth (double_matmul_middle_exit site columns depth temps)=
  double_matmul_middle_exit site columns depth temps.
Proof.
  unfold double_matmul_middle_exit; destruct columns; apply PTree.extensionality; intro key;
    rewrite !PTree.gsspec; repeat destruct (peq _ _); subst; reflexivity.
Qed.
Lemma matmul_middle_exit_commute site columns depth temps word :
  matmul_i site<>matmul_j site -> matmul_i site<>matmul_k site ->
  double_matmul_middle_exit site columns depth (PTree.set (matmul_i site) word temps)=
  PTree.set (matmul_i site) word (double_matmul_middle_exit site columns depth temps).
Proof.
  intros IJ IK; unfold double_matmul_middle_exit; destruct columns.
  - apply matmul_temp_set_commute; congruence.
  - rewrite (@matmul_temp_set_commute temps (matmul_k site) (matmul_i site)
      (Vlong (Int64.repr (Z.of_nat depth))) word ltac:(congruence)).
    apply matmul_temp_set_commute; congruence.
Qed.
Lemma matmul_nest_settled_exit site rows columns depth temps :
  matmul_i site<>matmul_j site -> matmul_i site<>matmul_k site ->
  memory_long_settled_exit (matmul_i site) (fun _ => double_matmul_middle_exit site columns depth) rows 0
    (PTree.set (matmul_i site) (Vlong Int64.zero) temps)=double_matmul_nest_exit site rows columns depth temps.
Proof.
  intros IJ IK; destruct rows as [|rows]; [reflexivity|].
  rewrite (@memory_long_constant_settle_exit (matmul_i site) (double_matmul_middle_exit site columns depth)
    ltac:(intro le; apply matmul_middle_exit_idempotent)
    ltac:(intros le word; apply matmul_middle_exit_commute; assumption) rows 0).
  unfold double_matmul_nest_exit; rewrite Z.add_0_l,matmul_middle_exit_commute by assumption.
  rewrite PTree.set2; reflexivity.
Qed.

Section SOURCE_NEST.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable site : double_matmul_site.
Variable blocks : double_matmul_blocks.
Variable m_bound n_bound k_bound : ident.
Variable m_block n_block k_block : block.
Variable rows columns depth : nat.
Hypothesis STATIC : double_matmul_static ge locals site blocks.
Hypothesis M_BIND : double_global_binding ge locals m_bound m_block.
Hypothesis N_BIND : double_global_binding ge locals n_bound n_block.
Hypothesis K_BIND : double_global_binding ge locals k_bound k_block.
Hypothesis M_OTHER : matmul_C site<>m_bound.
Hypothesis N_OTHER : matmul_C site<>n_bound.
Hypothesis K_OTHER : matmul_C site<>k_bound.
Hypothesis IJ : matmul_i site<>matmul_j site.
Hypothesis IK : matmul_i site<>matmul_k site.
Hypothesis JK : matmul_j site<>matmul_k site.
Hypothesis PAD : 0<=matmul_padding site.
Hypothesis M_SIZE : Z.of_nat rows+matmul_padding site<=matmul_extent site.
Hypothesis N_SIZE : Z.of_nat columns+matmul_padding site<=matmul_extent site.
Hypothesis K_SIZE : Z.of_nat depth+matmul_padding site<=matmul_extent site.
Hypothesis M_RANGE : Z.of_nat rows<=Int64.max_signed.
Hypothesis N_RANGE : Z.of_nat columns<=Int64.max_signed.
Hypothesis K_RANGE : Z.of_nat depth<=Int64.max_signed.

Definition matmul_middle_invariant i temps memory :=
  temps ! (matmul_i site)=Some (Vlong (Int64.repr i)) /\
  Mem.load Mint64 memory n_block 0=Some (Vlong (Int64.repr (Z.of_nat columns))) /\
  (0<Z.of_nat columns -> Mem.load Mint64 memory k_block 0=Some (Vlong (Int64.repr (Z.of_nat depth)))).
Definition matmul_nest_invariant (_ : temp_env) memory :=
  Mem.load Mint64 memory m_block 0=Some (Vlong (Int64.repr (Z.of_nat rows))) /\
  (0<Z.of_nat rows -> Mem.load Mint64 memory n_block 0=Some (Vlong (Int64.repr (Z.of_nat columns)))) /\
  (0<Z.of_nat rows -> 0<Z.of_nat columns -> Mem.load Mint64 memory k_block 0=Some (Vlong (Int64.repr (Z.of_nat depth)))).

Lemma matmul_middle_body_bridge i value temps memory after final :
  0<=i<Z.of_nat rows -> 0<=value<Z.of_nat columns -> matmul_middle_invariant i temps memory ->
  temps ! (matmul_j site)=Some (Vlong (Int64.repr value)) ->
  (exec_stmt fe ge locals temps memory (double_matmul_inner_source site k_bound) E0 after final Out_normal <->
   double_matmul_column_action site blocks depth i value memory final /\
   after=PTree.set (matmul_k site) (Vlong (Int64.repr (Z.of_nat depth))) temps).
Proof.
  intros I J [IV [NV KV]] JV.
  exact (@double_matmul_initialized_inner_equivalence fe ge locals site blocks k_bound k_block i value (Z.of_nat depth)
    STATIC K_BIND K_OTHER ltac:(congruence) ltac:(congruence) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(pose proof (Nat2Z.is_nonneg depth); lia) depth temps memory after final eq_refl
    ltac:(unfold matmul_inner_invariant; split; [exact IV|split; [exact JV|apply KV; lia]])).
Qed.
Lemma matmul_middle_body_invariant i value temps memory after final :
  0<=i<Z.of_nat rows -> 0<=value<Z.of_nat columns -> matmul_middle_invariant i temps memory ->
  temps ! (matmul_j site)=Some (Vlong (Int64.repr value)) ->
  exec_stmt fe ge locals temps memory (double_matmul_inner_source site k_bound) E0 after final Out_normal ->
  matmul_middle_invariant i after final.
Proof.
  intros I J INV JV RUN; destruct (proj1 (@matmul_middle_body_bridge i value temps memory after final I J INV JV) RUN) as [ACTION EXIT].
  destruct INV as [IV [NV KV]]; subst after; unfold matmul_middle_invariant; split.
  - rewrite PTree.gso by congruence; exact IV.
  - split.
    + rewrite (@double_matmul_column_preserves_load ge locals site blocks depth i value memory final
        n_bound n_block Mint64 0 STATIC (proj2 N_BIND) N_OTHER ACTION); exact NV.
    + intro ACTIVE; rewrite (@double_matmul_column_preserves_load ge locals site blocks depth i value memory final
        k_bound k_block Mint64 0 STATIC (proj2 K_BIND) K_OTHER ACTION); auto.
Qed.
Lemma matmul_middle_set_invariant i temps memory value : matmul_middle_invariant i temps memory ->
  matmul_middle_invariant i (PTree.set (matmul_j site) (Vlong (Int64.repr value)) temps) memory.
Proof. unfold matmul_middle_invariant; rewrite PTree.gso by congruence; auto. Qed.

Theorem double_matmul_middle_equivalence i temps memory after final :
  0<=i<Z.of_nat rows -> matmul_middle_invariant i temps memory ->
  (exec_stmt fe ge locals temps memory (double_matmul_middle_source site n_bound k_bound) E0 after final Out_normal <->
   double_matmul_row_action site blocks columns depth i memory final /\
   after=double_matmul_middle_exit site columns depth temps).
Proof.
  intros I INV; unfold double_matmul_middle_source,double_matmul_row_action.
  rewrite (@memory_long_initialized_settled_equivalence fe ge locals (matmul_j site)
    (double_matmul_long_condition (matmul_j site) n_bound) (double_matmul_inner_source site k_bound)
    (Z.of_nat columns) 0 (matmul_middle_invariant i) (double_matmul_column_action site blocks depth i)
    (fun _ => PTree.set (matmul_k site) (Vlong (Int64.repr (Z.of_nat depth))))
    ltac:(intros le m value [_ [LOAD _]] LIMIT VALUE; eapply double_matmul_global_test; eauto)
    (@normal_statement_execution fe ge locals _ (double_matmul_inner_normal site k_bound))
    ltac:(intros le m tr le' m' RUN; eapply writes_only_frame; [exact RUN|apply double_matmul_inner_writes|cbn; intuition])
    ltac:(intros; apply matmul_middle_body_bridge; assumption)
    ltac:(intros; eapply matmul_middle_body_invariant; eauto)
    (@matmul_middle_set_invariant i) columns temps memory after final eq_refl ltac:(lia) INV).
  rewrite matmul_middle_settled_exit by exact JK; reflexivity.
Qed.

Lemma matmul_outer_body_bridge value temps memory after final :
  0<=value<Z.of_nat rows -> matmul_nest_invariant temps memory ->
  temps ! (matmul_i site)=Some (Vlong (Int64.repr value)) ->
  (exec_stmt fe ge locals temps memory (double_matmul_middle_source site n_bound k_bound) E0 after final Out_normal <->
   double_matmul_row_action site blocks columns depth value memory final /\
   after=double_matmul_middle_exit site columns depth temps).
Proof.
  intros VALUE [MV [NV KV]] IV; apply double_matmul_middle_equivalence; [exact VALUE|].
  unfold matmul_middle_invariant; split; [exact IV|]; split.
  - apply NV; lia.
  - intro ACTIVE; apply KV; lia.
Qed.
Lemma matmul_outer_body_invariant value temps memory after final :
  0<=value<Z.of_nat rows -> matmul_nest_invariant temps memory ->
  temps ! (matmul_i site)=Some (Vlong (Int64.repr value)) ->
  exec_stmt fe ge locals temps memory (double_matmul_middle_source site n_bound k_bound) E0 after final Out_normal ->
  matmul_nest_invariant after final.
Proof.
  intros VALUE INV IV RUN; destruct (proj1 (@matmul_outer_body_bridge value temps memory after final VALUE INV IV) RUN) as [ACTION EXIT].
  destruct INV as [MV [NV KV]]; unfold matmul_nest_invariant; split.
  - rewrite (@double_matmul_row_preserves_load ge locals site blocks columns depth value memory final
      m_bound m_block Mint64 0 STATIC (proj2 M_BIND) M_OTHER ACTION); exact MV.
  - split.
    + intro ACTIVE; rewrite (@double_matmul_row_preserves_load ge locals site blocks columns depth value memory final
        n_bound n_block Mint64 0 STATIC (proj2 N_BIND) N_OTHER ACTION); auto.
    + intros ACTIVE CHILD; rewrite (@double_matmul_row_preserves_load ge locals site blocks columns depth value memory final
        k_bound k_block Mint64 0 STATIC (proj2 K_BIND) K_OTHER ACTION); auto.
Qed.

Theorem double_matmul_source_nest_equivalence temps memory after final : matmul_nest_invariant temps memory ->
  (exec_stmt fe ge locals temps memory (double_matmul_source_nest site m_bound n_bound k_bound) E0 after final Out_normal <->
   double_matmul_nest_action site blocks rows columns depth memory final /\
   after=double_matmul_nest_exit site rows columns depth temps).
Proof.
  intro INV; unfold double_matmul_source_nest,double_matmul_nest_action.
  rewrite (@memory_long_initialized_settled_equivalence fe ge locals (matmul_i site)
    (double_matmul_long_condition (matmul_i site) m_bound) (double_matmul_middle_source site n_bound k_bound)
    (Z.of_nat rows) 0 matmul_nest_invariant (double_matmul_row_action site blocks columns depth)
    (fun _ => double_matmul_middle_exit site columns depth)
    ltac:(intros le m value [LOAD _] LIMIT VALUE; eapply double_matmul_global_test; eauto)
    (@normal_statement_execution fe ge locals _ (double_matmul_middle_normal site n_bound k_bound))
    ltac:(intros le m tr le' m' RUN; eapply writes_only_frame; [exact RUN|apply double_matmul_middle_writes|cbn; intuition])
    (@matmul_outer_body_bridge) (@matmul_outer_body_invariant)
    ltac:(intros; exact H) rows temps memory after final eq_refl ltac:(lia) INV).
  rewrite matmul_nest_settled_exit by assumption; reflexivity.
Qed.
End SOURCE_NEST.

Print Assumptions matmul_middle_settled_exit.
Print Assumptions matmul_nest_settled_exit.
Print Assumptions double_matmul_middle_equivalence.
Print Assumptions double_matmul_source_nest_equivalence.
