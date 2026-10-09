From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import CompCertMemoryActions ClightCondition ClightCountedLoop ClightTempFrame
  ClightLoopSyntax ClightRegionProgress.
From GuardMemory Require Import GuardMemoryLongLoopControl GuardMemoryLongControl GuardMemoryDoubleLocations GuardMemoryDoubleMatmul
  GuardMemoryDoubleMatmulLoops GuardMemoryDoubleHeaderFrame.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition double_matmul_middle_source site n_bound k_bound :=
  memory_long_initialized_loop (matmul_j site) (double_matmul_long_condition (matmul_j site) n_bound)
    (double_matmul_inner_source site k_bound).
Definition double_matmul_source_nest site m_bound n_bound k_bound :=
  memory_long_initialized_loop (matmul_i site) (double_matmul_long_condition (matmul_i site) m_bound)
    (double_matmul_middle_source site n_bound k_bound).
Definition double_matmul_column_action site blocks depth i j :=
  counted_iterations (double_matmul_inner_action site blocks i j) depth 0.
Definition double_matmul_row_action site blocks columns depth i :=
  counted_iterations (double_matmul_column_action site blocks depth i) columns 0.
Definition double_matmul_nest_action site blocks rows columns depth :=
  counted_iterations (double_matmul_row_action site blocks columns depth) rows 0.
Definition double_matmul_middle_exit site columns depth (temps : temp_env) :=
  PTree.set (matmul_j site) (Vlong (Int64.repr (Z.of_nat columns)))
    (match columns with O=>temps | S _=>PTree.set (matmul_k site) (Vlong (Int64.repr (Z.of_nat depth))) temps end).
Definition double_matmul_nest_exit site rows columns depth (temps : temp_env) :=
  PTree.set (matmul_i site) (Vlong (Int64.repr (Z.of_nat rows)))
    (match rows with O=>temps | S _=>double_matmul_middle_exit site columns depth temps end).

Lemma double_matmul_inner_normal site bound : normal_statement (double_matmul_inner_source site bound)=true.
Proof. reflexivity. Qed.
Lemma double_matmul_middle_normal site n_bound k_bound :
  normal_statement (double_matmul_middle_source site n_bound k_bound)=true.
Proof. reflexivity. Qed.
Lemma double_matmul_nest_normal site m_bound n_bound k_bound :
  normal_statement (double_matmul_source_nest site m_bound n_bound k_bound)=true.
Proof. reflexivity. Qed.
Lemma double_matmul_inner_writes site bound : writes_only [matmul_k site] (double_matmul_inner_source site bound).
Proof.
  unfold double_matmul_inner_source,memory_long_initialized_loop,memory_long_frontend_loop,memory_long_increment,double_matmul_body.
  repeat constructor; cbn; auto.
Qed.
Lemma double_matmul_middle_writes site n_bound k_bound :
  writes_only [matmul_j site;matmul_k site] (double_matmul_middle_source site n_bound k_bound).
Proof.
  unfold double_matmul_middle_source,double_matmul_inner_source,memory_long_initialized_loop,
    memory_long_frontend_loop,memory_long_increment,double_matmul_body.
  repeat first [apply writes_sequence|apply writes_loop|apply writes_if|apply writes_assign|
    apply writes_skip|apply writes_break|apply writes_set]; cbn; auto.
Qed.

Lemma double_matmul_action_preserves_load ge locals site blocks i j k before after
  header header_block chunk offset :
  double_matmul_static ge locals site blocks -> Genv.find_symbol ge header=Some header_block ->
  matmul_C site<>header -> double_matmul_inner_action site blocks i j k before after ->
  Mem.load chunk after header_block offset=Mem.load chunk before header_block offset.
Proof.
  intros STATIC HEADER DIFFERENT [values [value [READS [COMPUTE STORE]]]].
  destruct (matmul_static_C STATIC) as [_ C].
  change (Mem.store Mfloat64 before (matmul_C_block blocks)
    (8*((i+matmul_padding site)*matmul_extent site+(j+matmul_padding site))) value=Some after) in STORE.
  eapply global_store_preserves_other_load; eauto.
Qed.
Lemma counted_memory_load_frame relation header_block chunk offset
  (FRAME : forall value before after, relation value before after ->
    Mem.load chunk after header_block offset=Mem.load chunk before header_block offset) :
  forall count value before after, counted_iterations relation count value before after ->
    Mem.load chunk after header_block offset=Mem.load chunk before header_block offset.
Proof. intros count value before after RUN; induction RUN; [reflexivity|rewrite IHRUN; eapply FRAME; eauto]. Qed.
Lemma double_matmul_column_preserves_load ge locals site blocks depth i j before after
  header header_block chunk offset :
  double_matmul_static ge locals site blocks -> Genv.find_symbol ge header=Some header_block ->
  matmul_C site<>header -> double_matmul_column_action site blocks depth i j before after ->
  Mem.load chunk after header_block offset=Mem.load chunk before header_block offset.
Proof.
  intros STATIC HEADER DIFFERENT RUN; eapply counted_memory_load_frame; [|exact RUN].
  intros; eapply double_matmul_action_preserves_load; eauto.
Qed.
Lemma double_matmul_row_preserves_load ge locals site blocks columns depth i before after
  header header_block chunk offset :
  double_matmul_static ge locals site blocks -> Genv.find_symbol ge header=Some header_block ->
  matmul_C site<>header -> double_matmul_row_action site blocks columns depth i before after ->
  Mem.load chunk after header_block offset=Mem.load chunk before header_block offset.
Proof.
  intros STATIC HEADER DIFFERENT RUN; eapply counted_memory_load_frame; [|exact RUN].
  intros; eapply double_matmul_column_preserves_load; eauto.
Qed.

Lemma double_matmul_global_test ge locals temps memory iterator header header_block value upper :
  double_global_binding ge locals header header_block ->
  Mem.load Mint64 memory header_block 0=Some (Vlong (Int64.repr upper)) ->
  temps ! iterator=Some (Vlong (Int64.repr value)) ->
  0<=value<=upper -> upper<=Int64.max_signed ->
  expression_test (double_matmul_long_condition iterator header) (Entry ge locals temps memory) (value <? upper).
Proof.
  intros BINDING LOAD VALUE LIMIT RANGE; exists (Val.of_bool (value <? upper)); split.
  - eapply GuardMemoryLongControl.memory_long_test_execution; try reflexivity.
    + pose proof Int64.min_signed_neg; lia.
    + pose proof Int64.min_signed_neg; lia.
    + constructor; exact VALUE.
    + eapply memory_global_long_execution; eauto.
  - destruct (value <? upper); reflexivity.
Qed.

Print Assumptions double_matmul_nest_normal.
Print Assumptions double_matmul_middle_writes.
Print Assumptions double_matmul_action_preserves_load.
Print Assumptions double_matmul_row_preserves_load.
Print Assumptions double_matmul_global_test.
