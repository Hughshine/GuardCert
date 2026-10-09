From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Integers Maps Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From polcert.lib Require Import Misc.
From Guard Require Import ClightCountedLoop ClightTempFrame ClightLoopSyntax.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryLongControl
  GuardMemoryDoubleAffineLong GuardMemoryDoubleMatmul GuardMemoryDoubleNestControl
  GuardMemoryDoubleMatmulCapture.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition double_cache_positive cache := Ebinop Olt
  (Econst_int Int.zero memory_signed_int_type) (Etempvar cache memory_signed_int_type) memory_signed_int_type.
Definition double_cached_long cache := double_long_operand (Etempvar cache memory_signed_int_type).
(** Restore the original initialized nest's public I64 counters. An empty outer
    domain preserves j/k; an empty middle domain preserves k. No memory reads. *)
Definition double_matmul_exit_code site captures := Ssequence
  (Sifthenelse (double_cache_positive (matmul_capture_M captures))
    (Ssequence
      (Sifthenelse (double_cache_positive (matmul_capture_N captures))
        (Sset (matmul_k site) (double_cached_long (matmul_capture_K captures))) Sskip)
      (Sset (matmul_j site) (double_cached_long (matmul_capture_N captures)))) Sskip)
  (Sset (matmul_i site) (double_cached_long (matmul_capture_M captures))).
Lemma double_cached_long_execution ge locals temps memory cache value :
  signed_range value -> temps ! cache=Some (Vint (Int.repr value)) ->
  eval_expr ge locals temps memory (double_cached_long cache) (Vlong (Int64.repr value)).
Proof. intros RANGE WORD; apply double_long_operand_exact; split; [split; [reflexivity|constructor; exact WORD]|exact RANGE]. Qed.
Lemma double_cache_positive_execution ge locals temps memory cache value :
  signed_range value -> temps ! cache=Some (Vint (Int.repr value)) ->
  eval_expr ge locals temps memory (double_cache_positive cache) (Val.of_bool (0<?value)).
Proof.
  intros RANGE WORD; unfold double_cache_positive; eapply eval_Ebinop;
    [constructor|constructor; exact WORD|].
  change (Some (Val.of_bool (Int.lt Int.zero (Int.repr value)))=Some (Val.of_bool (0<?value))).
  unfold Int.lt; rewrite Int.signed_zero,Int.signed_repr by exact RANGE.
  destruct (zlt 0 value) as [POSITIVE|EMPTY];
    [rewrite (proj2 (Z.ltb_lt 0 value) POSITIVE)|rewrite (proj2 (Z.ltb_ge 0 value) ltac:(lia))]; reflexivity.
Qed.
Definition double_matmul_exit_fresh site captures :=
  forall cache, In cache [matmul_capture_M captures;matmul_capture_N captures;matmul_capture_K captures] ->
    ~ In cache [matmul_i site;matmul_j site;matmul_k site].
Lemma double_matmul_cache_set_frame site captures iterator (value : val) (temps : temp_env) cache :
  double_matmul_exit_fresh site captures -> In iterator [matmul_i site;matmul_j site;matmul_k site] ->
  In cache [matmul_capture_M captures;matmul_capture_N captures;matmul_capture_K captures] ->
  (PTree.set iterator value temps) ! cache=temps ! cache.
Proof. intros FRESH PUBLIC PRIVATE; rewrite PTree.gso; [reflexivity|intro SAME; subst; apply (FRESH _ PRIVATE); exact PUBLIC]. Qed.

Theorem double_matmul_exit_execution fe ge locals temps memory site captures rows columns depth :
  double_matmul_exit_fresh site captures ->
  signed_range (Z.of_nat rows) -> signed_range (Z.of_nat columns) -> signed_range (Z.of_nat depth) ->
  temps ! (matmul_capture_M captures)=Some (Vint (Int.repr (Z.of_nat rows))) ->
  temps ! (matmul_capture_N captures)=Some (Vint (Int.repr (Z.of_nat columns))) ->
  temps ! (matmul_capture_K captures)=Some (Vint (Int.repr (Z.of_nat depth))) ->
  exec_stmt fe ge locals temps memory (double_matmul_exit_code site captures) E0
    (double_matmul_nest_exit site rows columns depth temps) memory Out_normal.
Proof.
  intros FRESH MR NR KR M N K.
  assert (M_POS : eval_expr ge locals temps memory (double_cache_positive (matmul_capture_M captures))
    (Val.of_bool (0<?Z.of_nat rows))) by (apply double_cache_positive_execution; assumption).
  assert (N_POS : eval_expr ge locals temps memory (double_cache_positive (matmul_capture_N captures))
    (Val.of_bool (0<?Z.of_nat columns))) by (apply double_cache_positive_execution; assumption).
  assert (FRAME : forall iterator word le cache,
    In iterator [matmul_i site;matmul_j site;matmul_k site] ->
    In cache [matmul_capture_M captures;matmul_capture_N captures;matmul_capture_K captures] ->
    (PTree.set iterator word le) ! cache=le ! cache)
    by (intros; eapply double_matmul_cache_set_frame; eauto).
  unfold double_matmul_exit_code,double_matmul_nest_exit,double_matmul_middle_exit.
  destruct rows as [|rows].
  - change (0<?Z.of_nat O) with false in M_POS.
    eapply exec_Sseq_1 with (le1:=temps) (m1:=memory) (t1:=E0) (t2:=E0);
      [|apply exec_Sset; apply double_cached_long_execution; assumption].
    eapply exec_Sifthenelse; [exact M_POS|reflexivity|constructor].
  - rewrite (proj2 (Z.ltb_lt 0 (Z.of_nat (S rows))) ltac:(lia)) in M_POS.
    destruct columns as [|columns].
    + change (0<?Z.of_nat O) with false in N_POS.
      eapply exec_Sseq_1 with (le1:=PTree.set (matmul_j site) (Vlong (Int64.repr 0)) temps)
        (m1:=memory) (t1:=E0) (t2:=E0).
      * eapply exec_Sifthenelse; [exact M_POS|reflexivity|].
        eapply exec_Sseq_1 with (le1:=temps) (m1:=memory) (t1:=E0) (t2:=E0).
        -- eapply exec_Sifthenelse; [exact N_POS|reflexivity|constructor].
        -- apply exec_Sset; apply double_cached_long_execution; assumption.
      * apply exec_Sset; apply double_cached_long_execution; [exact MR|].
        rewrite FRAME by (cbn; auto); exact M.
    + rewrite (proj2 (Z.ltb_lt 0 (Z.of_nat (S columns))) ltac:(lia)) in N_POS.
      eapply exec_Sseq_1 with
        (le1:=PTree.set (matmul_j site) (Vlong (Int64.repr (Z.of_nat (S columns))))
          (PTree.set (matmul_k site) (Vlong (Int64.repr (Z.of_nat depth))) temps))
        (m1:=memory) (t1:=E0) (t2:=E0).
      * eapply exec_Sifthenelse; [exact M_POS|reflexivity|].
        eapply exec_Sseq_1 with (le1:=PTree.set (matmul_k site) (Vlong (Int64.repr (Z.of_nat depth))) temps)
          (m1:=memory) (t1:=E0) (t2:=E0).
        -- eapply exec_Sifthenelse; [exact N_POS|reflexivity|].
           apply exec_Sset; apply double_cached_long_execution; assumption.
        -- apply exec_Sset; apply double_cached_long_execution; [exact NR|].
           rewrite FRAME by (cbn; auto); exact N.
      * apply exec_Sset; apply double_cached_long_execution; [exact MR|].
        rewrite !FRAME by (cbn; auto); exact M.
Qed.
Lemma double_matmul_exit_frame site rows columns depth live before after :
  temp_agree live before after -> temp_agree live
    (double_matmul_nest_exit site rows columns depth before)
    (double_matmul_nest_exit site rows columns depth after).
Proof.
  intros FRAME key MEMBER; unfold double_matmul_nest_exit,double_matmul_middle_exit;
    destruct rows,columns; rewrite !PTree.gsspec;
    repeat destruct (peq _ _); subst; try reflexivity; apply FRAME; exact MEMBER.
Qed.

Print Assumptions double_cached_long_execution.
Print Assumptions double_cache_positive_execution.
Print Assumptions double_matmul_exit_execution.
Print Assumptions double_matmul_exit_frame.
