From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightCountedLoop.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleInitializedNestExit
  GuardMemoryDoubleInitializedExitCode GuardMemoryDoubleMatmulExit GuardMemoryDoubleReductionNestModel.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition double_reduction_exit_code iterators cache := match iterators with
  | [] => Sskip
  | iterator::rest => Ssequence
      (Sifthenelse (double_cache_positive cache) (double_initialized_restore_words rest cache) Sskip)
      (Sset iterator (double_cached_long cache)) end.
Theorem double_reduction_exit_code_execution fe ge locals temps memory iterators cache count :
  ~ In cache iterators -> signed_range (Z.of_nat count) -> temps ! cache=Some (Vint (Int.repr (Z.of_nat count))) ->
  exec_stmt fe ge locals temps memory (double_reduction_exit_code iterators cache) E0
    (double_reduction_nest_exit iterators count temps) memory Out_normal.
Proof.
  intros FRESH RANGE WORD; destruct iterators as [|iterator rest].
  - rewrite double_reduction_nest_exit_nil; constructor.
  - unfold double_reduction_exit_code; rewrite double_reduction_nest_exit_cons.
    pose proof (@double_cache_positive_execution ge locals temps memory cache (Z.of_nat count) RANGE WORD) as TEST.
    destruct count as [|count].
    + change (0<?Z.of_nat O) with false in TEST.
      eapply exec_Sseq_1 with (le1:=temps) (m1:=memory) (t1:=E0) (t2:=E0).
      * eapply exec_Sifthenelse; [exact TEST|reflexivity|constructor].
      * apply exec_Sset, double_cached_long_execution; assumption.
    + rewrite (proj2 (Z.ltb_lt 0 (Z.of_nat (S count))) ltac:(lia)) in TEST.
      change (exec_stmt fe ge locals temps memory
        (Ssequence (Sifthenelse (double_cache_positive cache) (double_initialized_restore_words rest cache) Sskip)
          (Sset iterator (double_cached_long cache))) E0
        (PTree.set iterator (Vlong (Int64.repr (Z.of_nat (S count))))
          (double_source_set_words rest (Vlong (Int64.repr (Z.of_nat (S count)))) temps)) memory Out_normal).
      eapply exec_Sseq_1 with (le1:=double_source_set_words rest (Vlong (Int64.repr (Z.of_nat (S count)))) temps)
        (m1:=memory) (t1:=E0) (t2:=E0).
      * eapply exec_Sifthenelse; [exact TEST|reflexivity|].
        apply double_initialized_restore_words_execution;
          [intro MEMBER; apply FRESH; cbn; auto|exact RANGE|exact WORD].
      * apply exec_Sset, double_cached_long_execution; [exact RANGE|].
        rewrite double_source_set_words_frame; [exact WORD|intro MEMBER; apply FRESH; cbn; auto].
Qed.
Lemma double_reduction_exit_agree iterators count live before after :
  temp_agree live before after -> temp_agree live (double_reduction_nest_exit iterators count before)
    (double_reduction_nest_exit iterators count after).
Proof. apply double_initialized_words_agree. Qed.

Print Assumptions double_reduction_exit_code_execution.
Print Assumptions double_reduction_exit_agree.
