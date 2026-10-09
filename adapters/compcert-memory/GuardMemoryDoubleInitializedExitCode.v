From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightCountedLoop.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleInitializedNestExit
  GuardMemoryDoubleMatmulExit.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Restore actual source I64 controls from a private captured I32 count.
    The zero outer path retains every unreached inner temporary. *)
Fixpoint double_initialized_restore_words identifiers cache :=
  match identifiers with
  | [] => Sskip
  | identifier::rest => Ssequence (double_initialized_restore_words rest cache)
      (Sset identifier (double_cached_long cache))
  end.
Lemma double_initialized_restore_words_execution identifiers : forall fe ge locals temps memory cache count,
  ~ In cache identifiers -> signed_range (Z.of_nat count) ->
  temps ! cache=Some (Vint (Int.repr (Z.of_nat count))) ->
  exec_stmt fe ge locals temps memory (double_initialized_restore_words identifiers cache) E0
    (double_source_set_words identifiers (Vlong (Int64.repr (Z.of_nat count))) temps) memory Out_normal.
Proof.
  induction identifiers as [|identifier rest IH]; intros fe ge locals temps memory cache count FRESH RANGE WORD.
  - constructor.
  - cbn [double_initialized_restore_words double_source_set_words].
    eapply exec_Sseq_1 with
      (le1:=double_source_set_words rest (Vlong (Int64.repr (Z.of_nat count))) temps)
      (m1:=memory) (t1:=E0) (t2:=E0).
    + apply IH; [intro MEMBER; apply FRESH; cbn; auto|exact RANGE|exact WORD].
    + apply exec_Sset, double_cached_long_execution; [exact RANGE|].
      rewrite double_source_set_words_frame; [exact WORD|intro MEMBER; apply FRESH; cbn; auto].
Qed.
Definition double_initialized_exit_code outers inner cache :=
  match outers with
  | [] => double_initialized_restore_words [inner] cache
  | iterator::rest => Ssequence
      (Sifthenelse (double_cache_positive cache)
        (double_initialized_restore_words (rest++[inner]) cache) Sskip)
      (Sset iterator (double_cached_long cache))
  end.
Theorem double_initialized_exit_code_execution fe ge locals temps memory outers inner cache count :
  ~ In cache (outers++[inner]) -> signed_range (Z.of_nat count) ->
  temps ! cache=Some (Vint (Int.repr (Z.of_nat count))) ->
  exec_stmt fe ge locals temps memory (double_initialized_exit_code outers inner cache) E0
    (double_initialized_nest_exit outers inner count temps) memory Out_normal.
Proof.
  intros FRESH RANGE WORD; destruct outers as [|iterator rest].
  - rewrite double_initialized_nest_exit_leaf.
    exact (@double_initialized_restore_words_execution [inner] fe ge locals temps memory cache count FRESH RANGE WORD).
  - unfold double_initialized_exit_code; rewrite double_initialized_nest_exit_cons.
    pose proof (@double_cache_positive_execution ge locals temps memory cache (Z.of_nat count) RANGE WORD) as TEST.
    destruct count as [|count].
    + change (0<?Z.of_nat O) with false in TEST.
      eapply exec_Sseq_1 with (le1:=temps) (m1:=memory) (t1:=E0) (t2:=E0).
      * eapply exec_Sifthenelse; [exact TEST|reflexivity|constructor].
      * apply exec_Sset, double_cached_long_execution; assumption.
    + rewrite (proj2 (Z.ltb_lt 0 (Z.of_nat (S count))) ltac:(lia)) in TEST.
      change (exec_stmt fe ge locals temps memory
        (Ssequence (Sifthenelse (double_cache_positive cache)
          (double_initialized_restore_words (rest++[inner]) cache) Sskip)
          (Sset iterator (double_cached_long cache))) E0
        (PTree.set iterator (Vlong (Int64.repr (Z.of_nat (S count))))
          (double_source_set_words (rest++[inner]) (Vlong (Int64.repr (Z.of_nat (S count)))) temps)) memory Out_normal).
      eapply exec_Sseq_1 with
        (le1:=double_source_set_words (rest++[inner]) (Vlong (Int64.repr (Z.of_nat (S count)))) temps)
        (m1:=memory) (t1:=E0) (t2:=E0).
      * eapply exec_Sifthenelse; [exact TEST|reflexivity|].
        apply double_initialized_restore_words_execution;
          [intro MEMBER; apply FRESH; cbn; auto|exact RANGE|exact WORD].
      * apply exec_Sset, double_cached_long_execution; [exact RANGE|].
        rewrite double_source_set_words_frame;
          [exact WORD|intro MEMBER; apply FRESH; cbn; auto].
Qed.
Lemma double_initialized_words_agree identifiers word live before after :
  temp_agree live before after -> temp_agree live
    (double_source_set_words identifiers word before) (double_source_set_words identifiers word after).
Proof.
  intro FRAME; induction identifiers as [|identifier rest IH]; [exact FRAME|].
  intros key MEMBER; cbn [double_source_set_words]; rewrite !PTree.gsspec.
  destruct (peq key identifier); [reflexivity|apply IH; exact MEMBER].
Qed.
Theorem double_initialized_exit_agree outers inner count live before after :
  temp_agree live before after -> temp_agree live
    (double_initialized_nest_exit outers inner count before)
    (double_initialized_nest_exit outers inner count after).
Proof. apply double_initialized_words_agree. Qed.

Print Assumptions double_initialized_restore_words_execution.
Print Assumptions double_initialized_exit_code_execution.
Print Assumptions double_initialized_exit_agree.
