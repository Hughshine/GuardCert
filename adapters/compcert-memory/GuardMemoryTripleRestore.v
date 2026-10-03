From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightTempFrame ClightNoWrap ClightRedundantSet ClightCondition.
From GuardMemory Require Import GuardMemoryTripleSyntax GuardMemoryTripleDomain.
Import ListNotations.
Set Implicit Arguments.

Definition memory_triple_context d := [triple_row_bound d;triple_column_bound d;triple_depth_bound d].
Definition memory_triple_restore d :=
  Ssequence (Sset (triple_depth d) (Etempvar (triple_depth_bound d) type_int32s))
    (Ssequence (Sset (triple_column d) (Etempvar (triple_column_bound d) type_int32s))
      (Sset (triple_row d) (Etempvar (triple_row_bound d) type_int32s))).
Lemma memory_triple_restore_execution fe ge locals d temps memory :
  triple_column_bound d <> triple_depth d -> triple_row_bound d <> triple_depth d -> triple_row_bound d <> triple_column d ->
  (forall identifier, In identifier (memory_triple_context d) -> register_domain identifier (Entry ge locals temps memory)) ->
  exec_stmt fe ge locals temps memory (memory_triple_restore d) E0 (memory_triple_exit d temps) memory Out_normal.
Proof.
  intros MD ND NC WORDS.
  destruct (WORDS (triple_depth_bound d) ltac:(unfold memory_triple_context; cbn; auto)) as [depth DEPTH].
  destruct (WORDS (triple_column_bound d) ltac:(unfold memory_triple_context; cbn; auto)) as [column COLUMN].
  destruct (WORDS (triple_row_bound d) ltac:(unfold memory_triple_context; cbn; auto)) as [row ROW].
  cbn [entry_temps] in DEPTH,COLUMN,ROW.
  unfold memory_triple_restore,memory_triple_exit,temp_word; rewrite DEPTH,COLUMN,ROW.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0)
    (le1 := PTree.set (triple_depth d) (Vint depth) temps) (m1 := memory).
  - constructor; constructor; exact DEPTH.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0)
      (le1 := PTree.set (triple_column d) (Vint column) (PTree.set (triple_depth d) (Vint depth) temps)) (m1 := memory).
    + constructor; constructor; rewrite PTree.gso by exact MD; exact COLUMN.
    + constructor; constructor; rewrite !PTree.gso by assumption; exact ROW.
Qed.
Lemma memory_triple_exit_frame d live first second :
  temp_agree (memory_triple_context d++live) first second ->
  temp_agree live (memory_triple_exit d first) (memory_triple_exit d second).
Proof.
  intro FRAME; unfold memory_triple_exit,temp_word.
  rewrite (FRAME (triple_row_bound d) ltac:(apply in_or_app; left; unfold memory_triple_context; cbn; auto)).
  rewrite (FRAME (triple_column_bound d) ltac:(apply in_or_app; left; unfold memory_triple_context; cbn; auto)).
  rewrite (FRAME (triple_depth_bound d) ltac:(apply in_or_app; left; unfold memory_triple_context; cbn; auto)).
  intros identifier MEMBER; rewrite !PTree.gsspec.
  destruct (peq identifier (triple_row d)),(peq identifier (triple_column d)),(peq identifier (triple_depth d)); auto.
  apply FRAME,in_or_app; right; exact MEMBER.
Qed.
Print Assumptions memory_triple_restore_execution.
