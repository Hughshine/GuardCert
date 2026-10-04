From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightTempFrame.
From GuardMemory Require Import GuardMemoryBooleanScan.
Import ListNotations.
Set Implicit Arguments.

Section SEQUENCE.
Context {A:Type}.
Variable code : A->statement.
Variable result : A->bool.
Fixpoint affine_scan_sequence items := match items with
  | []=>Sskip | item::rest=>Ssequence(code item)(affine_scan_sequence rest) end.
Fixpoint affine_scan_sequence_result items := match items with
  | []=>true | item::rest=>result item&&affine_scan_sequence_result rest end.
Lemma affine_scan_sequence_forall items : affine_scan_sequence_result items=forallb result items.
Proof. induction items; cbn; [reflexivity|rewrite IHitems; reflexivity]. Qed.

Theorem affine_scan_sequence_execution fe ge locals memory live original flag items :
  (forall item, In item items -> forall temps accepted,
    temp_agree live original temps -> temps!flag=Some(memory_boolean_word accepted) ->
    exists after, exec_stmt fe ge locals temps memory(code item) E0 after memory Out_normal /\
      temp_agree live temps after /\ after!flag=Some(memory_boolean_word(accepted&&result item))) ->
  forall temps accepted,
    temp_agree live original temps -> temps!flag=Some(memory_boolean_word accepted) ->
    exists after,
      exec_stmt fe ge locals temps memory(affine_scan_sequence items) E0 after memory Out_normal /\
      temp_agree live temps after /\
      after!flag=Some(memory_boolean_word(accepted&&affine_scan_sequence_result items)).
Proof.
  induction items as [|item rest IH]; intros BODY temps accepted FRAME FLAG.
  - exists temps; cbn; rewrite andb_true_r; repeat split; auto using exec_Sskip,temp_agree_refl.
  - destruct(BODY item ltac:(cbn; auto) temps accepted FRAME FLAG) as [middle [RUN [MIDDLE GOOD]]].
    destruct(IH ltac:(intros; apply BODY; cbn; auto) middle(accepted&&result item))
      as [after [REST [AFTER RESULT]]].
    + eapply temp_agree_trans; eassumption.
    + exact GOOD.
    + exists after; cbn; split; [eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); eassumption|].
      split; [eapply temp_agree_trans; eassumption|rewrite andb_assoc; exact RESULT].
Qed.
End SEQUENCE.
Print Assumptions affine_scan_sequence_execution.
