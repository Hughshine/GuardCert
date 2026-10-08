From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightStraightLine.
From GuardMemory Require Import GuardMemoryBooleanScan.
Import ListNotations.
Set Implicit Arguments.

(** A static sequence accumulates tests in one private flag. Every executed
    test must be licensed, including tests reached after an earlier refusal. *)
Fixpoint memory_boolean_tests_statement flag codes := match codes with
  | [] => Sskip
  | code::rest => Ssequence (memory_boolean_test_body flag code) (memory_boolean_tests_statement flag rest)
  end.
Theorem memory_boolean_tests_execution fe ge locals memory flag live original
    {A : Type} (code : A -> expr) (test : A -> bool) tests :
  ~ In flag live ->
  (forall item temps, In item tests -> temp_agree live original temps ->
    expression_test (code item) (Entry ge locals temps memory) (test item)) ->
  forall current accepted,
    temp_agree live original current -> current!flag = Some (memory_boolean_word accepted) ->
    exists after,
      exec_stmt fe ge locals current memory
        (memory_boolean_tests_statement flag (map code tests)) E0 after memory Out_normal /\
      temp_agree live current after /\
      after!flag = Some (memory_boolean_word (accepted && forallb test tests)).
Proof.
  intro FRESH; induction tests as [|item tests IH]; intros TEST current accepted FRAME FLAG.
  - exists current; split; [constructor|split; [apply temp_agree_refl|rewrite andb_true_r; exact FLAG]].
  - destruct (@memory_boolean_test_body_execution fe ge locals current memory flag (code item)
      accepted (test item) live FRESH FLAG (TEST item current ltac:(cbn; auto) FRAME))
      as [middle [HEAD [MID_FRAME MID_FLAG]]].
    destruct (IH ltac:(intros next temps MEMBER PUBLIC; apply TEST; [cbn; auto|exact PUBLIC])
      middle (accepted && test item)) as [after [TAIL [AFTER_FRAME RESULT]]].
    + eapply temp_agree_trans; eassumption.
    + exact MID_FLAG.
    + exists after; split.
      * cbn [map memory_boolean_tests_statement]; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);
          [exact HEAD|exact TAIL].
      * split; [eapply temp_agree_trans; eassumption|cbn [forallb]; rewrite andb_assoc; exact RESULT].
Qed.
Print Assumptions memory_boolean_tests_execution.
