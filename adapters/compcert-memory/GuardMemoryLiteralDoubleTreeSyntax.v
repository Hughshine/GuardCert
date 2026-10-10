From Stdlib Require Import List Bool.
From compcert.common Require Import Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightLoopSyntax ClightRegionProgress ClightTempFrame.
From GuardMemory Require Import GuardMemoryLiteralDoubleTreeData GuardMemoryDoubleSourceTreeData GuardMemoryDoubleSourceInstruction
  GuardMemoryDoubleAssignmentFactory GuardMemoryLongRangeSource GuardMemoryLongLoopControl
  GuardMemoryLongRawLoadedProgress GuardMemoryLongProgressControl.
Import ListNotations.
Definition literal_double_source_tree_writes tree :=
  double_source_tree_writes (literal_double_tree_skeleton tree).

Set Implicit Arguments.

Lemma literal_double_source_tree_quiet p controls tree : literal_double_source_tree_checked p controls tree ->
  quiet_statement (literal_double_source_tree_code tree)=true.
Proof.
  revert controls; induction tree; intros controls CHECK; cbn [literal_double_source_tree_code]; [reflexivity| | |].
  - destruct (@checked_double_source_instruction_sound p controls body instruction CHECK) as [ASSIGN _].
    destruct (@decoded_double_assignment_shape body (double_source_assignment instruction) ASSIGN) as [value [SHAPE TYPE]]; rewrite SHAPE; reflexivity.
  - destruct CHECK as [FIRST SECOND]; cbn [quiet_statement]; rewrite (IHtree1 controls FIRST),(IHtree2 controls SECOND); reflexivity.
  - destruct CHECK as [FRESH [DECODE [RANGE CHILD]]]; destruct raw;
      unfold long_raw_from_loop,long_raw_loaded_loop,memory_long_from_loop,memory_long_frontend_loop,
        memory_long_increment,long_counter_increment;
      cbn [quiet_statement]; rewrite (IHtree (controls++[iterator]) CHILD); reflexivity.
Qed.
Lemma literal_double_source_tree_normal p controls tree : literal_double_source_tree_checked p controls tree ->
  normal_statement (literal_double_source_tree_code tree)=true.
Proof.
  revert controls; induction tree; intros controls CHECK; cbn [literal_double_source_tree_code]; [reflexivity| | |].
  - destruct (@checked_double_source_instruction_sound p controls body instruction CHECK) as [ASSIGN _].
    destruct (@decoded_double_assignment_shape body (double_source_assignment instruction) ASSIGN) as [value [SHAPE TYPE]]; rewrite SHAPE; reflexivity.
  - destruct CHECK as [FIRST SECOND]; cbn [normal_statement]; rewrite (IHtree1 controls FIRST),(IHtree2 controls SECOND); reflexivity.
  - destruct CHECK as [FRESH [DECODE [RANGE CHILD]]]; destruct raw;
      unfold long_raw_from_loop,long_raw_loaded_loop,memory_long_from_loop,memory_long_frontend_loop,
        memory_long_increment,long_counter_increment;
      cbn [normal_statement quiet_statement]; rewrite (@literal_double_source_tree_quiet p (controls++[iterator]) tree CHILD); reflexivity.
Qed.
Lemma literal_double_source_tree_writes_only p controls tree : literal_double_source_tree_checked p controls tree ->
  writes_only (literal_double_source_tree_writes tree) (literal_double_source_tree_code tree).
Proof.
  revert controls; induction tree; intros controls CHECK; cbn [literal_double_source_tree_code literal_double_source_tree_writes literal_double_tree_skeleton double_source_tree_writes].
  - constructor.
  - destruct (@checked_double_source_instruction_sound p controls body instruction CHECK) as [ASSIGN _].
    destruct (@decoded_double_assignment_shape body (double_source_assignment instruction) ASSIGN) as [value [SHAPE TYPE]]; rewrite SHAPE; constructor.
  - destruct CHECK as [FIRST SECOND]; apply writes_sequence.
    + eapply writes_only_weaken; [intros key MEMBER; apply in_or_app; left; exact MEMBER|exact (IHtree1 controls FIRST)].
    + eapply writes_only_weaken; [intros key MEMBER; apply in_or_app; right; exact MEMBER|exact (IHtree2 controls SECOND)].
  - destruct CHECK as [FRESH [DECODE [RANGE CHILD]]].
    assert (BODY : writes_only (iterator::literal_double_source_tree_writes tree) (literal_double_source_tree_code tree)).
    { eapply writes_only_weaken; [intros key MEMBER; right; exact MEMBER|exact (IHtree (controls++[iterator]) CHILD)]. }
    destruct raw; unfold long_raw_from_loop,long_raw_loaded_loop,memory_long_from_loop,memory_long_frontend_loop,
      memory_long_increment,long_counter_increment;
      repeat first [apply writes_sequence|apply writes_loop|apply writes_if|exact BODY|constructor; cbn; auto].
Qed.
Corollary literal_double_source_tree_completed_normal p controls tree fe ge locals temps memory trace after final outcome :
  literal_double_source_tree_checked p controls tree ->
  exec_stmt fe ge locals temps memory (literal_double_source_tree_code tree) trace after final outcome -> outcome=Out_normal.
Proof. intro CHECK; apply normal_statement_execution; eapply literal_double_source_tree_normal; exact CHECK. Qed.

Print Assumptions literal_double_source_tree_quiet.
Print Assumptions literal_double_source_tree_normal.
Print Assumptions literal_double_source_tree_writes_only.
Print Assumptions literal_double_source_tree_completed_normal.
