From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightTempFrame ClightCondition.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryNaryCompute GuardMemoryNaryAffineAccess
  GuardMemoryPointerCellComparison GuardMemoryBooleanScan GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestScanAddress AffineNestScanAccesses AffineNestScanSyntax AffineNestScanWords.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightObservedWordProbe.
Import ListNotations.
Set Implicit Arguments.

Definition affine_observation_test pointer values operation :=
  memory_pointer_cells_test
    (affine_scan_address (memory_nary_access_array(memory_nary_compute_write operation)) values
      (memory_nary_access_expression(memory_nary_compute_write operation))) (signed_pointer_temp pointer).
Fixpoint affine_observation_leaf pointer values flag operations := match operations with
  | []=>Sskip
  | operation::rest=>Ssequence(memory_boolean_test_body flag(affine_observation_test pointer values operation))
      (affine_observation_leaf pointer values flag rest) end.
Definition affine_observation_result locations observation operations point :=
  forallb(fun operation=>observed_word_cell_check locations observation
    (affine_scan_access_cell point(memory_nary_compute_write operation))) operations.

(** Every test is licensed by the same current complete body. Accumulation
    changes only the private flag; it does not execute source stores. *)
Theorem affine_observation_leaf_execution operations fe ge locals memory pointer values flag
  layout point locations observation public base protected checked good :
  ~In flag protected -> ~In flag public -> ~In flag(map values layout) ->
  temp_agree public base checked -> affine_scan_word_view layout values point checked ->
  checked!flag=Some(memory_boolean_word good) ->
  (forall operation current, In operation operations -> temp_agree public base current ->
    affine_scan_word_view layout values point current ->
    expression_test(affine_observation_test pointer values operation)(Entry ge locals current memory)
      (observed_word_cell_check locations observation(affine_scan_access_cell point(memory_nary_compute_write operation)))) ->
  exists after,
    exec_stmt fe ge locals checked memory(affine_observation_leaf pointer values flag operations) E0 after memory Out_normal /\
    temp_agree protected checked after /\
    after!flag=Some(memory_boolean_word(good&&affine_observation_result locations observation operations point)).
Proof.
  revert checked good; induction operations as [|operation rest IH];
    intros checked good PRIVATE PUBLIC_PRIVATE WORD_PRIVATE FRAME WORDS FLAG TESTS.
  - exists checked; split; [constructor|split; [apply temp_agree_refl|]].
    cbn [affine_observation_result forallb]; rewrite andb_true_r; exact FLAG.
  - set(keep:=protected++public++map values layout).
    assert (KEEP_PRIVATE : ~In flag keep).
    { unfold keep; repeat rewrite in_app_iff; tauto. }
    destruct(@memory_boolean_test_body_execution fe ge locals checked memory flag
      (affine_observation_test pointer values operation) good
      (observed_word_cell_check locations observation(affine_scan_access_cell point(memory_nary_compute_write operation))) keep
      KEEP_PRIVATE FLAG (TESTS operation checked (or_introl eq_refl) FRAME WORDS))
      as [middle [FIRST [MIDDLE MID_FLAG]]].
    assert (MID_PUBLIC : temp_agree public base middle).
    { eapply temp_agree_trans; [exact FRAME|eapply temp_agree_weaken; [|exact MIDDLE]].
      unfold keep; intros identifier MEMBER; apply in_or_app; right; apply in_or_app; left; exact MEMBER. }
    assert (MID_WORDS : affine_scan_word_view layout values point middle).
    { eapply affine_scan_word_view_frame; [apply incl_refl| |exact WORDS].
      eapply temp_agree_weaken; [|exact MIDDLE].
      unfold keep; intros identifier MEMBER; apply in_or_app; right; apply in_or_app; right; exact MEMBER. }
    destruct (@IH middle
      (good&&observed_word_cell_check locations observation(affine_scan_access_cell point(memory_nary_compute_write operation)))
      PRIVATE PUBLIC_PRIVATE WORD_PRIVATE MID_PUBLIC MID_WORDS MID_FLAG
      (fun next current MEMBER=>TESTS next current (or_intror MEMBER))) as [after [REST [AFTER RESULT]]].
    exists after; split.
    + cbn [affine_observation_leaf]; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); eassumption.
    + split.
      * eapply temp_agree_trans; [eapply temp_agree_weaken; [|exact MIDDLE]|exact AFTER].
        unfold keep; intros identifier MEMBER; apply in_or_app; left; exact MEMBER.
      * cbn [affine_observation_result forallb] in RESULT |- *; rewrite andb_assoc; exact RESULT.
Qed.

Print Assumptions affine_observation_leaf_execution.
