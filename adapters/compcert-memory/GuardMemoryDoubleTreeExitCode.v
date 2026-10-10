From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleSourceTreeData
  GuardMemoryDoubleSourceTreeExit GuardMemoryDoubleRectangularNestData GuardMemoryDoubleTreeCaptureData
  GuardMemoryDoubleTreeCacheParameters GuardMemoryDoubleTreeCacheEnvironment GuardMemoryLongControl GuardMemoryLongSourceAffine.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint double_tree_exit_code tree cache := match tree with
  | DoubleTreeSkip | DoubleTreePoint _ _=>Sskip
  | DoubleTreeSequence first second=>Ssequence (double_tree_exit_code first cache) (double_tree_exit_code second cache)
  | DoubleTreeRange _ iterator start bound child=>Sifthenelse (double_tree_cached_active start bound cache)
      (Ssequence (double_tree_exit_code child cache) (Sset iterator (double_tree_cached_bound bound cache)))
      (Sset iterator (double_tree_initial start)) end.
Lemma double_tree_exit_cached_values tree valuation cache temps :
  (forall header, In header (double_source_tree_headers tree) -> ~ In (cache header) (double_source_tree_writes tree)) ->
  forall header, In header (double_source_tree_headers tree) ->
    double_tree_cached_value cache (double_source_tree_exit valuation tree temps) header=double_tree_cached_value cache temps header.
Proof.
  intros FRESH header MEMBER; unfold double_tree_cached_value; rewrite double_source_tree_exit_frame by (apply FRESH; exact MEMBER); reflexivity.
Qed.
Lemma double_tree_cached_bound_from_slot ge locals temps memory bound cache :
  (exists word, temps ! (cache (tree_bound_header bound))=Some (Vint word)) ->
  eval_expr ge locals temps memory (double_tree_cached_bound bound cache)
    (Vlong (Int64.repr (double_tree_bound_value (double_tree_cached_value cache temps) bound))).
Proof.
  intros [word WORD].
  assert (CAST : eval_expr ge locals temps memory
    (Ecast (Etempvar (cache (tree_bound_header bound)) (Tint I32 Signed noattr)) memory_long_type)
    (Vlong (Int64.repr (Int.signed word)))).
  { eapply eval_Ecast; [constructor; exact WORD|reflexivity]. }
  unfold double_tree_bound_value,double_tree_cached_value; rewrite WORD.
  destruct bound as [header [offset|]]; cbn [double_tree_cached_bound tree_bound_offset] in *.
  - eapply eval_Ebinop; [exact CAST|constructor|].
    change (Some (Vlong (Int64.sub (Int64.repr (Int.signed word)) (Int64.repr (Int.signed offset))))=
      Some (Vlong (Int64.repr (Int.signed word-Int.signed offset)))).
    rewrite long_source_repr_sub; reflexivity.
  - replace (Int.signed word-0) with (Int.signed word) by lia; exact CAST.
Qed.
Lemma double_tree_cached_exit_test ge locals temps memory start bound cache :
  (exists word, temps ! (cache (tree_bound_header bound))=Some (Vint word)) ->
  Int64.min_signed<=double_tree_bound_value (double_tree_cached_value cache temps) bound<=Int64.max_signed ->
  expression_test (double_tree_cached_active start bound cache) (Entry ge locals temps memory)
    (Int.signed start <? double_tree_bound_value (double_tree_cached_value cache temps) bound).
Proof.
  intros WORD RANGE; exists (Val.of_bool (Int.signed start <? double_tree_bound_value (double_tree_cached_value cache temps) bound)); split.
  - unfold double_tree_cached_active; apply memory_long_test_execution; [reflexivity|destruct bound as [header [offset|]]; reflexivity|
      |exact RANGE| |apply double_tree_cached_bound_from_slot; exact WORD].
    + change (-9223372036854775808<=Int.signed start<=9223372036854775807).
      pose proof (Int.signed_range start); change (-2147483648<=Int.signed start<=2147483647) in H; lia.
    + unfold double_tree_initial; eapply eval_Ecast; [constructor|reflexivity].
  - destruct (Int.signed start <? double_tree_bound_value (double_tree_cached_value cache temps) bound); reflexivity.
Qed.
Lemma double_tree_exit_assignments_agree tree : forall first second,
  (forall header, In header (double_source_tree_headers tree) -> second header=first header) ->
  double_source_tree_exit_assignments second tree=double_source_tree_exit_assignments first tree.
Proof.
  induction tree; intros first second VALUES; cbn [double_source_tree_exit_assignments]; try reflexivity.
  - f_equal; [apply IHtree2|apply IHtree1]; intros header MEMBER; apply VALUES; cbn;
      apply in_or_app; [right|left]; exact MEMBER.
  - assert (BOUND : double_tree_bound_value second bound=double_tree_bound_value first bound).
    { unfold double_tree_bound_value; rewrite VALUES by (cbn; left; reflexivity); reflexivity. }
    rewrite BOUND; f_equal; destruct (Int.signed start <? double_tree_bound_value first bound); [|reflexivity].
    apply IHtree; intros header MEMBER; apply VALUES; cbn; right; exact MEMBER.
Qed.
Lemma double_tree_exit_valuation_agree tree first second temps :
  (forall header, In header (double_source_tree_headers tree) -> second header=first header) ->
  double_source_tree_exit second tree temps=double_source_tree_exit first tree temps.
Proof. intro VALUES; unfold double_source_tree_exit; rewrite (@double_tree_exit_assignments_agree tree first second VALUES); reflexivity. Qed.
Lemma double_tree_exit_public_frame tree valuation live before after :
  temp_agree live before after -> temp_agree live
    (double_source_tree_exit valuation tree before) (double_source_tree_exit valuation tree after).
Proof.
  intros FRAME key MEMBER; unfold double_source_tree_exit; rewrite !double_rectangular_set_assignments_lookup.
  destruct (double_rectangular_assignment_value (double_source_tree_exit_assignments valuation tree) key);
    [reflexivity|apply FRAME; exact MEMBER].
Qed.

Theorem double_tree_exit_code_execution tree : forall cache fe ge locals temps memory,
  (forall header, In header (double_source_tree_headers tree) -> ~ In (cache header) (double_source_tree_writes tree)) ->
  (forall header, In header (double_source_tree_headers tree) -> exists word, temps ! (cache header)=Some (Vint word)) ->
  exec_stmt fe ge locals temps memory (double_tree_exit_code tree cache) E0
    (double_source_tree_exit (double_tree_cached_value cache temps) tree temps) memory Out_normal.
Proof.
  induction tree; intros cache fe ge locals temps memory FRESH WORDS; cbn [double_tree_exit_code]; try solve [constructor].
  - rewrite double_source_tree_exit_sequence.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [apply IHtree1|].
    + intros header MEMBER BAD; apply (FRESH header ltac:(cbn; apply in_or_app; left; exact MEMBER)); cbn; apply in_or_app; left; exact BAD.
    + intros header MEMBER; apply WORDS; cbn; apply in_or_app; left; exact MEMBER.
    + assert (VALUES : forall header, In header (double_source_tree_headers tree2) ->
        double_tree_cached_value cache (double_source_tree_exit (double_tree_cached_value cache temps) tree1 temps) header=
        double_tree_cached_value cache temps header).
      { intros header MEMBER; unfold double_tree_cached_value; rewrite double_source_tree_exit_frame; [reflexivity|].
        intro BAD; apply (FRESH header ltac:(cbn; apply in_or_app; right; exact MEMBER)); cbn; apply in_or_app; left; exact BAD. }
      assert (EXIT : double_source_tree_exit
        (double_tree_cached_value cache (double_source_tree_exit (double_tree_cached_value cache temps) tree1 temps)) tree2
        (double_source_tree_exit (double_tree_cached_value cache temps) tree1 temps)=
        double_source_tree_exit (double_tree_cached_value cache temps) tree2
        (double_source_tree_exit (double_tree_cached_value cache temps) tree1 temps)).
      { apply double_tree_exit_valuation_agree; exact VALUES. }
      rewrite <- EXIT; apply IHtree2.
      * intros header MEMBER BAD; apply (FRESH header ltac:(cbn; apply in_or_app; right; exact MEMBER)); cbn; apply in_or_app; right; exact BAD.
      * intros header MEMBER; destruct (WORDS header ltac:(cbn; apply in_or_app; right; exact MEMBER)) as [word WORD]; exists word.
        rewrite double_source_tree_exit_frame; [exact WORD|].
        intro BAD; apply (FRESH header ltac:(cbn; apply in_or_app; right; exact MEMBER)); cbn; apply in_or_app; left; exact BAD.
  - assert (BOUND_RANGE : Int64.min_signed<=double_tree_bound_value (double_tree_cached_value cache temps) bound<=Int64.max_signed).
    { destruct (WORDS _ (or_introl eq_refl)) as [word WORD]; unfold double_tree_bound_value,double_tree_cached_value; rewrite WORD.
      pose proof (Int.signed_range word); destruct (tree_bound_offset bound) as [offset|]; [pose proof (Int.signed_range offset)|];
        change Int.min_signed with (-2147483648) in *; change Int.max_signed with 2147483647 in *;
        change Int64.min_signed with (-9223372036854775808); change Int64.max_signed with 9223372036854775807; lia. }
    destruct (@double_tree_cached_exit_test ge locals temps memory start bound cache (WORDS _ (or_introl eq_refl)) BOUND_RANGE)
      as [test [TEST BOOLEAN]].
    destruct (Int.signed start <? double_tree_bound_value (double_tree_cached_value cache temps) bound) eqn:ACTIVE.
    + eapply exec_Sifthenelse with (b:=true); [exact TEST|exact BOOLEAN|].
      unfold double_source_tree_exit; cbn [double_source_tree_exit_assignments]; rewrite ACTIVE.
      rewrite Z.max_r by (apply Z.ltb_lt in ACTIVE; lia); cbn [double_rectangular_set_assignments].
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [apply IHtree|].
      * intros header MEMBER BAD; apply (FRESH header ltac:(cbn; right; exact MEMBER)); cbn; right; exact BAD.
      * intros header MEMBER; apply WORDS; cbn; right; exact MEMBER.
      * assert (SLOT : exists word,
          (double_source_tree_exit (double_tree_cached_value cache temps) tree temps) !
            (cache (tree_bound_header bound))=Some (Vint word)).
        { destruct (WORDS _ (or_introl eq_refl)) as [word WORD]; exists word.
          rewrite double_source_tree_exit_frame; [exact WORD|].
          intro BAD; apply (FRESH _ (or_introl eq_refl)); cbn; right; exact BAD. }
        assert (SAME : double_tree_cached_value cache
          (double_source_tree_exit (double_tree_cached_value cache temps) tree temps)
          (tree_bound_header bound)=double_tree_cached_value cache temps (tree_bound_header bound)).
        { unfold double_tree_cached_value; rewrite double_source_tree_exit_frame; [reflexivity|].
          intro BAD; apply (FRESH _ (or_introl eq_refl)); cbn; right; exact BAD. }
        pose proof (@double_tree_cached_bound_from_slot ge locals
          (double_source_tree_exit (double_tree_cached_value cache temps) tree temps)
          memory bound cache SLOT) as EVAL.
        unfold double_tree_bound_value in EVAL; rewrite SAME in EVAL.
        apply exec_Sset; exact EVAL.
    + eapply exec_Sifthenelse with (b:=false); [exact TEST|exact BOOLEAN|].
      unfold double_source_tree_exit; cbn [double_source_tree_exit_assignments]; rewrite ACTIVE.
      rewrite Z.max_l by (apply Z.ltb_ge in ACTIVE; lia); cbn [double_rectangular_set_assignments].
      constructor; unfold double_tree_initial; eapply eval_Ecast; [constructor|reflexivity].
Qed.

Print Assumptions double_tree_exit_cached_values.
Print Assumptions double_tree_cached_bound_from_slot.
Print Assumptions double_tree_cached_exit_test.
Print Assumptions double_tree_exit_assignments_agree.
Print Assumptions double_tree_exit_valuation_agree.
Print Assumptions double_tree_exit_public_frame.
Print Assumptions double_tree_exit_code_execution.
