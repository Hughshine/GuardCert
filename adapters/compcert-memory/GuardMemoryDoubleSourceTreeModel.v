From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Integers.
From compcert.common Require Import Memory.
From polcert.lib Require Import Misc.
From Guard Require Import ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDoubleSourceInstruction
  GuardMemoryDoubleSourceTreeData GuardMemoryDoubleSourceTreeModelData
  GuardMemoryDoubleSourceLoopModel GuardMemoryDoubleInitializedNestModel
  GuardMemoryDoubleMatmulLoopModel GuardMemoryDoubleRangeModel GuardMemoryLongRangeSource GuardMemoryLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma double_source_tree_range_iterations headers raw iterator start bound child prefix valuation before after :
  In (tree_bound_header bound) headers ->
  (SL.loop_semantics (double_source_tree_model headers (length prefix) (DoubleTreeRange raw iterator start bound child))
    (rev prefix++map valuation headers) before after <->
   counted_iterations (fun value => SL.loop_semantics (double_source_tree_model headers (S (length prefix)) child)
     (value::rev prefix++map valuation headers))
     (memory_long_range_count (Int.signed start) (double_tree_bound_value valuation bound))
     (Int.signed start) before after).
Proof.
  intro MEMBER; cbn [double_source_tree_model]; split.
  - intro RUN; inversion RUN as [| | | | | env lower upper body first final ITER]; subst.
    cbn [SL.eval_expr] in ITER.
    rewrite double_tree_bound_model_value in ITER by exact MEMBER.
    rewrite double_signed_range_domain in ITER.
    apply (proj1 (@double_matmul_range_iterations
      (memory_long_range_count (Int.signed start) (double_tree_bound_value valuation bound)) _
      (Int.signed start) (Z.max (Int.signed start) (double_tree_bound_value valuation bound)) before after
      ltac:(symmetry; apply memory_long_range_end))); exact ITER.
  - intro ITER; apply SL.LLoop; cbn [SL.eval_expr].
    rewrite double_tree_bound_model_value by exact MEMBER; rewrite double_signed_range_domain.
    apply (proj2 (@double_matmul_range_iterations
      (memory_long_range_count (Int.signed start) (double_tree_bound_value valuation bound)) _
      (Int.signed start) (Z.max (Int.signed start) (double_tree_bound_value valuation bound)) before after
      ltac:(symmetry; apply memory_long_range_end))); exact ITER.
Qed.

Theorem double_source_tree_model_frame headers tree : incl (double_source_tree_headers tree) headers ->
  forall prefix valuation before after,
  SL.loop_semantics (double_source_tree_model headers (length prefix) tree)
    (rev prefix++map valuation headers) before after -> runtime_locations after=runtime_locations before.
Proof.
  induction tree; intros MEMBERS prefix valuation before after RUN.
  - cbn [double_source_tree_model] in RUN; inversion RUN; reflexivity.
  - cbn [double_source_tree_model] in RUN; eapply double_source_instruction_Loop_frame; exact RUN.
  - cbn [double_source_tree_model] in RUN; apply double_source_model_sequence in RUN as [middle [FIRST SECOND]].
    assert (LEFT : incl (double_source_tree_headers tree1) headers).
    { intros key MEMBER; apply MEMBERS,in_or_app; left; exact MEMBER. }
    assert (RIGHT : incl (double_source_tree_headers tree2) headers).
    { intros key MEMBER; apply MEMBERS,in_or_app; right; exact MEMBER. }
    rewrite (IHtree2 RIGHT prefix valuation middle after SECOND); exact (IHtree1 LEFT prefix valuation before middle FIRST).
  - assert (BOUND : In (tree_bound_header bound) headers) by (apply MEMBERS; left; reflexivity).
    assert (CHILD : incl (double_source_tree_headers tree) headers) by (intros key MEMBER; apply MEMBERS; right; exact MEMBER).
    apply double_source_tree_range_iterations in RUN; [|exact BOUND].
    eapply counted_locations; [|exact RUN]; intros value first final STEP.
    replace (S (length prefix)) with (length (prefix++[value])) in STEP by (rewrite app_length; cbn [length]; lia).
    rewrite <- double_source_extended_environment in STEP; eapply IHtree; eassumption.
Qed.

Theorem double_source_tree_shared_memory headers tree : incl (double_source_tree_headers tree) headers ->
  forall prefix valuation locations before after,
  (SL.loop_semantics (double_source_tree_model headers (length prefix) tree)
    (rev prefix++map valuation headers) (RuntimeState locations before) (RuntimeState locations after) <->
   double_source_tree_memory tree valuation prefix locations before after).
Proof.
  induction tree; intros MEMBERS prefix valuation locations before after.
  - cbn [double_source_tree_model double_source_tree_memory]; split.
    + intro RUN; inversion RUN; reflexivity.
    + intro SAME; subst; constructor.
  - cbn [double_source_tree_model double_source_tree_memory]; apply double_source_instruction_Loop.
  - assert (LEFT : incl (double_source_tree_headers tree1) headers).
    { intros key MEMBER; apply MEMBERS,in_or_app; left; exact MEMBER. }
    assert (RIGHT : incl (double_source_tree_headers tree2) headers).
    { intros key MEMBER; apply MEMBERS,in_or_app; right; exact MEMBER. }
    cbn [double_source_tree_model double_source_tree_memory]; rewrite double_source_model_sequence; split.
    + intros [middle [FIRST SECOND]]; destruct middle as [registry memory].
      pose proof (@double_source_tree_model_frame headers tree1 LEFT prefix valuation
        (RuntimeState locations before) (RuntimeState registry memory) FIRST) as SAME.
      cbn [runtime_locations] in SAME; subst registry.
      exists memory; split; [apply (proj1 (IHtree1 LEFT _ _ _ _ _))|apply (proj1 (IHtree2 RIGHT _ _ _ _ _))]; assumption.
    + intros [middle [FIRST SECOND]]; exists (RuntimeState locations middle); split;
        [apply (proj2 (IHtree1 LEFT _ _ _ _ _))|apply (proj2 (IHtree2 RIGHT _ _ _ _ _))]; assumption.
  - assert (BOUND : In (tree_bound_header bound) headers) by (apply MEMBERS; left; reflexivity).
    assert (CHILD : incl (double_source_tree_headers tree) headers) by (intros key MEMBER; apply MEMBERS; right; exact MEMBER).
    rewrite double_source_tree_range_iterations by exact BOUND; cbn [double_source_tree_memory]; symmetry.
    apply counted_memory_lift with (floor:=Int.signed start) (upper:=Z.max (Int.signed start) (double_tree_bound_value valuation bound)).
    + intros value first final RANGE.
      rewrite <- (IHtree CHILD (prefix++[value]) valuation locations first final).
      rewrite app_length; cbn [length]; rewrite Nat.add_1_r,double_source_extended_environment; reflexivity.
    + intros value first final RUN.
      replace (S (length prefix)) with (length (prefix++[value])) in RUN by (rewrite app_length; cbn [length]; lia).
      rewrite <- double_source_extended_environment in RUN.
      eapply double_source_tree_model_frame; eassumption.
    + lia.
    + symmetry; apply memory_long_range_end.
Qed.
Corollary double_source_tree_model_memory tree prefix valuation locations before after :
  SL.loop_semantics (double_source_tree_model (double_source_tree_parameters tree) (length prefix) tree)
    (rev prefix++map valuation (double_source_tree_parameters tree))
    (RuntimeState locations before) (RuntimeState locations after) <->
  double_source_tree_memory tree valuation prefix locations before after.
Proof.
  apply double_source_tree_shared_memory; intros header MEMBER.
  apply double_source_tree_parameter_membership; exact MEMBER.
Qed.

Print Assumptions double_source_tree_range_iterations.
Print Assumptions double_source_tree_model_frame.
Print Assumptions double_source_tree_shared_memory.
Print Assumptions double_source_tree_model_memory.
