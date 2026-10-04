From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightNoWrap ClightTempFrame.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestFirstDomain AffineNestFirstLeaf
  AffineNestBoundWords AffineNestProbeRenaming AffineNestProbe.
Import ListNotations.
Set Implicit Arguments.

Definition affine_probe_coverage registers nest :=
  forall identifier, In identifier(affine_nest_controls nest++affine_tail_bound_reads nest) -> In identifier registers.
Lemma affine_probe_child_coverage registers iterator bound expression body child :
  affine_probe_coverage registers(AffineSourceAxis iterator bound expression body child) ->
  affine_probe_coverage registers child.
Proof.
  intros COVERAGE identifier MEMBER; apply COVERAGE.
  apply in_app_or in MEMBER; destruct MEMBER as [MEMBER|MEMBER].
  - apply in_or_app; left; cbn [affine_nest_controls List.In]; auto.
  - apply in_or_app; right; destruct child; [contradiction|].
    cbn [affine_tail_bound_reads]; apply in_or_app; auto.
Qed.

(** The check executes only the first source control path on renamed private
    controls. Normal source execution supplies each conditionally reached
    expression's definition; no later row or data operation is executed. *)
Theorem affine_first_probe_execution nest : forall fe ge locals registers rename result source target memory,
  affine_probe_coverage registers nest -> affine_rename_injective registers rename ->
  affine_first_header_domain nest source -> affine_renamed_view registers rename source target ->
  exists after,
    exec_stmt fe ge locals target memory (affine_first_probe nest rename result) E0 after memory Out_normal /\
    after!result=Some(Vint(if affine_first_path_flag nest source then Int.one else Int.zero)).
Proof.
  induction nest as [leaf|iterator bound expression body child IH];
    intros fe ge locals registers rename result source target memory COVERAGE UNIQUE DOMAIN VIEW.
  - exists(PTree.set result (Vint Int.one) target); split; [constructor; constructor|apply PTree.gss].
  - assert (ITERATOR:In iterator registers).
    { apply COVERAGE,in_or_app; left; cbn [affine_nest_controls List.In]; auto. }
    assert (BOUND:In bound registers).
    { apply COVERAGE,in_or_app; left; cbn [affine_nest_controls List.In]; auto. }
    destruct DOMAIN as [ITERATOR_WORD [BOUND_WORD DOMAIN]].
    pose proof(@affine_probe_header_test iterator bound registers rename ge locals source target memory
      ITERATOR BOUND ITERATOR_WORD BOUND_WORD VIEW) as TEST.
    destruct TEST as [test_value [EVAL BOOL]].
    destruct(Int.lt(temp_word iterator source)(temp_word bound source)) eqn:ACTIVE.
    + assert (SOURCE_ACTIVE:(Int.signed(temp_word iterator source)<Int.signed(temp_word bound source))%Z).
      { rewrite affine_integer_lt in ACTIVE; apply Z.ltb_lt; exact ACTIVE. }
      specialize(DOMAIN SOURCE_ACTIVE).
      pose proof(@affine_probe_child_coverage registers iterator bound expression body child COVERAGE) as CHILD_COVERAGE.
      destruct child as [code|child_iterator child_bound child_expression child_body grandchild].
      * destruct(IH fe ge locals registers rename result source target memory CHILD_COVERAGE UNIQUE I VIEW)
          as [after [RUN RESULT]].
        exists after; split.
        -- eapply exec_Sifthenelse with (v1:=test_value)(b:=true); [exact EVAL|exact BOOL|exact RUN].
        -- cbn [affine_first_path_flag]; rewrite ACTIVE; exact RESULT.
      * destruct DOMAIN as [WORDS CHILD_DOMAIN].
        assert (READS:forall identifier, In identifier(memory_source_affine_reads child_expression) -> In identifier registers).
        { intros identifier MEMBER; apply COVERAGE,in_or_app; right; cbn [affine_tail_bound_reads]; apply in_or_app; auto. }
        assert (CHILD_ITERATOR:In child_iterator registers).
        { apply CHILD_COVERAGE,in_or_app; left; cbn [affine_nest_controls List.In]; auto. }
        assert (CHILD_BOUND:In child_bound registers).
        { apply CHILD_COVERAGE,in_or_app; left; cbn [affine_nest_controls List.In]; auto. }
        pose proof(@affine_renamed_bound_evaluation child_expression registers rename ge locals source target memory
          READS WORDS VIEW) as BOUND_EVAL.
        set (word:=Int.repr(memory_source_affine_math(affine_word_valuation source) child_expression)).
        set (next:=PTree.set (rename child_iterator) (Vint Int.zero)
          (PTree.set (rename child_bound) (Vint word) target)).
        assert (NEXT_VIEW:affine_renamed_view registers rename
          (affine_first_child_temps(AffineSourceAxis child_iterator child_bound child_expression child_body grandchild) source) next).
        { unfold next; cbn [affine_first_child_temps]; apply affine_renamed_view_set; [exact UNIQUE|exact CHILD_ITERATOR|].
          apply affine_renamed_view_set; [exact UNIQUE|exact CHILD_BOUND|exact VIEW]. }
        destruct(IH fe ge locals registers rename result
          (affine_first_child_temps(AffineSourceAxis child_iterator child_bound child_expression child_body grandchild) source)
          next memory CHILD_COVERAGE UNIQUE CHILD_DOMAIN NEXT_VIEW) as [after [RUN RESULT]].
        exists after; split.
        -- eapply exec_Sifthenelse with (v1:=test_value)(b:=true); [exact EVAL|exact BOOL|].
           eapply exec_Sseq_1 with (t1:=E0)(t2:=E0).
           ++ constructor; exact BOUND_EVAL.
           ++ eapply exec_Sseq_1 with (t1:=E0)(t2:=E0); [constructor; constructor|exact RUN].
        -- cbn [affine_first_path_flag]; rewrite ACTIVE; exact RESULT.
    + exists(PTree.set result (Vint Int.zero) target); split.
      * eapply exec_Sifthenelse with (v1:=test_value)(b:=false); [exact EVAL|exact BOOL|constructor; constructor].
      * cbn [affine_first_path_flag]; rewrite ACTIVE; apply PTree.gss.
Qed.
Print Assumptions affine_probe_child_coverage.
Print Assumptions affine_first_probe_execution.
