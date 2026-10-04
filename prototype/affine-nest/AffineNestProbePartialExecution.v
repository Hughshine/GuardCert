From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightNoWrap.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestFirstDomain AffineNestFirstLeaf
  AffineNestProbeRenaming AffineNestProbe AffineNestProbeStage.
Import ListNotations.
Set Implicit Arguments.

(** This version requires no entry relation on future controls. Undefined
    future bounds and coordinates are allowed and are never copied/read. *)
Theorem affine_first_probe_partial_execution nest : forall fe ge locals prefix parameters registers rename result source target memory,
  affine_nest_bound_dependencies prefix parameters nest ->
  affine_probe_stage_coverage registers nest prefix parameters -> affine_rename_injective registers rename ->
  affine_first_header_domain nest source ->
  affine_renamed_view (affine_probe_needed nest prefix parameters) rename source target ->
  exists after,
    exec_stmt fe ge locals target memory(affine_first_probe nest rename result) E0 after memory Out_normal /\
    after!result=Some(Vint(if affine_first_path_flag nest source then Int.one else Int.zero)).
Proof.
  induction nest as [leaf|iterator bound expression body child IH];
    intros fe ge locals prefix parameters registers rename result source target memory DEPENDENCIES COVERAGE UNIQUE DOMAIN VIEW.
  - exists(PTree.set result(Vint Int.one) target); split; [constructor; constructor|apply PTree.gss].
  - assert (ITERATOR:In iterator(affine_probe_needed(AffineSourceAxis iterator bound expression body child) prefix parameters)).
    { unfold affine_probe_needed; apply in_or_app; right; cbn; auto. }
    assert (BOUND:In bound(affine_probe_needed(AffineSourceAxis iterator bound expression body child) prefix parameters)).
    { unfold affine_probe_needed; apply in_or_app; right; cbn; auto. }
    destruct DOMAIN as [ITERATOR_WORD [BOUND_WORD DOMAIN]].
    pose proof(@affine_probe_header_test iterator bound _ rename ge locals source target memory
      ITERATOR BOUND ITERATOR_WORD BOUND_WORD VIEW) as TEST.
    destruct TEST as [test_value [EVAL BOOL]].
    destruct(Int.lt(temp_word iterator source)(temp_word bound source)) eqn:ACTIVE.
    + assert (SOURCE_ACTIVE:(Int.signed(temp_word iterator source)<Int.signed(temp_word bound source))%Z).
      { rewrite affine_integer_lt in ACTIVE; apply Z.ltb_lt; exact ACTIVE. }
      specialize(DOMAIN SOURCE_ACTIVE).
      pose proof(@affine_probe_stage_child_coverage registers prefix parameters iterator bound expression body child COVERAGE)
        as CHILD_COVERAGE.
      pose proof DEPENDENCIES as CHILD_DEPENDENCIES; destruct CHILD_DEPENDENCIES as [_ CHILD_DEPENDENCIES].
      destruct child as [code|child_iterator child_bound child_expression child_body grandchild].
      * assert (CHILD_VIEW:affine_renamed_view (affine_probe_needed(AffineSourceLeaf code)(prefix++[iterator]) parameters)
          rename source target).
        { eapply affine_renamed_view_weaken; [|exact VIEW].
          intros identifier MEMBER; unfold affine_probe_needed in *; repeat rewrite in_app_iff in *;
            cbn [List.In] in *; tauto. }
        destruct(IH fe ge locals (prefix++[iterator]) parameters registers rename result source target memory
          CHILD_DEPENDENCIES CHILD_COVERAGE UNIQUE I CHILD_VIEW) as [after [RUN RESULT]].
        exists after; split.
        -- eapply exec_Sifthenelse with (v1:=test_value)(b:=true); [exact EVAL|exact BOOL|exact RUN].
        -- cbn [affine_first_path_flag]; rewrite ACTIVE; exact RESULT.
      * destruct DOMAIN as [WORDS CHILD_DOMAIN].
        pose proof(@affine_probe_stage_child_reads prefix parameters iterator bound expression body
          child_iterator child_bound child_expression child_body grandchild DEPENDENCIES) as READS.
        pose proof(@affine_renamed_bound_evaluation child_expression _ rename ge locals source target memory
          READS WORDS VIEW) as BOUND_EVAL.
        set (word:=Int.repr(memory_source_affine_math(affine_word_valuation source) child_expression)).
        set (next:=PTree.set(rename child_iterator)(Vint Int.zero)
          (PTree.set(rename child_bound)(Vint word) target)).
        pose proof(@affine_probe_stage_child_view registers prefix parameters iterator bound expression body
          child_iterator child_bound child_expression child_body grandchild rename source target COVERAGE UNIQUE VIEW)
          as NEXT_VIEW.
        destruct(IH fe ge locals (prefix++[iterator]) parameters registers rename result
          (affine_first_child_temps(AffineSourceAxis child_iterator child_bound child_expression child_body grandchild) source)
          next memory CHILD_DEPENDENCIES CHILD_COVERAGE UNIQUE CHILD_DOMAIN NEXT_VIEW) as [after [RUN RESULT]].
        exists after; split.
        -- eapply exec_Sifthenelse with(v1:=test_value)(b:=true); [exact EVAL|exact BOOL|].
           eapply exec_Sseq_1 with(t1:=E0)(t2:=E0).
           ++ constructor; exact BOUND_EVAL.
           ++ eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [constructor; constructor|exact RUN].
        -- cbn [affine_first_path_flag]; rewrite ACTIVE; exact RESULT.
    + exists(PTree.set result(Vint Int.zero) target); split.
      * eapply exec_Sifthenelse with(v1:=test_value)(b:=false); [exact EVAL|exact BOOL|constructor; constructor].
      * cbn [affine_first_path_flag]; rewrite ACTIVE; apply PTree.gss.
Qed.
Print Assumptions affine_first_probe_partial_execution.
