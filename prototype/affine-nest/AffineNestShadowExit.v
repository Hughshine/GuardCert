From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightCountedProtocol
  ClightFrontendLoopProtocol ClightFrontendRegion ClightLoopExecution ClightLoopSyntax
  ClightFramedLoop ClightTempFrame ClightNoWrap ClightRectangularLoops ClightRegionProgress.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestWords AffineNestExit
  AffineNestSourceShape AffineNestFirstDomain AffineNestControlTransfer.
Import ListNotations.
Set Implicit Arguments.

(** Replaying only the pure control code restores the exact source exit,
    including empty child loops and helpers that remain undefined. It reads
    no source data and makes no assumption that a final child is active.
    This baseline may cost as many control iterations as the source. *)
Fixpoint affine_shadow_source nest := match nest with
  | AffineSourceLeaf _ => Sskip
  | AffineSourceAxis iterator bound _ _ child =>
      frontend_counted_loop iterator bound
        (match child with
        | AffineSourceLeaf _ => Sskip
        | AffineSourceAxis child_iterator child_bound expression _ _ =>
            Ssequence (Sset child_bound (memory_source_affine_code expression))
              (Ssequence (rectangle_reset child_iterator) (affine_shadow_source child)) end) end.
Definition affine_shadow_body child := match child with
  | AffineSourceLeaf _ => Sskip
  | AffineSourceAxis iterator bound expression _ _ =>
      Ssequence (Sset bound (memory_source_affine_code expression))
        (Ssequence (rectangle_reset iterator) (affine_shadow_source child)) end.

Lemma affine_expression_memory_transfer expression ge locals temps memory word other_memory :
  eval_expr ge locals temps memory (memory_source_affine_code expression) (Vint word) ->
  eval_expr ge locals temps other_memory (memory_source_affine_code expression) (Vint word).
Proof.
  intro EVAL; rewrite (@affine_expression_word_value expression ge locals temps memory word EVAL).
  apply memory_source_affine_evaluation; intros identifier MEMBER.
  destruct (@memory_source_affine_defined_words expression ge locals temps memory word EVAL identifier MEMBER)
    as [value LOOKUP].
  unfold affine_word_valuation,temp_word; rewrite LOOKUP,Int.repr_signed; reflexivity.
Qed.

Lemma affine_no_temp_writes_exact fe ge locals temps memory source trace after final outcome :
  writes_only [] source -> exec_stmt fe ge locals temps memory source trace after final outcome -> after=temps.
Proof.
  intros WRITES RUN; apply PTree.extensionality; intro identifier.
  eapply writes_only_frame; [exact RUN|exact WRITES|cbn; auto].
Qed.

Theorem affine_source_shadow_exit nest fe ge locals temps memory after final :
  affine_nest_shapes nest -> NoDup(affine_nest_controls nest) ->
  normal_statement(affine_nest_leaf nest)=true -> quiet_statement(affine_nest_leaf nest)=true ->
  writes_only [] (affine_nest_leaf nest) ->
  exec_stmt fe ge locals temps memory (affine_nest_source nest) E0 after final Out_normal ->
  forall shadow_memory,
  exec_stmt fe ge locals temps shadow_memory (affine_shadow_source nest) E0 after shadow_memory Out_normal.
Proof.
  revert temps memory after final.
  induction nest as [leaf|iterator bound expression body child IH];
    intros temps memory after final SHAPES FRESH NORMAL QUIET WRITES SOURCE shadow_memory.
  - cbn [affine_nest_source] in SOURCE; cbn [affine_nest_leaf] in WRITES.
    pose proof (@affine_no_temp_writes_exact fe ge locals temps memory leaf E0 after final Out_normal WRITES SOURCE) as SAME.
    subst after; constructor.
  - change (exec_stmt fe ge locals temps memory (frontend_counted_loop iterator bound body) E0 after final Out_normal) in SOURCE.
    destruct (@affine_exit_fresh_child iterator bound expression body child FRESH)
      as [CHILD_FRESH [BOUND_FRESH DISTINCT]].
    assert (ITERATOR_FRESH:~In iterator (affine_nest_controls child)).
    { inversion FRESH as [|first rest NOT_IN TAIL]; subst; intro MEMBER; apply NOT_IN; cbn; auto. }
    assert (BODY_FRAME:forall before source_memory trace next target,
      exec_stmt fe ge locals before source_memory body trace next target Out_normal ->
      temp_agree [iterator;bound] before next).
    { intros before source_memory trace next target RUN.
      eapply structured_temp_frame; [eapply affine_nest_body_writes; eassumption| |exact RUN].
      intros identifier MEMBER; cbn in MEMBER; destruct MEMBER as [SAME|[SAME|BAD]];
        [subst; exact ITERATOR_FRESH|subst; exact BOUND_FRESH|contradiction]. }
    assert (BODY_SHADOW:forall before source_memory next target,
      exec_stmt fe ge locals before source_memory body E0 next target Out_normal ->
      forall private_memory,
      exec_stmt fe ge locals before private_memory (affine_shadow_body child) E0 next private_memory Out_normal).
    { intros before source_memory next target RUN private_memory.
      destruct SHAPES as [SHAPE CHILD_SHAPES].
      destruct child as [code|child_iterator child_bound child_expression child_body grandchild].
      - cbn [affine_nest_child_shape] in SHAPE; subst body.
        cbn [affine_nest_leaf] in WRITES.
        pose proof (@affine_no_temp_writes_exact fe ge locals before source_memory code E0 next target Out_normal WRITES RUN) as SAME.
        subst next; constructor.
      - destruct (@affine_exit_fresh_child child_iterator child_bound child_expression child_body grandchild CHILD_FRESH)
          as [GRANDCHILD_FRESH [CHILD_BOUND_FRESH CHILD_DISTINCT]].
        destruct (@affine_child_setup_decode fe ge locals child_iterator child_bound child_expression child_body body
          before source_memory next target CHILD_DISTINCT SHAPE RUN) as [word [EVAL CHILD]].
        cbn [affine_shadow_body].
        eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
        + constructor; eapply affine_expression_memory_transfer; exact EVAL.
        + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
          * unfold rectangle_reset; constructor; constructor.
          * eapply IH; eassumption. }
    change (exec_stmt fe ge locals temps shadow_memory
      (frontend_counted_loop iterator bound (affine_shadow_body child)) E0 after shadow_memory Out_normal).
    eapply affine_frontend_control_transfer; [exact DISTINCT| |exact BODY_FRAME|exact BODY_SHADOW|exact SOURCE].
    eapply affine_nest_body_normal; eassumption.
Qed.
Print Assumptions affine_expression_memory_transfer.
Print Assumptions affine_no_temp_writes_exact.
Print Assumptions affine_source_shadow_exit.
