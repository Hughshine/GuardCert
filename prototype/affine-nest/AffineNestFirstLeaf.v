From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightNoWrap ClightLoopSyntax ClightRegionProgress ClightTempFrame
  ClightFrontendLoopProtocol.
From GuardMemory Require Import GuardMemoryStartedFirstLeaf GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestWords AffineNestExit
  AffineNestSourceShape AffineNestFirstDomain.
Import ListNotations.
Set Implicit Arguments.

Definition affine_first_child_temps child temps := match child with
  | AffineSourceLeaf _ => temps
  | AffineSourceAxis iterator bound expression _ _ =>
      PTree.set iterator (Vint Int.zero)
        (PTree.set bound (Vint(Int.repr(memory_source_affine_math (affine_word_valuation temps) expression))) temps) end.
Fixpoint affine_first_path_active nest temps := match nest with
  | AffineSourceLeaf _ => True
  | AffineSourceAxis iterator bound _ _ child =>
      (Int.signed(temp_word iterator temps)<Int.signed(temp_word bound temps))%Z /\
      affine_first_path_active child (affine_first_child_temps child temps) end.

Lemma affine_first_child_frame child protected temps :
  (forall identifier, In identifier protected -> ~In identifier (affine_nest_controls child)) ->
  temp_agree protected temps (affine_first_child_temps child temps).
Proof.
  intro FRESH; destruct child; [apply temp_agree_refl|].
  cbn [affine_first_child_temps].
  eapply temp_agree_trans; apply temp_agree_set;
    intro MEMBER; [apply(FRESH bound MEMBER)|apply(FRESH iterator MEMBER)]; cbn; auto.
Qed.

Theorem affine_source_first_leaf nest fe ge locals protected temps memory after final :
  affine_nest_shapes nest -> NoDup(affine_nest_controls nest) ->
  normal_statement(affine_nest_leaf nest)=true -> quiet_statement(affine_nest_leaf nest)=true ->
  writes_only [] (affine_nest_leaf nest) ->
  (forall identifier, In identifier protected -> ~In identifier (affine_nest_controls nest)) ->
  affine_first_path_active nest temps ->
  exec_stmt fe ge locals temps memory (affine_nest_source nest) E0 after final Out_normal ->
  exists leaf_temps leaf_after leaf_final,
    temp_agree protected temps leaf_temps /\
    exec_stmt fe ge locals leaf_temps memory (affine_nest_leaf nest) E0 leaf_after leaf_final Out_normal.
Proof.
  revert temps memory after final.
  induction nest as [code|iterator bound expression body child IH];
    intros temps memory after final SHAPES FRESH NORMAL QUIET WRITES PROTECTED ACTIVE SOURCE.
  - exists temps,after,final; split; [apply temp_agree_refl|exact SOURCE].
  - change (exec_stmt fe ge locals temps memory (frontend_counted_loop iterator bound body) E0 after final Out_normal) in SOURCE.
    destruct ACTIVE as [ROOT_ACTIVE CHILD_ACTIVE].
    destruct (@affine_exit_fresh_child iterator bound expression body child FRESH)
      as [CHILD_FRESH [BOUND_FRESH DISTINCT]].
    assert (ITERATOR_FRESH:~In iterator (affine_nest_controls child)).
    { inversion FRESH as [|first rest NOT_IN TAIL]; subst; intro MEMBER; apply NOT_IN; cbn; auto. }
    destruct (@memory_frontend_active_body fe ge locals iterator bound body (affine_nest_controls child)
      temps memory after final (@affine_nest_body_normal iterator bound expression body child SHAPES NORMAL QUIET)
      (@affine_nest_body_writes iterator bound expression body child SHAPES WRITES)
      ITERATOR_FRESH BOUND_FRESH ROOT_ACTIVE SOURCE) as [next [target BODY]].
    destruct SHAPES as [SHAPE CHILD_SHAPES].
    assert (CHILD_PROTECTED:forall identifier, In identifier protected -> ~In identifier (affine_nest_controls child)).
    { intros identifier MEMBER BAD; apply(PROTECTED identifier MEMBER); cbn; auto. }
    destruct child as [leaf|child_iterator child_bound child_expression child_body grandchild].
    + cbn [affine_nest_child_shape] in SHAPE; subst body.
      exists temps,next,target; split; [apply temp_agree_refl|exact BODY].
    + destruct (@affine_exit_fresh_child child_iterator child_bound child_expression child_body grandchild CHILD_FRESH)
        as [GRANDCHILD_FRESH [CHILD_BOUND_FRESH CHILD_DISTINCT]].
      destruct (@affine_child_setup_decode fe ge locals child_iterator child_bound child_expression child_body body
        temps memory next target CHILD_DISTINCT SHAPE BODY) as [word [EVAL CHILD]].
      pose proof (@affine_expression_word_value child_expression ge locals temps memory word EVAL) as VALUE.
      rewrite VALUE in CHILD.
      destruct (IH _ _ _ _ CHILD_SHAPES CHILD_FRESH NORMAL QUIET WRITES CHILD_PROTECTED CHILD_ACTIVE CHILD)
        as [leaf_temps [leaf_after [leaf_final [FRAME LEAF]]]].
      exists leaf_temps,leaf_after,leaf_final; split; [|exact LEAF].
      eapply temp_agree_trans; [apply affine_first_child_frame; exact CHILD_PROTECTED|exact FRAME].
Qed.
Print Assumptions affine_first_child_frame.
Print Assumptions affine_source_first_leaf.
