From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Coqlib Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightTempFrame ClightCountedLoop
  ClightLoopSyntax ClightRegionProgress ClightFrontendLoopProtocol ClightFrontendRegion ClightZeroTrip ClightPureExpr.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions GuardMemoryStartedFirstLeaf.
From GuardAffineNest Require Import AffineNestSyntax AffineNestWords AffineNestExit AffineNestSourceShape.
Import ListNotations.
Set Implicit Arguments.

Definition affine_expression_word_domain expression temps :=
  forall identifier, In identifier (memory_source_affine_reads expression) ->
    exists word,temps!identifier=Some(Vint word).
Lemma affine_expression_word_value expression ge locals temps memory word :
  eval_expr ge locals temps memory (memory_source_affine_code expression) (Vint word) ->
  word=Int.repr(memory_source_affine_math (affine_word_valuation temps) expression).
Proof.
  intro EVAL.
  assert (FORWARD:eval_expr ge locals temps memory (memory_source_affine_code expression)
    (Vint(Int.repr(memory_source_affine_math (affine_word_valuation temps) expression)))).
  { apply memory_source_affine_evaluation; intros identifier MEMBER.
    destruct (@memory_source_affine_defined_words expression ge locals temps memory word EVAL identifier MEMBER) as [value LOOKUP].
    unfold affine_word_valuation,temp_word; rewrite LOOKUP,Int.repr_signed; reflexivity. }
  pose proof (@pure_scalar_determinate (memory_source_affine_code expression)
    (memory_source_affine_pure expression) ge locals temps memory _ _ EVAL FORWARD) as SAME.
  inversion SAME; reflexivity.
Qed.

Fixpoint affine_first_header_domain nest temps := match nest with
  | AffineSourceLeaf _ => True
  | AffineSourceAxis iterator bound _ _ child =>
      (exists word,temps!iterator=Some(Vint word)) /\
      (exists word,temps!bound=Some(Vint word)) /\
      (Int.signed(temp_word iterator temps)<Int.signed(temp_word bound temps) ->
       match child with
       | AffineSourceLeaf _ => True
       | AffineSourceAxis child_iterator child_bound expression _ _ =>
           affine_expression_word_domain expression temps /\
           affine_first_header_domain child
             (PTree.set child_iterator (Vint Int.zero)
               (PTree.set child_bound (Vint(Int.repr(memory_source_affine_math (affine_word_valuation temps) expression))) temps)) end) end.

Theorem affine_source_first_header_domain nest fe ge locals temps memory after final :
  affine_nest_shapes nest -> NoDup(affine_nest_controls nest) ->
  normal_statement(affine_nest_leaf nest)=true -> quiet_statement(affine_nest_leaf nest)=true ->
  writes_only [] (affine_nest_leaf nest) ->
  exec_stmt fe ge locals temps memory (affine_nest_source nest) E0 after final Out_normal ->
  affine_first_header_domain nest temps.
Proof.
  revert temps memory after final; induction nest as [leaf|iterator bound expression body child IH];
    intros temps memory after final SHAPES FRESH NORMAL QUIET WRITES SOURCE; [exact I|].
  change (exec_stmt fe ge locals temps memory (frontend_counted_loop iterator bound body) E0 after final Out_normal) in SOURCE.
  destruct (frontend_entry_test SOURCE) as [flag TEST].
  destruct (counter_test_domain TEST) as [word [upper [ITERATOR BOUND]]].
  cbn [entry_temps] in ITERATOR,BOUND.
  cbn [affine_first_header_domain]; split; [exists word; exact ITERATOR|split; [exists upper; exact BOUND|]].
  intro ACTIVE.
  assert (ITERATOR_FRESH:~In iterator (affine_nest_controls child)).
  { inversion FRESH as [|first rest NOT_IN TAIL]; subst; intro MEMBER; apply NOT_IN; cbn; auto. }
  destruct (@affine_exit_fresh_child iterator bound expression body child FRESH)
    as [CHILD_FRESH [BOUND_FRESH DISTINCT]].
  destruct (@memory_frontend_active_body fe ge locals iterator bound body (affine_nest_controls child)
    temps memory after final (@affine_nest_body_normal iterator bound expression body child SHAPES NORMAL QUIET)
    (@affine_nest_body_writes iterator bound expression body child SHAPES WRITES)
    ITERATOR_FRESH BOUND_FRESH ACTIVE SOURCE) as [next [target BODY]].
  destruct SHAPES as [SHAPE SHAPES].
  destruct child as [leaf|child_iterator child_bound child_expression child_body child]; [exact I|].
  destruct (@affine_exit_fresh_child child_iterator child_bound child_expression child_body child CHILD_FRESH)
    as [GRANDCHILD_FRESH [CHILD_BOUND_FRESH CHILD_DISTINCT]].
  destruct (@affine_child_setup_decode fe ge locals child_iterator child_bound child_expression child_body body
    temps memory next target CHILD_DISTINCT SHAPE BODY) as [child_upper [EVAL CHILD]].
  split.
  - intros identifier MEMBER; eapply memory_source_affine_defined_words; eassumption.
  - pose proof (@affine_expression_word_value child_expression ge locals temps memory child_upper EVAL) as VALUE.
    rewrite <-VALUE; eapply IH; eassumption.
Qed.
Print Assumptions affine_expression_word_value.
Print Assumptions affine_source_first_header_domain.
