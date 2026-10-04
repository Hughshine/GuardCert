From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Coqlib Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightTempFrame ClightCountedLoop
  ClightRectangularLoops ClightRegionProgress ClightFrontendLoopProtocol ClightFrontendRegion ClightZeroTrip
  ClightFiniteRegion ClightStraightLine ClightPureExpr.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax.
Import ListNotations.
Set Implicit Arguments.

Theorem affine_child_setup_decode fe ge locals iterator bound expression body source temps memory after final :
  iterator <> bound ->
  flatten_region source = [Sset bound (memory_source_affine_code expression);rectangle_reset iterator;
    frontend_counted_loop iterator bound body] ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists word,
    eval_expr ge locals temps memory (memory_source_affine_code expression) (Vint word) /\
    exec_stmt fe ge locals (PTree.set iterator (Vint Int.zero) (PTree.set bound (Vint word) temps)) memory
      (frontend_counted_loop iterator bound body) E0 after final Out_normal.
Proof.
  intros DISTINCT SHAPE SOURCE; apply flatten_region_execution in SOURCE; rewrite SHAPE in SOURCE.
  inversion SOURCE; subst.
  match goal with SETUP : exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _ => inversion SETUP; subst end.
  match goal with REST : tail_execution _ _ _ [_;_] _ _ _ _ |- _ => inversion REST; subst end.
  match goal with RESET : exec_stmt _ _ _ _ _ (rectangle_reset _) _ _ _ _ |- _ =>
    unfold rectangle_reset in RESET; inversion RESET; subst;
    match goal with VALUE : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ => apply scalar_const_inv in VALUE; subst end
  end.
  match goal with REST : tail_execution _ _ _ [_] _ _ _ _ |- _ => inversion REST; subst end.
  match goal with REST : tail_execution _ _ _ [] _ _ _ _ |- _ => inversion REST; subst end.
  match goal with CHILD : exec_stmt _ _ _ _ _ (frontend_counted_loop _ _ _) _ _ _ _ |- _ =>
    destruct (frontend_entry_test CHILD) as [flag TEST];
    destruct (counter_test_domain TEST) as [iterator_word [upper_word [ITERATOR BOUND]]];
    cbn [entry_temps] in BOUND;
    rewrite PTree.gso in BOUND by congruence;
    rewrite PTree.gss in BOUND;
    inversion BOUND; subst;
    exists upper_word; split; [assumption|exact CHILD]
  end.
Qed.
Corollary affine_child_setup_read_words fe ge locals iterator bound expression body source temps memory after final :
  iterator <> bound ->
  flatten_region source = [Sset bound (memory_source_affine_code expression);rectangle_reset iterator;
    frontend_counted_loop iterator bound body] ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  forall identifier, In identifier (memory_source_affine_reads expression) ->
    exists word, temps ! identifier = Some (Vint word).
Proof.
  intros DISTINCT SHAPE SOURCE.
  destruct (@affine_child_setup_decode fe ge locals iterator bound expression body source temps memory after final
    DISTINCT SHAPE SOURCE) as [word [EVAL CHILD]].
  eapply memory_source_affine_defined_words; exact EVAL.
Qed.
Print Assumptions affine_child_setup_decode.
Print Assumptions affine_child_setup_read_words.
