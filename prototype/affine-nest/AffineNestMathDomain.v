From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightNoWrap ClightPureExpr ClightTempFrame ClightCountedLoop.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation
  GuardMemoryIntervalBox.
From GuardAffineNest Require Import AffineNestSyntax AffineNestWords AffineNestValuation.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** This semantic domain contains only integer facts. AffineNestPackageGuard
    proves it from the generated runtime check, keeping this definition
    separate from source syntax and the candidate dependence certificate. *)
Fixpoint affine_math_domain bounds layout nest valuation lower : Prop := match nest with
  | AffineSourceLeaf _ => interval_ranges bounds (map valuation layout)
  | AffineSourceAxis iterator _ expression _ child =>
      signed_range lower /\ signed_range(memory_source_affine_math valuation expression) /\
      forall value, lower<=value<memory_source_affine_math valuation expression ->
        affine_math_domain bounds layout child (memory_source_set_valuation valuation iterator value) 0 end.

Lemma affine_bound_word_from_view expression registers valuation ge locals temps memory word :
  (forall identifier, In identifier(memory_source_affine_reads expression) -> In identifier registers) ->
  affine_word_view registers valuation temps ->
  eval_expr ge locals temps memory (memory_source_affine_code expression) (Vint word) ->
  word=Int.repr(memory_source_affine_math valuation expression).
Proof.
  intros READS WORDS EVAL.
  assert (EXPECTED:eval_expr ge locals temps memory (memory_source_affine_code expression)
    (Vint(Int.repr(memory_source_affine_math valuation expression)))).
  { apply memory_source_affine_evaluation; intros identifier MEMBER; apply WORDS,READS; exact MEMBER. }
  pose proof (@pure_scalar_determinate (memory_source_affine_code expression)
    (memory_source_affine_pure expression) ge locals temps memory _ _ EVAL EXPECTED) as SAME.
  inversion SAME; reflexivity.
Qed.
Print Assumptions affine_math_domain.
Print Assumptions affine_bound_word_from_view.
