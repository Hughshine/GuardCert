From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Integers.
From compcert.common Require Import Values Memory.
From compcert.cfrontend Require Import Clight.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestLoopEncoding AffineNestExit AffineNestFirstDomain.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Reuse the checked interval analysis of the concrete language instance.
    This initial policy conservatively requires intermediate mathematical
    operations to fit as well; it is not a weakest-condition algorithm. *)
Definition check_affine_bound_cap layout bounds expression cap :=
  match affine_loop_expression layout expression with
  | Some encoded => match MemoryNested.A.analyze bounds encoded with
    | Some interval => MemoryNested.A.upper interval <=? cap
    | None => false end
  | None => false end.

Theorem checked_affine_bound_exact layout bounds expression cap ge locals temps memory word :
  check_affine_bound_cap layout bounds expression cap=true ->
  MemoryNested.A.env_within bounds (map (affine_word_valuation temps) layout) ->
  eval_expr ge locals temps memory (memory_source_affine_code expression) (Vint word) ->
  Int.signed word=memory_source_affine_math (affine_word_valuation temps) expression /\
  Int.signed word<=cap.
Proof.
  unfold check_affine_bound_cap.
  destruct (affine_loop_expression layout expression) as [encoded|] eqn:ENCODE; [|discriminate].
  destruct (MemoryNested.A.analyze bounds encoded) as [interval|] eqn:ANALYZE; [|discriminate].
  intros CAP VIEW EVAL; apply Z.leb_le in CAP.
  destruct (@MemoryNested.A.analyze_sound encoded bounds interval
    (map (affine_word_valuation temps) layout) ANALYZE VIEW) as [CONTAINS SAFE].
  pose proof (@MemoryNested.A.affine_safe_range encoded
    (map (affine_word_valuation temps) layout) SAFE) as RANGE.
  change (Int.min_signed<=L.eval_expr (map (affine_word_valuation temps) layout) encoded<=Int.max_signed) in RANGE.
  change (MemoryNested.A.lower interval<=L.eval_expr (map (affine_word_valuation temps) layout) encoded<=MemoryNested.A.upper interval) in CONTAINS.
  pose proof (@affine_loop_expression_value expression layout encoded (affine_word_valuation temps) ENCODE) as VALUE.
  assert (SIGNED:Int.min_signed<=memory_source_affine_math (affine_word_valuation temps) expression<=Int.max_signed).
  { rewrite <-VALUE; exact RANGE. }
  assert (BOUND:memory_source_affine_math (affine_word_valuation temps) expression<=cap).
  { rewrite <-VALUE; eapply Z.le_trans; [exact(proj2 CONTAINS)|exact CAP]. }
  pose proof (@affine_expression_word_value expression ge locals temps memory word EVAL) as WORD.
  rewrite WORD,Int.signed_repr by exact SIGNED.
  split; [reflexivity|exact BOUND].
Qed.
Print Assumptions check_affine_bound_cap.
Print Assumptions checked_affine_bound_exact.
