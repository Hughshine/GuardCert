From Stdlib Require Import List ZArith.
From compcert.lib Require Import Coqlib.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceLoop.
From GuardAffineNest Require Import AffineNestLoopEncoding.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma affine_source_position_tail_value identifier layout position valuation tail :
  memory_source_position identifier layout=Some position ->
  nth position (map valuation layout++tail) 0=valuation identifier.
Proof.
  revert position; induction layout as [|first rest IH]; intros position LOOKUP; cbn in LOOKUP; [discriminate|].
  destruct (peq identifier first) as [->|OTHER].
  - inversion LOOKUP; reflexivity.
  - destruct (memory_source_position identifier rest) as [index|] eqn:INDEX; cbn in LOOKUP; [|discriminate].
    inversion LOOKUP; subst; cbn; apply IH; reflexivity.
Qed.

Theorem affine_loop_expression_tail_value expression layout encoded valuation tail :
  affine_loop_expression layout expression=Some encoded ->
  L.eval_expr (map valuation layout++tail) encoded=memory_source_affine_math valuation expression.
Proof.
  revert encoded; induction expression; intros encoded LOWER; cbn [affine_loop_expression] in LOWER.
  - destruct (memory_source_position identifier layout) as [position|] eqn:POSITION; cbn in LOWER; [|discriminate].
    inversion LOWER; subst; cbn [L.eval_expr memory_source_affine_math].
    eapply affine_source_position_tail_value; exact POSITION.
  - inversion LOWER; reflexivity.
  - destruct (affine_loop_expression layout expression1) as [first|] eqn:FIRST; [|discriminate].
    destruct (affine_loop_expression layout expression2) as [second|] eqn:SECOND; [|discriminate].
    inversion LOWER; subst; cbn [L.eval_expr memory_source_affine_math];
      rewrite (IHexpression1 _ eq_refl),(IHexpression2 _ eq_refl); reflexivity.
  - destruct (affine_loop_expression layout expression1) as [first|] eqn:FIRST; [|discriminate].
    destruct (affine_loop_expression layout expression2) as [second|] eqn:SECOND; [|discriminate].
    inversion LOWER; subst; cbn [L.eval_expr memory_source_affine_math];
      rewrite (IHexpression1 _ eq_refl),(IHexpression2 _ eq_refl); ring.
  - destruct (affine_loop_expression layout expression) as [first|] eqn:FIRST; cbn in LOWER; [|discriminate].
    inversion LOWER; subst; cbn [L.eval_expr memory_source_affine_math]; rewrite (IHexpression _ eq_refl); ring.
  - destruct (affine_loop_expression layout expression) as [first|] eqn:FIRST; cbn in LOWER; [|discriminate].
    inversion LOWER; subst; cbn [L.eval_expr memory_source_affine_math]; rewrite (IHexpression _ eq_refl); ring.
Qed.

Print Assumptions affine_loop_expression_tail_value.
