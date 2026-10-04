From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryAffineSourceExpressions
  GuardMemoryAffineSourceLoop.
From GuardAffineNest Require Import AffineNestSyntax.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Each bound is evaluated before introducing its own coordinate. Earlier
    coordinates occupy the same reversed prefix as the real Loop semantics;
    the remaining context is the stable parameter list and optional metadata. *)
Fixpoint affine_loop_expression layout expression : option L.expr := match expression with
  | MemorySourceTemp identifier => option_map L.Var (memory_source_position identifier layout)
  | MemorySourceConstant value => Some(L.Constant value)
  | MemorySourceAdd first second =>
      match affine_loop_expression layout first,affine_loop_expression layout second with
      | Some first,Some second => Some(L.Sum first second) | _,_ => None end
  | MemorySourceSub first second =>
      match affine_loop_expression layout first,affine_loop_expression layout second with
      | Some first,Some second => Some(L.Sum first (L.Mult (-1) second)) | _,_ => None end
  | MemorySourceScale factor value | MemorySourceScaleLeft factor value =>
      option_map (L.Mult factor) (affine_loop_expression layout value) end.

Theorem affine_loop_expression_value expression layout encoded valuation :
  affine_loop_expression layout expression=Some encoded ->
  L.eval_expr (map valuation layout) encoded=memory_source_affine_math valuation expression.
Proof.
  revert encoded; induction expression; intros encoded LOWER; cbn [affine_loop_expression] in LOWER.
  - destruct (memory_source_position identifier layout) as [position|] eqn:POSITION; cbn in LOWER; [|discriminate].
    inversion LOWER; subst; cbn [L.eval_expr memory_source_affine_math].
    eapply memory_source_position_value; exact POSITION.
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

Fixpoint affine_lower_nest nest prefix parameters (root_lower : L.expr) (leaf : L.stmt) : option L.stmt :=
  match nest with
  | AffineSourceLeaf _ => Some leaf
  | AffineSourceAxis iterator _ expression _ child =>
      match affine_loop_expression (rev prefix++parameters) expression,
        affine_lower_nest child (prefix++[iterator]) parameters (L.Constant 0) leaf with
      | Some upper,Some body => Some(L.Loop root_lower upper body)
      | _,_ => None end end.

Lemma affine_lower_nest_axis iterator bound expression body child prefix parameters lower leaf encoded :
  affine_lower_nest (AffineSourceAxis iterator bound expression body child) prefix parameters lower leaf=Some encoded ->
  exists upper child_code,
    affine_loop_expression (rev prefix++parameters) expression=Some upper /\
    affine_lower_nest child (prefix++[iterator]) parameters (L.Constant 0) leaf=Some child_code /\
    encoded=L.Loop lower upper child_code.
Proof.
  cbn [affine_lower_nest].
  destruct (affine_loop_expression (rev prefix++parameters) expression) as [upper|] eqn:UPPER; [|discriminate].
  destruct (affine_lower_nest child (prefix++[iterator]) parameters (L.Constant 0) leaf) as [code|] eqn:CHILD; [|discriminate].
  intro RESULT; inversion RESULT; subst; exists upper,code; auto.
Qed.
Print Assumptions affine_loop_expression_value.
Print Assumptions affine_lower_nest_axis.
