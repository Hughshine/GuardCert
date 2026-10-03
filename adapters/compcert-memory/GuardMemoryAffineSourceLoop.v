From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint memory_source_position identifier layout : option nat :=
  match layout with
  | [] => None
  | first::rest => if peq identifier first then Some O else option_map S (memory_source_position identifier rest) end.
Fixpoint memory_source_loop_expression row layout expression : option L.expr :=
  match expression with
  | MemorySourceTemp identifier =>
    if peq identifier row then Some (L.Var O)
    else option_map (fun position => L.Var (S position)) (memory_source_position identifier layout)
  | MemorySourceConstant value => Some (L.Constant value)
  | MemorySourceAdd first second =>
    match memory_source_loop_expression row layout first,memory_source_loop_expression row layout second with
    | Some first,Some second => Some (L.Sum first second) | _,_ => None end
  | MemorySourceSub first second =>
    match memory_source_loop_expression row layout first,memory_source_loop_expression row layout second with
    | Some first,Some second => Some (L.Sum first (L.Mult (-1) second)) | _,_ => None end
  | MemorySourceScale factor value | MemorySourceScaleLeft factor value =>
    option_map (L.Mult factor) (memory_source_loop_expression row layout value) end.
Lemma memory_source_position_value identifier layout position valuation :
  memory_source_position identifier layout = Some position ->
  nth position (map valuation layout) 0 = valuation identifier.
Proof.
  revert position; induction layout as [|first rest IH]; intros position LOOKUP; cbn in LOOKUP; [discriminate|].
  destruct (peq identifier first) as [->|OTHER].
  - inversion LOOKUP; reflexivity.
  - destruct (memory_source_position identifier rest) as [index|] eqn:INDEX; cbn in LOOKUP; [|discriminate].
    inversion LOOKUP; subst; cbn; apply IH; reflexivity.
Qed.
Theorem memory_source_loop_expression_value expression row layout encoded valuation value :
  memory_source_loop_expression row layout expression = Some encoded ->
  L.eval_expr (value::map valuation layout) encoded =
    memory_source_affine_math (memory_source_set_valuation valuation row value) expression.
Proof.
  revert encoded; induction expression; intros encoded LOWER; cbn [memory_source_loop_expression] in LOWER.
  - destruct (peq identifier row) as [SAME|OTHER].
    + inversion LOWER; subst; cbn [L.eval_expr nth memory_source_affine_math];
        unfold memory_source_set_valuation; destruct (peq row row); congruence.
    + destruct (memory_source_position identifier layout) as [position|] eqn:POSITION; cbn in LOWER; [|discriminate].
      inversion LOWER; subst; cbn [L.eval_expr nth memory_source_affine_math].
      unfold memory_source_set_valuation; destruct (peq identifier row); [contradiction|].
      apply memory_source_position_value; exact POSITION.
  - inversion LOWER; reflexivity.
  - destruct (memory_source_loop_expression row layout expression1) as [first|] eqn:FIRST; [|discriminate].
    destruct (memory_source_loop_expression row layout expression2) as [second|] eqn:SECOND; [|discriminate].
    inversion LOWER; subst; cbn [L.eval_expr memory_source_affine_math]; rewrite (IHexpression1 _ eq_refl),(IHexpression2 _ eq_refl); reflexivity.
  - destruct (memory_source_loop_expression row layout expression1) as [first|] eqn:FIRST; [|discriminate].
    destruct (memory_source_loop_expression row layout expression2) as [second|] eqn:SECOND; [|discriminate].
    inversion LOWER; subst; cbn [L.eval_expr memory_source_affine_math]; rewrite (IHexpression1 _ eq_refl),(IHexpression2 _ eq_refl); ring.
  - destruct (memory_source_loop_expression row layout expression) as [first|] eqn:FIRST; cbn in LOWER; [|discriminate].
    inversion LOWER; subst; cbn [L.eval_expr memory_source_affine_math]; rewrite (IHexpression _ eq_refl); ring.
  - destruct (memory_source_loop_expression row layout expression) as [first|] eqn:FIRST; cbn in LOWER; [|discriminate].
    inversion LOWER; subst; cbn [L.eval_expr memory_source_affine_math]; rewrite (IHexpression _ eq_refl); ring.
Qed.
Print Assumptions memory_source_loop_expression_value.
