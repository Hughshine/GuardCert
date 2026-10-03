From Stdlib Require Import List ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation
  GuardMemoryAffineSourceLoop.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Endpoints read only the preserved source parameters. The row expression
    is supplied separately, e.g. zero or N-1. *)
Fixpoint memory_source_endpoint_expression row layout row_expression expression : option L.expr :=
  match expression with
  | MemorySourceTemp identifier => if peq identifier row then Some row_expression
    else option_map L.Var (memory_source_position identifier layout)
  | MemorySourceConstant value => Some (L.Constant value)
  | MemorySourceAdd first second =>
    match memory_source_endpoint_expression row layout row_expression first,
      memory_source_endpoint_expression row layout row_expression second with
    | Some first,Some second => Some (L.Sum first second) | _,_ => None end
  | MemorySourceSub first second =>
    match memory_source_endpoint_expression row layout row_expression first,
      memory_source_endpoint_expression row layout row_expression second with
    | Some first,Some second => Some (L.Sum first (L.Mult (-1) second)) | _,_ => None end
  | MemorySourceScale factor value | MemorySourceScaleLeft factor value =>
    option_map (L.Mult factor) (memory_source_endpoint_expression row layout row_expression value) end.
Theorem memory_source_endpoint_value expression row layout row_expression encoded valuation :
  memory_source_endpoint_expression row layout row_expression expression = Some encoded ->
  L.eval_expr (map valuation layout) encoded =
    memory_source_affine_math (memory_source_set_valuation valuation row
      (L.eval_expr (map valuation layout) row_expression)) expression.
Proof.
  revert encoded; induction expression; intros encoded LOWER; cbn [memory_source_endpoint_expression] in LOWER.
  - destruct (peq identifier row) as [SAME|OTHER].
    + inversion LOWER; subst; cbn [memory_source_affine_math];
        unfold memory_source_set_valuation; destruct (peq row row); congruence.
    + destruct (memory_source_position identifier layout) as [position|] eqn:POSITION; cbn in LOWER; [|discriminate].
      inversion LOWER; subst; cbn [L.eval_expr memory_source_affine_math].
      unfold memory_source_set_valuation; destruct (peq identifier row); [contradiction|].
      apply memory_source_position_value; exact POSITION.
  - inversion LOWER; reflexivity.
  - destruct (memory_source_endpoint_expression row layout row_expression expression1) as [first|] eqn:FIRST; [|discriminate].
    destruct (memory_source_endpoint_expression row layout row_expression expression2) as [second|] eqn:SECOND; [|discriminate].
    inversion LOWER; subst; cbn [L.eval_expr memory_source_affine_math]; rewrite (IHexpression1 _ eq_refl),(IHexpression2 _ eq_refl); reflexivity.
  - destruct (memory_source_endpoint_expression row layout row_expression expression1) as [first|] eqn:FIRST; [|discriminate].
    destruct (memory_source_endpoint_expression row layout row_expression expression2) as [second|] eqn:SECOND; [|discriminate].
    inversion LOWER; subst; cbn [L.eval_expr memory_source_affine_math]; rewrite (IHexpression1 _ eq_refl),(IHexpression2 _ eq_refl); ring.
  - destruct (memory_source_endpoint_expression row layout row_expression expression) as [first|] eqn:FIRST; cbn in LOWER; [|discriminate].
    inversion LOWER; subst; cbn [L.eval_expr memory_source_affine_math]; rewrite (IHexpression _ eq_refl); ring.
  - destruct (memory_source_endpoint_expression row layout row_expression expression) as [first|] eqn:FIRST; cbn in LOWER; [|discriminate].
    inversion LOWER; subst; cbn [L.eval_expr memory_source_affine_math]; rewrite (IHexpression _ eq_refl); ring.
Qed.
Definition memory_source_endpoint_test stride first last :=
  L.And (L.LE (L.Constant 1) first)
    (L.And (L.LE first (L.Constant stride))
      (L.And (L.LE (L.Constant 0) last) (L.LE last (L.Constant stride)))).
Theorem memory_source_endpoint_test_sound stride expression valuation row count first last :
  0 < count ->
  first = memory_source_affine_math (memory_source_set_valuation valuation row 0) expression ->
  last = memory_source_affine_math (memory_source_set_valuation valuation row (count-1)) expression ->
  1 <= first <= stride -> 0 <= last <= stride ->
  0 < first /\ forall value, 0 <= value < count ->
    0 <= memory_source_affine_math (memory_source_set_valuation valuation row value) expression <= stride.
Proof.
  intros COUNT FIRST LAST POSITIVE WIDTH; split; [lia|].
  intros value RANGE; apply memory_source_affine_row_extrema with (last := count-1); subst; lia.
Qed.
Print Assumptions memory_source_endpoint_value.
Print Assumptions memory_source_endpoint_test_sound.

Definition memory_source_endpoints row context expression :=
  match memory_source_endpoint_expression row context (L.Constant 0) expression,
    memory_source_endpoint_expression row context (L.Sum (L.Var O) (L.Constant (-1))) expression with
  | Some first,Some last => Some (first,last) | _,_ => None end.
Theorem memory_source_endpoints_sound expression row bound parameters valuation stride first last :
  0 < valuation bound ->
  memory_source_endpoints row (bound::parameters) expression = Some (first,last) ->
  L.eval_test (map valuation (bound::parameters)) (memory_source_endpoint_test stride first last) = true ->
  0 < memory_source_affine_math (memory_source_set_valuation valuation row 0) expression /\
  forall value, 0 <= value < valuation bound ->
    0 <= memory_source_affine_math (memory_source_set_valuation valuation row value) expression <= stride.
Proof.
  intros POSITIVE LOWER TEST; unfold memory_source_endpoints in LOWER.
  destruct (memory_source_endpoint_expression row (bound::parameters) (L.Constant 0) expression) as [a|] eqn:FIRST; [|discriminate].
  destruct (memory_source_endpoint_expression row (bound::parameters) (L.Sum (L.Var O) (L.Constant (-1))) expression) as [b|] eqn:LAST; [|discriminate].
  inversion LOWER; subst a b.
  unfold memory_source_endpoint_test in TEST; cbn [L.eval_test L.eval_expr] in TEST.
  repeat rewrite Bool.andb_true_iff in TEST; repeat rewrite Z.leb_le in TEST.
  pose proof (@memory_source_endpoint_value expression row (bound::parameters) (L.Constant 0) first valuation FIRST) as FIRST_VALUE.
  pose proof (@memory_source_endpoint_value expression row (bound::parameters) (L.Sum (L.Var O) (L.Constant (-1))) last valuation LAST) as LAST_VALUE.
  cbn [L.eval_expr map nth] in FIRST_VALUE,LAST_VALUE.
  replace (valuation bound + -1) with (valuation bound-1) in LAST_VALUE by ring.
  cbn [map] in TEST; rewrite FIRST_VALUE,LAST_VALUE in TEST.
  eapply memory_source_endpoint_test_sound; [exact POSITIVE|reflexivity|reflexivity|tauto|tauto].
Qed.
Print Assumptions memory_source_endpoints_sound.
