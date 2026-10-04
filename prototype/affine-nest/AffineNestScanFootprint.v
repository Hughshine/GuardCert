From Stdlib Require Import List ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From polcert.lib Require Import Misc.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryLoopTrace
  GuardMemoryFiniteFootprint GuardMemoryRectangularFootprint GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation.
From GuardAffineNest Require Import AffineNestSyntax AffineNestLoopEncoding AffineNestExpressionTail
  AffineNestValuation AffineNestLeafLoop AffineNestScanModel AffineNestScanPoints.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma affine_leaf_trace_footprint instructions coordinates parameters tail :
  memory_events_footprint(memory_loop_list_trace
    (affine_leaf_sequence(length coordinates)(length parameters) instructions)(rev coordinates++parameters++tail))=
  memory_point_footprint instructions(coordinates++parameters).
Proof.
  induction instructions; [reflexivity|].
  cbn [affine_leaf_sequence memory_loop_list_trace memory_loop_trace].
  unfold memory_events_footprint at 1; rewrite flat_map_app.
  cbn [flat_map event_instruction event_arguments]; rewrite affine_leaf_arguments_value,app_nil_r.
  change(memory_instruction_footprint a(coordinates++parameters)++
    memory_events_footprint(memory_loop_list_trace
      (affine_leaf_sequence(length coordinates)(length parameters) instructions)(rev coordinates++parameters++tail))=
    memory_point_footprint(a::instructions)(coordinates++parameters)).
  rewrite IHinstructions; reflexivity.
Qed.

Lemma affine_scan_iterator_fresh (prefix parameters:list ident) iterator rest :
  NoDup((prefix++iterator::rest)++parameters) -> ~In iterator(prefix++parameters).
Proof.
  intro UNIQUE; rewrite <-app_assoc in UNIQUE; cbn in UNIQUE.
  pose proof(NoDup_remove_2 prefix (rest++parameters) iterator UNIQUE) as FRESH.
  intro MEMBER; apply FRESH; repeat rewrite in_app_iff in *; tauto.
Qed.
Print Assumptions affine_leaf_trace_footprint.

Theorem affine_scan_source_footprint nest : forall coordinates prefix parameters instructions valuation lower lower_code code tail,
  coordinates=prefix++affine_nest_iterators nest -> NoDup(coordinates++parameters) ->
  affine_lower_nest nest prefix parameters lower_code
    (L.Seq(affine_leaf_sequence(length coordinates)(length parameters) instructions))=Some code ->
  L.eval_expr(map valuation(rev prefix++parameters)++tail) lower_code=lower ->
  memory_events_footprint(memory_loop_trace code(map valuation(rev prefix++parameters)++tail))=
  flat_map(fun point=>memory_point_footprint instructions(map point(coordinates++parameters)))
    (affine_scan_points nest valuation lower).
Proof.
  induction nest as [source|iterator bound expression body child IH];
    intros coordinates prefix parameters instructions valuation lower lower_code code tail COORDINATES UNIQUE LOWER VALUE.
  - cbn [affine_lower_nest] in LOWER; inversion LOWER; subst code.
    cbn [affine_nest_iterators] in COORDINATES; rewrite app_nil_r in COORDINATES; subst coordinates.
    cbn [affine_scan_points flat_map memory_loop_trace]; rewrite app_nil_r,map_app.
    rewrite map_app,map_rev,<-app_assoc.
    replace(length prefix) with(length(map valuation prefix)) by apply length_map.
    replace(length parameters) with(length(map valuation parameters)) by apply length_map.
    apply affine_leaf_trace_footprint.
  - destruct(@affine_lower_nest_axis iterator bound expression body child prefix parameters lower_code
      (L.Seq(affine_leaf_sequence(length coordinates)(length parameters) instructions)) code LOWER)
      as [upper_code [child_code [UPPER [CHILD CODE]]]]; subst code.
    cbn [memory_loop_trace]; rewrite VALUE.
    assert(UPPER_VALUE:L.eval_expr(map valuation(rev prefix++parameters)++tail) upper_code=
      memory_source_affine_math valuation expression).
    { eapply affine_loop_expression_tail_value; exact UPPER. }
    rewrite UPPER_VALUE.
    cbn [affine_scan_points]; unfold memory_events_footprint at 1.
    rewrite !memory_flat_map_associative; apply flat_map_ext; intro value.
    change(memory_events_footprint(memory_loop_trace child_code(value::(map valuation(rev prefix++parameters)++tail)))=
      flat_map(fun point=>memory_point_footprint instructions(map point(coordinates++parameters)))
        (affine_scan_points child(memory_source_set_valuation valuation iterator value) 0)).
    assert(FRESH:~In iterator(prefix++parameters)).
    { apply affine_scan_iterator_fresh with(rest:=affine_nest_iterators child).
      cbn [affine_nest_iterators] in COORDINATES; rewrite <-COORDINATES; exact UNIQUE. }
    replace(value::(map valuation(rev prefix++parameters)++tail)) with
      (map(memory_source_set_valuation valuation iterator value)(rev(prefix++[iterator])++parameters)++tail)
      by(apply affine_valuation_loop_environment; exact FRESH).
    apply IH with(prefix:=prefix++[iterator])(lower_code:=L.Constant 0); try assumption; try reflexivity.
    rewrite COORDINATES; cbn [affine_nest_iterators]; rewrite <-app_assoc; reflexivity.
Qed.
Print Assumptions affine_scan_source_footprint.
