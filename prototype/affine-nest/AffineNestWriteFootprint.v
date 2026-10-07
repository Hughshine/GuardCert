From Stdlib Require Import List ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From polcert.lib Require Import Misc.
From polcert.src Require Import PolyBase.
From Guard Require Import CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryLoopTrace
  GuardMemoryObservationStability GuardMemoryRectangularFootprint GuardMemoryAffineSourceExpressions
  GuardMemoryAffineSourceValuation GuardMemoryNaryCompute GuardMemoryWindowCompute GuardMemoryRectangles
  GuardMemoryFiniteFootprint.
From GuardAffineNest Require Import AffineNestSyntax AffineNestLoopEncoding AffineNestExpressionTail
  AffineNestValuation AffineNestLeafLoop AffineNestScanModel AffineNestScanPoints AffineNestScanFootprint
  AffineNestScanAccesses.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Bound stability excludes writes only. Reads may alias the observed word;
    they still occur in the source-derived capability domain. *)
Lemma affine_leaf_trace_writes instructions coordinates parameters tail :
  map memory_event_write (memory_loop_list_trace
    (affine_leaf_sequence(length coordinates)(length parameters) instructions)(rev coordinates++parameters++tail))=
  map (fun instruction=>exact_cell(instruction_write instruction)(coordinates++parameters)) instructions.
Proof.
  induction instructions; [reflexivity|].
  cbn [affine_leaf_sequence memory_loop_list_trace memory_loop_trace].
  rewrite map_app; cbn [map memory_event_write event_instruction event_arguments].
  rewrite affine_leaf_arguments_value; cbn [memory_event_write event_instruction event_arguments app].
  f_equal; exact IHinstructions.
Qed.

Theorem affine_scan_source_writes nest : forall coordinates prefix parameters instructions valuation lower lower_code code tail,
  coordinates=prefix++affine_nest_iterators nest -> NoDup(coordinates++parameters) ->
  affine_lower_nest nest prefix parameters lower_code
    (L.Seq(affine_leaf_sequence(length coordinates)(length parameters) instructions))=Some code ->
  L.eval_expr(map valuation(rev prefix++parameters)++tail) lower_code=lower ->
  map memory_event_write(memory_loop_trace code(map valuation(rev prefix++parameters)++tail))=
  flat_map(fun point=>map(fun instruction=>exact_cell(instruction_write instruction)
    (map point(coordinates++parameters))) instructions)(affine_scan_points nest valuation lower).
Proof.
  induction nest as [source|iterator bound expression body child IH];
    intros coordinates prefix parameters instructions valuation lower lower_code code tail COORDINATES UNIQUE LOWER VALUE.
  - cbn [affine_lower_nest] in LOWER; inversion LOWER; subst code.
    cbn [affine_nest_iterators] in COORDINATES; rewrite app_nil_r in COORDINATES; subst coordinates.
    cbn [affine_scan_points flat_map memory_loop_trace]; rewrite app_nil_r,map_app.
    rewrite map_app,map_rev,<-app_assoc.
    replace(length prefix) with(length(map valuation prefix)) by apply length_map.
    replace(length parameters) with(length(map valuation parameters)) by apply length_map.
    apply affine_leaf_trace_writes.
  - destruct(@affine_lower_nest_axis iterator bound expression body child prefix parameters lower_code
      (L.Seq(affine_leaf_sequence(length coordinates)(length parameters) instructions)) code LOWER)
      as [upper_code [child_code [UPPER [CHILD CODE]]]]; subst code.
    cbn [memory_loop_trace]; rewrite VALUE.
    assert (UPPER_VALUE : L.eval_expr(map valuation(rev prefix++parameters)++tail) upper_code=
      memory_source_affine_math valuation expression).
    { eapply affine_loop_expression_tail_value; exact UPPER. }
    rewrite UPPER_VALUE.
    rewrite memory_map_flat_map; cbn [affine_scan_points].
    rewrite memory_flat_map_associative; apply flat_map_ext; intro value.
    assert(FRESH:~In iterator(prefix++parameters)).
    { apply affine_scan_iterator_fresh with(rest:=affine_nest_iterators child).
      cbn [affine_nest_iterators] in COORDINATES; rewrite <-COORDINATES; exact UNIQUE. }
    replace(value::(map valuation(rev prefix++parameters)++tail)) with
      (map(memory_source_set_valuation valuation iterator value)(rev(prefix++[iterator])++parameters)++tail)
      by(apply affine_valuation_loop_environment; exact FRESH).
    apply IH with(prefix:=prefix++[iterator])(lower_code:=L.Constant 0); try assumption; try reflexivity.
    rewrite COORDINATES; cbn [affine_nest_iterators]; rewrite <-app_assoc; reflexivity.
Qed.

Theorem affine_scan_checked_writes nest coordinates prefix parameters operations valuation lower lower_code code tail
  bounds window_lower window_upper :
  coordinates=prefix++affine_nest_iterators nest -> NoDup(coordinates++parameters) ->
  affine_lower_nest nest prefix parameters lower_code
    (L.Seq(affine_leaf_sequence(length coordinates)(length parameters)(map memory_nary_compute_instruction operations)))=Some code ->
  L.eval_expr(map valuation(rev prefix++parameters)++tail) lower_code=lower ->
  Forall(window_compute_valid bounds window_lower window_upper(coordinates++parameters) []) operations ->
  map memory_event_write(memory_loop_trace code(map valuation(rev prefix++parameters)++tail))=
  flat_map(fun point=>map(fun operation=>affine_scan_access_cell point(memory_nary_compute_write operation)) operations)
    (affine_scan_points nest valuation lower).
Proof.
  intros COORDINATES UNIQUE LOWER VALUE VALID.
  rewrite (@affine_scan_source_writes nest coordinates prefix parameters
    (map memory_nary_compute_instruction operations) valuation lower lower_code code tail COORDINATES UNIQUE LOWER VALUE).
  apply flat_map_ext; intro point; rewrite map_map; apply map_ext_in; intros operation MEMBER.
  apply Forall_forall with(x:=operation) in VALID; [|exact MEMBER].
  destruct VALID as [WRITE REST].
  cbn [memory_nary_compute_instruction instruction_write].
  eapply affine_scan_access_exact; exact WRITE.
Qed.

Theorem affine_scan_checked_writes_apart nest coordinates prefix parameters operations valuation lower lower_code code tail
  bounds window_lower window_upper locations observation :
  coordinates=prefix++affine_nest_iterators nest -> NoDup(coordinates++parameters) ->
  affine_lower_nest nest prefix parameters lower_code
    (L.Seq(affine_leaf_sequence(length coordinates)(length parameters)(map memory_nary_compute_instruction operations)))=Some code ->
  L.eval_expr(map valuation(rev prefix++parameters)++tail) lower_code=lower ->
  Forall(window_compute_valid bounds window_lower window_upper(coordinates++parameters) []) operations ->
  (forall point, affine_scan_point nest valuation lower point -> forall operation, In operation operations ->
    forall write, locations(affine_scan_access_cell point(memory_nary_compute_write operation))=Some write ->
      location_disjoint write observation) ->
  memory_writes_apart_observation locations(memory_loop_trace code(map valuation(rev prefix++parameters)++tail)) observation.
Proof.
  intros COORDINATES UNIQUE LOWER VALUE VALID APART event EVENT write RESOLVE.
  assert (WRITE : In (memory_event_write event)
    (map memory_event_write(memory_loop_trace code(map valuation(rev prefix++parameters)++tail))))
    by(apply in_map; exact EVENT).
  rewrite (@affine_scan_checked_writes nest coordinates prefix parameters operations valuation lower lower_code code tail
    bounds window_lower window_upper COORDINATES UNIQUE LOWER VALUE VALID) in WRITE.
  apply in_flat_map in WRITE as [point [POINT WRITE]]; apply affine_scan_points_exact in POINT.
  apply in_map_iff in WRITE as [operation [SAME MEMBER]].
  rewrite <-SAME in RESOLVE; exact(APART point POINT operation MEMBER write RESOLVE).
Qed.

Print Assumptions affine_leaf_trace_writes.
Print Assumptions affine_scan_source_writes.
Print Assumptions affine_scan_checked_writes.
Print Assumptions affine_scan_checked_writes_apart.
