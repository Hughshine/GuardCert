From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryWindowCells.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestLoopEncoding
  AffineNestValuation AffineNestMathDomain AffineNestSourceDecode AffineNestLeafModel AffineNestLeafDecode.
Import ListNotations.
Set Implicit Arguments.

Definition affine_checked_nest_loop nest geometry scalars operations lower :=
  affine_lower_nest nest [] (geometry++scalars) lower
    (affine_checked_leaf_code (affine_nest_iterators nest) geometry scalars operations).

(** No source/IR correspondence is postulated here: the checked leaf and the
    checked complete source shape discharge every recursive adapter premise.
    The integer domain still requires a proved runtime encoder before this
    theorem can be used as an actual guarded compiler pass. *)
Theorem affine_checked_nest_source_decode nest bounds window_lower window_upper geometry scalars pointers operations
  (certificate:affine_leaf_certificate (affine_nest_leaf nest) bounds window_lower window_upper
    (affine_nest_iterators nest++geometry) scalars pointers operations)
  fe ge locals initial valuation lower lower_code code temps memory after final tail :
  affine_nest_shapes nest -> NoDup(affine_nest_controls nest) ->
  affine_nest_bound_dependencies [] (geometry++scalars) nest ->
  (forall identifier, In identifier ((geometry++scalars)++pointers) -> ~In identifier(affine_nest_mutated nest)) ->
  affine_math_domain bounds (affine_nest_iterators nest++geometry) nest valuation lower ->
  affine_word_view (geometry++scalars) valuation temps -> temp_agree pointers initial temps ->
  affine_nest_entry nest valuation lower temps ->
  affine_checked_nest_loop nest geometry scalars operations lower_code=Some code ->
  L.eval_expr (map valuation(geometry++scalars)++tail) lower_code=lower ->
  exec_stmt fe ge locals temps memory (affine_nest_source nest) E0 after final Out_normal ->
  L.loop_semantics code (map valuation(geometry++scalars)++tail)
    (RuntimeState(window_multi_pointer_locations initial window_lower window_upper) memory)
    (RuntimeState(window_multi_pointer_locations initial window_lower window_upper) final).
Proof.
  intros SHAPES FRESH DEPENDENCIES PROTECTED DOMAIN WORDS POINTERS ENTRY LOWER VALUE SOURCE.
  unfold affine_checked_nest_loop in LOWER.
  eapply affine_nest_source_decode with
    (pointers:=pointers) (original:=initial) (bounds:=bounds)
    (layout:=affine_nest_iterators nest++geometry) (coordinates:=affine_nest_iterators nest)
    (source_leaf:=affine_nest_leaf nest)
    (target_leaf:=affine_checked_leaf_code (affine_nest_iterators nest) geometry scalars operations)
    (prefix:=[]) (parameters:=geometry++scalars) (valuation:=valuation) (lower:=lower)
    (lower_code:=lower_code); try eassumption; try reflexivity.
  - eapply affine_leaf_normal; exact certificate.
  - eapply affine_leaf_quiet; exact certificate.
  - eapply affine_leaf_writes; exact certificate.
  - intros prefix point_valuation point_temps first point_after last COORDINATES POINT_WORDS POINT_POINTERS RANGES LEAF.
    subst prefix; eapply affine_checked_leaf_decode; eassumption.
Qed.
Print Assumptions affine_checked_nest_loop.
Print Assumptions affine_checked_nest_source_decode.
