From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From polcert.src Require Import PolyBase.
From Guard Require Import CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryFiniteFootprint GuardMemoryFiniteAliasCondition
  GuardMemoryFootprintCapabilities GuardMemoryCrossPointerSeparation GuardMemoryNaryAffineAccess GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestScanModel AffineNestScanPoints AffineNestScanAccesses AffineNestScanPair.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition affine_scan_cells nest valuation lower accesses :=
  flat_map(fun point=>map(affine_scan_access_cell point) accesses)(affine_scan_points nest valuation lower).
Definition affine_scan_access_pair_result nest valuation lower locations first second :=
  if Pos.eqb(memory_nary_access_array first)(memory_nary_access_array second) then true else
    affine_scan_pair_result nest valuation lower locations(memory_nary_access_array first)(memory_nary_access_array second)
      (memory_nary_access_expression first)(memory_nary_access_expression second).
Definition affine_scan_separation_result nest valuation lower locations accesses :=
  forallb(fun first=>forallb(affine_scan_access_pair_result nest valuation lower locations first) accesses) accesses.

Lemma affine_scan_capable_pair_separated locations memory first second first_location second_location :
  memory_cell_capable locations memory first -> memory_cell_capable locations memory second -> first<>second ->
  locations first=Some first_location -> locations second=Some second_location ->
  memory_cell_pair_address_check locations first second=true -> location_disjoint first_location second_location.
Proof.
  intros [left [LEFT [LCHUNK [LVALID LALIGN]]]] [right [RIGHT [RCHUNK [RVALID RALIGN]]]] DISTINCT FIRST SECOND CHECK.
  assert(left=first_location) by congruence; subst left.
  assert(right=second_location) by congruence; subst right.
  unfold memory_cell_pair_address_check in CHECK; destruct memory_cell_identity_dec; [contradiction|].
  rewrite FIRST,SECOND in CHECK.
  apply negb_true_iff in CHECK; apply andb_false_iff in CHECK as [BLOCKS|ADDRESSES].
  - apply Pos.eqb_neq in BLOCKS; unfold location_disjoint; auto.
  - apply Z.eqb_neq in ADDRESSES; unfold location_disjoint; rewrite LCHUNK,RCHUNK; cbn [size_chunk].
    destruct LALIGN as [left_units LEFT_UNITS]; destruct RALIGN as [right_units RIGHT_UNITS].
    right; rewrite LEFT_UNITS,RIGHT_UNITS in *; lia.
Qed.
Print Assumptions affine_scan_capable_pair_separated.

Theorem affine_scan_separation_sound nest valuation lower locations memory accesses :
  (forall point, affine_scan_point nest valuation lower point ->
    Forall(memory_cell_capable locations memory)(map(affine_scan_access_cell point) accesses)) ->
  affine_scan_separation_result nest valuation lower locations accesses=true ->
  memory_cross_pointer_separated_on(memory_footprint_allowed(affine_scan_cells nest valuation lower accesses)) locations.
Proof.
  intros CAPABLE CHECK first second first_location second_location FIRST_ALLOWED SECOND_ALLOWED DISTINCT FIRST SECOND.
  apply memory_footprint_allowed_exact in FIRST_ALLOWED,SECOND_ALLOWED.
  unfold affine_scan_cells in FIRST_ALLOWED,SECOND_ALLOWED.
  apply in_flat_map in FIRST_ALLOWED as [first_point [FIRST_POINT FIRST_ACCESS]].
  apply in_flat_map in SECOND_ALLOWED as [second_point [SECOND_POINT SECOND_ACCESS]].
  apply affine_scan_points_exact in FIRST_POINT,SECOND_POINT.
  apply in_map_iff in FIRST_ACCESS as [first_access [FIRST_CELL FIRST_ACCESS]].
  apply in_map_iff in SECOND_ACCESS as [second_access [SECOND_CELL SECOND_ACCESS]].
  subst first second.
  unfold affine_scan_separation_result in CHECK.
  apply forallb_forall with(x:=first_access) in CHECK; [|exact FIRST_ACCESS].
  apply forallb_forall with(x:=second_access) in CHECK; [|exact SECOND_ACCESS].
  unfold affine_scan_access_pair_result in CHECK.
  cbn [affine_scan_access_cell point_cell arr_id] in DISTINCT.
  assert(DIFFERENT:Pos.eqb(memory_nary_access_array first_access)(memory_nary_access_array second_access)=false)
    by(apply Pos.eqb_neq; exact DISTINCT).
  rewrite DIFFERENT in CHECK; unfold affine_scan_pair_result in CHECK.
  pose proof(proj1(@affine_scan_result_points nest valuation lower _) CHECK first_point FIRST_POINT) as FIRST_CHECK.
  pose proof(proj1(@affine_scan_result_points nest valuation lower _) FIRST_CHECK second_point SECOND_POINT) as PAIR_CHECK.
  eapply affine_scan_capable_pair_separated; [| | |exact FIRST|exact SECOND|exact PAIR_CHECK].
  - pose proof(CAPABLE first_point FIRST_POINT) as FIRST_CAPABLE.
    apply Forall_forall with(x:=affine_scan_access_cell first_point first_access) in FIRST_CAPABLE.
    + exact FIRST_CAPABLE.
    + apply in_map; exact FIRST_ACCESS.
  - pose proof(CAPABLE second_point SECOND_POINT) as SECOND_CAPABLE.
    apply Forall_forall with(x:=affine_scan_access_cell second_point second_access) in SECOND_CAPABLE.
    + exact SECOND_CAPABLE.
    + apply in_map; exact SECOND_ACCESS.
  - intro SAME; apply(f_equal arr_id) in SAME; contradiction.
Qed.
Print Assumptions affine_scan_separation_sound.
