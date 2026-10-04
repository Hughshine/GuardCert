From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From polcert.lib Require Import Linalg.
From polcert.src Require Import PolyBase.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryMultiPointerCells
  GuardMemoryFootprintCapabilities GuardMemoryFiniteAliasCondition GuardMemoryNaryAffineExpressions GuardMemoryBooleanRectangle
  GuardMemoryAffineAxisPairScan GuardMemoryParamAxisPairScan GuardMemoryAxisBoundaryMath GuardMemoryAxisBoundaryCells.
From GuardMemory Require Import GuardMemoryParamBoundaryMath.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_param_rectangle_active_ext (first second : list Z -> bool) counts :
  Forall (fun count => 0 <= count) counts ->
  (forall coordinates, Forall2 (fun index count => 0 <= index < count) coordinates counts -> first coordinates = second coordinates) ->
  memory_boolean_rectangle_result first counts [] = memory_boolean_rectangle_result second counts [].
Proof.
  intros COUNTS POINTS; apply Bool.eq_true_iff_eq.
  rewrite !memory_boolean_rectangle_member by exact COUNTS; cbn; split; intros CHECK point RANGE.
  - rewrite <-POINTS by exact RANGE; apply CHECK; exact RANGE.
  - rewrite POINTS by exact RANGE; apply CHECK; exact RANGE.
Qed.
Lemma memory_param_axis_full_specialize locations counts parameters first second first_term second_term :
  Forall (fun count => 0 <= count) counts ->
  memory_param_affine_axis_pair_check locations counts parameters first second first_term second_term =
    memory_affine_axis_pair_check locations counts first second
      (memory_param_boundary_specialize (length counts) first_term parameters)
      (memory_param_boundary_specialize (length counts) second_term parameters).
Proof.
  intro COUNTS; unfold memory_param_affine_axis_pair_check,memory_affine_axis_pair_check.
  apply memory_param_rectangle_active_ext; [exact COUNTS|].
  intros left LEFT; apply memory_param_rectangle_active_ext; [exact COUNTS|].
  intros right RIGHT; rewrite (@memory_param_boundary_specialize_value (length counts) first_term parameters left (Forall2_length LEFT)),
    (@memory_param_boundary_specialize_value (length counts) second_term parameters right (Forall2_length RIGHT)).
  reflexivity.
Qed.

Definition memory_param_affine_axis_boundary_pair_check locations counts parameters first second first_term second_term :=
  forallb (fun mask => memory_boolean_rectangle_result (fun coordinates =>
    memory_cell_pair_address_check locations
      (point_cell first (memory_nary_index_value first_term (memory_axis_boundary_pick mask coordinates++parameters)))
      (point_cell second (memory_nary_index_value second_term (memory_axis_boundary_pick (map negb mask) coordinates++parameters))))
    counts []) (memory_axis_boundary_masks (length counts)).
Lemma memory_param_axis_boundary_specialize locations counts parameters first second first_term second_term :
  Forall (fun count => 0 <= count) counts ->
  memory_param_affine_axis_boundary_pair_check locations counts parameters first second first_term second_term =
    memory_affine_axis_boundary_pair_check locations counts first second
      (memory_param_boundary_specialize (length counts) first_term parameters)
      (memory_param_boundary_specialize (length counts) second_term parameters).
Proof.
  intro COUNTS; unfold memory_param_affine_axis_boundary_pair_check,memory_affine_axis_boundary_pair_check.
  apply Bool.eq_true_iff_eq; rewrite !forallb_forall; split; intros CHECK mask MEMBER;
    specialize (CHECK mask MEMBER); apply memory_axis_boundary_mask_member in MEMBER;
    rewrite memory_boolean_rectangle_member in * by exact COUNTS;
    intros point RANGE; specialize (CHECK point RANGE); cbn in *.
  all: assert (LEFT : Forall2 (fun index count => 0 <= index < count) (memory_axis_boundary_pick mask point) counts)
    by (apply memory_axis_boundary_pick_range; assumption).
  all: assert (RIGHT : Forall2 (fun index count => 0 <= index < count) (memory_axis_boundary_pick (map negb mask) point) counts)
    by (apply memory_axis_boundary_pick_range; [exact RANGE|rewrite length_map; exact MEMBER]).
  all: rewrite (@memory_param_boundary_specialize_value (length counts) first_term parameters
    (memory_axis_boundary_pick mask point) (Forall2_length LEFT)),
    (@memory_param_boundary_specialize_value (length counts) second_term parameters
      (memory_axis_boundary_pick (map negb mask) point) (Forall2_length RIGHT)) in *; exact CHECK.
Qed.
Theorem memory_param_axis_boundary_pair_exact temps extent memory counts parameters first second first_term second_term :
  first <> second -> resize (length counts) (fst first_term) = resize (length counts) (fst second_term) ->
  Forall (fun count => 0 <= count) counts ->
  (forall coordinates, Forall2 (fun index count => 0 <= index < count) coordinates counts ->
    memory_cell_capable (memory_multi_pointer_locations temps extent) memory
      (point_cell first (memory_nary_index_value first_term (coordinates++parameters))) /\
    memory_cell_capable (memory_multi_pointer_locations temps extent) memory
      (point_cell second (memory_nary_index_value second_term (coordinates++parameters)))) ->
  memory_param_affine_axis_boundary_pair_check (memory_multi_pointer_locations temps extent)
    counts parameters first second first_term second_term =
  memory_param_affine_axis_pair_check (memory_multi_pointer_locations temps extent)
    counts parameters first second first_term second_term.
Proof.
  intros DISTINCT COEFFICIENTS COUNTS CAPABILITIES.
  rewrite memory_param_axis_boundary_specialize,memory_param_axis_full_specialize by exact COUNTS.
  apply memory_affine_axis_boundary_pair_exact with (memory := memory); [exact DISTINCT|exact COEFFICIENTS|exact COUNTS|].
  intros coordinates RANGE; specialize (CAPABILITIES coordinates RANGE).
  rewrite (@memory_param_boundary_specialize_value (length counts) first_term parameters coordinates (Forall2_length RANGE)),
    (@memory_param_boundary_specialize_value (length counts) second_term parameters coordinates (Forall2_length RANGE)) in CAPABILITIES.
  exact CAPABILITIES.
Qed.
Print Assumptions memory_param_axis_full_specialize.
Print Assumptions memory_param_axis_boundary_specialize.
Print Assumptions memory_param_axis_boundary_pair_exact.
