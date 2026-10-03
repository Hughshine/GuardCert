From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightNoWrap ClightCountedLoop ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryRectangularFootprint GuardMemoryCoordinateActivation
  GuardMemoryActivatedAliasCondition.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_rectangular_activated_item bounds coordinates cell :=
  MemoryActivatedCell cell (memory_coordinate_activation_tree bounds coordinates) coordinates.
Definition memory_rectangular_activated_items cap bounds instructions :=
  flat_map (fun coordinates => map (memory_rectangular_activated_item bounds coordinates)
    (memory_point_footprint instructions coordinates))
    (memory_rectangular_points (repeat cap (length bounds)) []).
Definition memory_rectangular_item_active bounds s item :=
  memory_coordinate_activation_flag bounds (activated_coordinates item) s.
Definition memory_rectangular_counts bounds s := map (fun bound => Int.signed (temp_word bound (entry_temps s))) bounds.

Lemma memory_forall2_map_right {A B C} (R : A -> C -> Prop) (f : B -> C) xs ys :
  Forall2 R xs (map f ys) <-> Forall2 (fun x y => R x (f y)) xs ys.
Proof.
  revert xs; induction ys; intros [|x xs]; cbn; split; intro RUN; inversion RUN; subst;
    constructor; auto; apply IHys; assumption.
Qed.
Lemma memory_rectangular_coordinate_bounds cap count coordinates :
  Forall2 (fun coordinate upper => 0 <= coordinate < upper) coordinates (repeat cap count) ->
  Forall (fun coordinate => 0 <= coordinate < cap) coordinates.
Proof.
  revert coordinates; induction count; intros coordinates RANGE; cbn in RANGE; inversion RANGE; subst; constructor;
    [assumption|eapply IHcount; eassumption].
Qed.
Lemma memory_rectangular_coordinate_signed cap count coordinates :
  signed_range cap ->
  In coordinates (memory_rectangular_points (repeat cap count) []) -> Forall signed_range coordinates.
Proof.
  intros CAP POINT; apply memory_rectangular_points_origin in POINT.
  apply memory_rectangular_coordinate_bounds in POINT; eapply Forall_impl; [|exact POINT].
  intros coordinate RANGE; unfold signed_range in *; change Int.min_signed with (-2147483648) in *; lia.
Qed.
Lemma memory_rectangular_activation_ranges cap bounds coordinates s :
  signed_range cap -> In coordinates (memory_rectangular_points (repeat cap (length bounds)) []) ->
  (memory_coordinate_activation_flag bounds coordinates s = true <->
    In coordinates (memory_rectangular_points (memory_rectangular_counts bounds s) [])).
Proof.
  intros CAP POINT; rewrite memory_coordinate_activation_semantics by
    (eapply memory_rectangular_coordinate_signed; eassumption).
  rewrite memory_rectangular_points_origin; unfold memory_rectangular_counts; rewrite memory_forall2_map_right.
  apply memory_rectangular_points_origin in POINT; apply memory_rectangular_coordinate_bounds in POINT.
  split; intro UPPERS.
  - revert POINT; induction UPPERS; intro NONNEGATIVE; [constructor|].
    inversion NONNEGATIVE; subst; constructor; [lia|apply IHUPPERS; assumption].
  - eapply Forall2_impl; [|exact UPPERS]; intros coordinate bound RANGE.
    exact (proj2 RANGE).
Qed.
Lemma memory_rectangular_points_monotone small large coordinates :
  Forall2 Z.le small large -> In coordinates (memory_rectangular_points small []) ->
  In coordinates (memory_rectangular_points large []).
Proof.
  intros LIMITS POINT; apply memory_rectangular_points_origin in POINT; apply memory_rectangular_points_origin.
  revert coordinates POINT; induction LIMITS; intros coordinates POINT; inversion POINT; subst; constructor;
    [lia|apply IHLIMITS; assumption].
Qed.
Lemma memory_rectangular_repeat_limits cap counts :
  Forall (fun count => count <= cap) counts -> Forall2 Z.le counts (repeat cap (length counts)).
Proof. intro COUNTS; induction COUNTS; cbn; constructor; assumption. Qed.
Lemma memory_rectangular_items_member cap bounds instructions item :
  In item (memory_rectangular_activated_items cap bounds instructions) <->
  exists coordinates cell,
    In coordinates (memory_rectangular_points (repeat cap (length bounds)) []) /\
    In cell (memory_point_footprint instructions coordinates) /\
    item = memory_rectangular_activated_item bounds coordinates cell.
Proof.
  unfold memory_rectangular_activated_items; rewrite in_flat_map; split.
  - intros [coordinates [POINT MEMBER]]; apply in_map_iff in MEMBER as [cell [SAME MEMBER]].
    exists coordinates,cell; auto.
  - intros [coordinates [cell [POINT [CELL SAME]]]]; subst item; exists coordinates;
      split; [exact POINT|apply in_map; exact CELL].
Qed.
Theorem memory_rectangular_selected_members cap bounds instructions s cell :
  signed_range cap -> Forall (fun bound => Int.signed (temp_word bound (entry_temps s)) <= cap) bounds ->
  (In cell (memory_selected_cells (memory_rectangular_item_active bounds s)
    (memory_rectangular_activated_items cap bounds instructions)) <->
   In cell (flat_map (memory_point_footprint instructions)
     (memory_rectangular_points (memory_rectangular_counts bounds s) []))).
Proof.
  intros CAP COUNTS; unfold memory_selected_cells; rewrite in_map_iff; split.
  - intros [item [SAME MEMBER]]; apply filter_In in MEMBER as [MEMBER ACTIVE].
    apply memory_rectangular_items_member in MEMBER as [coordinates [point_cell [POINT [CELL ITEM]]]]; subst item.
    cbn [activated_cell] in SAME; subst cell.
    unfold memory_rectangular_item_active in ACTIVE; cbn [activated_coordinates] in ACTIVE.
    apply in_flat_map; exists coordinates; split; [|exact CELL].
    apply (proj1 (@memory_rectangular_activation_ranges cap bounds coordinates s CAP POINT)); exact ACTIVE.
  - intro MEMBER; apply in_flat_map in MEMBER as [coordinates [POINT CELL]].
    assert (LIMITS : Forall2 Z.le (memory_rectangular_counts bounds s) (repeat cap (length bounds))).
    { unfold memory_rectangular_counts; replace (length bounds) with (length (map (fun bound => Int.signed (temp_word bound (entry_temps s))) bounds))
        by (rewrite length_map; reflexivity).
      apply memory_rectangular_repeat_limits,Forall_map; exact COUNTS. }
    assert (POTENTIAL : In coordinates (memory_rectangular_points (repeat cap (length bounds)) []))
      by (eapply memory_rectangular_points_monotone; eassumption).
    exists (memory_rectangular_activated_item bounds coordinates cell); split; [reflexivity|].
    apply filter_In; split.
    + apply memory_rectangular_items_member; exists coordinates,cell; auto.
    + unfold memory_rectangular_item_active; cbn [activated_coordinates].
      apply (proj2 (@memory_rectangular_activation_ranges cap bounds coordinates s CAP POTENTIAL)); exact POINT.
Qed.
Print Assumptions memory_rectangular_activation_ranges.
Print Assumptions memory_rectangular_selected_members.
