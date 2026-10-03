From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import AbstractGuard SemanticFacts ClightCondition ClightPureExpr ClightRedundantSet ClightRectangularGuard ClightNoWrap.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryScalarLoops
  GuardMemoryRecursiveSource GuardMemoryRecursiveGuard GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerDomain
  GuardMemoryMultiPointerCells GuardMemoryMultiPointerFootprint GuardMemoryActivatedAliasCondition
  GuardMemoryActivatedRectangle GuardMemoryCoordinateActivation GuardMemoryRectangularFootprint
  GuardMemoryFiniteAliasCondition GuardMemoryFootprintRestriction GuardMemoryFootprintCapabilities GuardMemoryFiniteFootprint
  GuardMemoryLoopTrace GuardMemoryTripleGuard GuardMemoryRegistryGuard.
Import ListNotations.
Set Implicit Arguments.

Definition memory_multi_pointer_region_active source (package : memory_multi_pointer_region_package source) s :=
  memory_rectangular_item_active (memory_nest_bounds (multi_pointer_region_nest package)) s.
Definition memory_multi_pointer_region_alias_tree source (package : memory_multi_pointer_region_package source) :=
  memory_activated_alias_tree memory_multi_pointer_cell_code (memory_multi_pointer_region_items package).
Definition memory_multi_pointer_region_alias_check source (package : memory_multi_pointer_region_package source) s :=
  memory_activated_alias_check (memory_multi_pointer_locations (entry_temps s) (multi_pointer_region_window package))
    (memory_multi_pointer_region_active package s) (memory_multi_pointer_region_items package).
Definition memory_multi_pointer_region_guard_tree source (package : memory_multi_pointer_region_package source) :=
  decision_bind (memory_recursive_guard_tree (multi_pointer_region_limit package) [] (multi_pointer_region_nest package))
    (memory_multi_pointer_region_alias_tree package) (Decision false).
Definition memory_multi_pointer_region_guard_accept source (package : memory_multi_pointer_region_package source) s :=
  memory_recursive_guard_accept (multi_pointer_region_limit package) [] (multi_pointer_region_nest package) s &&
    memory_multi_pointer_region_alias_check package s.
Definition memory_multi_pointer_region_guard_domain source (package : memory_multi_pointer_region_package source) s :=
  memory_recursive_guard_domain (multi_pointer_region_limit package) [] (multi_pointer_region_nest package) s /\
  (memory_recursive_guard_accept (multi_pointer_region_limit package) [] (multi_pointer_region_nest package) s = true ->
   Forall (memory_activated_item_domain memory_multi_pointer_cell_code
     (memory_multi_pointer_locations (entry_temps s) (multi_pointer_region_window package)) s
     (memory_multi_pointer_region_active package s)) (memory_multi_pointer_region_items package)).

Theorem memory_multi_pointer_region_source_guard_domain source (package : memory_multi_pointer_region_package source)
  fe ge locals temps memory after final :
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  memory_multi_pointer_region_guard_domain package (Entry ge locals temps memory).
Proof.
  intro SOURCE.
  pose proof (@memory_multi_pointer_region_source_domain source package fe ge locals temps memory after final SOURCE) as DOMAIN.
  split; [exact DOMAIN|]; intro ACCEPT.
  destruct (@memory_recursive_guard_sound (multi_pointer_region_limit package) [] (multi_pointer_region_nest package)
    (Entry ge locals temps memory) (proj2 (multi_pointer_region_cap (multi_pointer_region_syntax package))) DOMAIN ACCEPT)
    as [INITIAL [RANGES ALIAS]].
  destruct (@memory_multi_pointer_source_under_ranges source package fe ge locals temps memory after final INITIAL RANGES SOURCE)
    as [SCALARS [LOOP EXIT]].
  pose proof (@memory_loop_source_capabilities _ _
    (RuntimeState (memory_multi_pointer_locations temps (multi_pointer_region_window package)) memory)
    (RuntimeState (memory_multi_pointer_locations temps (multi_pointer_region_window package)) final)
    (memory_multi_pointer_locations_int32 temps (multi_pointer_region_window package)) LOOP) as CAPABILITIES.
  apply Forall_forall; intros item MEMBER.
  assert (ITEM : In item (memory_multi_pointer_region_items package)) by exact MEMBER.
  unfold memory_multi_pointer_region_items in MEMBER.
  apply memory_rectangular_items_member in MEMBER as [coordinates [cell [POINT [CELL SAME]]]]; subst item.
  split.
  - unfold memory_activation_exact,memory_multi_pointer_region_active,memory_rectangular_item_active.
    cbn [activated_test activated_coordinates]; apply memory_coordinate_activation_exact.
    eapply Forall_impl; [|exact RANGES]; intros bound RANGE; exact (proj1 RANGE).
  - intro ACTIVE.
    assert (SELECTED : In cell (memory_selected_cells (memory_multi_pointer_region_active package (Entry ge locals temps memory))
      (memory_multi_pointer_region_items package))).
    { unfold memory_selected_cells; apply in_map_iff;
      exists (memory_rectangular_activated_item (memory_nest_bounds (multi_pointer_region_nest package)) coordinates cell);
      split; [reflexivity|].
      apply filter_In; split; [exact ITEM|exact ACTIVE]. }
    change (In cell (memory_selected_cells
      (memory_rectangular_item_active (memory_nest_bounds (multi_pointer_region_nest package)) (Entry ge locals temps memory))
      (memory_multi_pointer_region_items package))) in SELECTED.
    apply (proj1 (@memory_multi_pointer_selected_footprint source package ge locals temps memory cell RANGES)) in SELECTED.
    unfold memory_events_footprint in SELECTED; apply in_flat_map in SELECTED as [event [EVENT ACCESS]].
    apply Forall_forall with (x := event) in CAPABILITIES; [|exact EVENT].
    change (In cell (memory_event_cells event)) in ACCESS.
    apply Forall_forall with (x := cell) in CAPABILITIES; [|exact ACCESS].
    cbn [activated_cell]; apply memory_multi_pointer_cell_encoding;
      [exact (proj1 (proj2 (multi_pointer_region_extent (multi_pointer_region_syntax package))))|exact CAPABILITIES].
Qed.
Theorem memory_multi_pointer_region_guard_exact source (package : memory_multi_pointer_region_package source) s :
  memory_multi_pointer_region_guard_domain package s -> forall flag,
  decision_run s (memory_multi_pointer_region_guard_tree package) flag <->
    flag = memory_multi_pointer_region_guard_accept package s.
Proof.
  intros [DOMAIN ITEMS] flag; unfold memory_multi_pointer_region_guard_tree,memory_multi_pointer_region_guard_accept.
  apply memory_guard_gate_exact.
  - apply memory_recursive_guard_exact; exact DOMAIN.
  - intro ACCEPT; unfold memory_multi_pointer_region_alias_tree,memory_multi_pointer_region_alias_check.
    apply memory_activated_alias_exact; apply ITEMS; exact ACCEPT.
Qed.
Theorem memory_multi_pointer_region_guard_nonalias source (package : memory_multi_pointer_region_package source) s :
  memory_multi_pointer_region_guard_domain package s -> memory_multi_pointer_region_guard_accept package s = true ->
  locations_nonalias (memory_restrict_locations (memory_footprint_allowed
    (memory_selected_cells (memory_multi_pointer_region_active package s) (memory_multi_pointer_region_items package)))
    (memory_multi_pointer_locations (entry_temps s) (multi_pointer_region_window package))).
Proof.
  intros [DOMAIN ITEMS] ACCEPT; unfold memory_multi_pointer_region_guard_accept in ACCEPT;
    apply andb_true_iff in ACCEPT as [COUNTS ALIAS].
  eapply memory_activated_alias_condition_sound; [apply ITEMS; exact COUNTS|].
  apply (proj2 (@memory_activated_alias_exact memory_multi_pointer_cell_code
    (memory_multi_pointer_locations (entry_temps s) (multi_pointer_region_window package)) s
    (memory_multi_pointer_region_active package s) (memory_multi_pointer_region_items package) (ITEMS COUNTS) true)).
  unfold memory_multi_pointer_region_alias_check in ALIAS; symmetry; exact ALIAS.
Qed.
Definition memory_multi_pointer_region_guard_dimension source (package : memory_multi_pointer_region_package source) :=
  @positive_dimension clight_entry unit (memory_multi_pointer_region_guard_domain package)
    (fun _ s => memory_multi_pointer_region_guard_accept package s = true)
    (fun _ => memory_multi_pointer_region_guard_accept package) (fun _ s _ ACCEPT => ACCEPT).
Definition memory_multi_pointer_region_guard_primitives source (package : memory_multi_pointer_region_package source) :
  check_primitives decision_test_language (memory_multi_pointer_region_guard_domain package)
    (decide_atom (memory_multi_pointer_region_guard_dimension package)).
Proof.
  refine (@CheckPrimitives clight_entry unit decision_test_language (memory_multi_pointer_region_guard_domain package)
    (decide_atom (memory_multi_pointer_region_guard_dimension package))
    (fun _ => memory_multi_pointer_region_guard_tree package) (fun _ => Decision true) _ _).
  - intros [] s flag DOMAIN.
    change (decision_run s (memory_multi_pointer_region_guard_tree package) flag <->
      flag = checked_valid (decide_atom (memory_multi_pointer_region_guard_dimension package) tt s)).
    rewrite memory_multi_pointer_region_guard_exact by exact DOMAIN.
    cbn [memory_multi_pointer_region_guard_dimension positive_dimension decide_atom];
      destruct (memory_multi_pointer_region_guard_accept package s); reflexivity.
  - intros [] s flag expected DOMAIN ACCEPT.
    change (decision_run s (Decision true) flag <-> flag = expected).
    cbn [memory_multi_pointer_region_guard_dimension positive_dimension decide_atom] in ACCEPT.
    destruct (memory_multi_pointer_region_guard_accept package s); try discriminate;
      inversion ACCEPT; subst; split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
Defined.
Print Assumptions memory_multi_pointer_region_source_guard_domain.
Print Assumptions memory_multi_pointer_region_guard_exact.
Print Assumptions memory_multi_pointer_region_guard_nonalias.
Print Assumptions memory_multi_pointer_region_guard_primitives.
