From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightNoWrap ClightCountedLoop ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryLoopTrace GuardMemoryNaryCompute
  GuardMemoryNaryAffineAccess GuardMemoryNaryAccessCheck GuardMemoryScalarAccess GuardMemoryInstructionPadding
  GuardMemoryMultiPointerCompute GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerCells GuardMemoryMultiPointerDomain
  GuardMemoryRecursiveSource GuardMemoryRecursiveSyntax GuardMemoryRecursiveDomain GuardMemoryRectangularFootprint GuardMemoryScalarLoops
  GuardMemoryActivatedRectangle GuardMemoryActivatedAliasCondition GuardMemoryFootprintCapabilities GuardMemoryFiniteFootprint.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_multi_pointer_operation_footprint_prefix limits layout scalars extent operation coordinates values :
  memory_multi_pointer_compute_valid limits layout scalars extent operation -> length coordinates = length layout ->
  memory_instruction_footprint (memory_nary_compute_instruction operation) (coordinates++values) =
    memory_instruction_footprint (memory_nary_compute_instruction operation) coordinates.
Proof.
  intros [[WRITE WEXTENT] [READS REST]] LENGTH.
  unfold memory_instruction_footprint; cbn [memory_nary_compute_instruction instruction_write instruction_reads].
  rewrite map_map,map_map.
  rewrite (@memory_scalar_access_cell layout (memory_nary_compute_write operation) coordinates values (proj1 (proj2 WRITE)) LENGTH).
  f_equal; apply map_ext_in; intros access MEMBER.
  apply Forall_forall with (x := access) in READS; [|exact MEMBER].
  apply memory_scalar_access_cell with (layout := layout); [exact (proj1 (proj2 (proj1 READS)))|exact LENGTH].
Qed.
Lemma memory_pad_instruction_footprint extra instruction values :
  memory_instruction_footprint (memory_pad_instruction extra instruction) values = memory_instruction_footprint instruction values.
Proof.
  unfold memory_instruction_footprint; cbn [memory_pad_instruction instruction_write instruction_reads].
  rewrite memory_pad_access_cell,map_map; f_equal; apply map_ext; intros access; apply memory_pad_access_cell.
Qed.
Lemma memory_multi_pointer_point_footprint_prefix limits layout scalars extent operations coordinates values :
  Forall (memory_multi_pointer_compute_valid limits layout scalars extent) operations -> length coordinates = length layout ->
  memory_point_footprint (memory_pad_instructions (length scalars) (map memory_nary_compute_instruction operations)) (coordinates++values) =
    memory_point_footprint (memory_pad_instructions (length scalars) (map memory_nary_compute_instruction operations)) coordinates.
Proof.
  intros CERT LENGTH; induction CERT as [|operation operations HEAD CERT IH]; cbn [memory_point_footprint memory_pad_instructions map flat_map]; [reflexivity|].
  rewrite !memory_pad_instruction_footprint.
  rewrite (@memory_multi_pointer_operation_footprint_prefix limits layout scalars extent operation coordinates values HEAD LENGTH).
  f_equal; exact IH.
Qed.
Lemma memory_flat_map_ext_in {A B} (first second : A -> list B) items :
  (forall item, In item items -> first item = second item) -> flat_map first items = flat_map second items.
Proof.
  intro SAME; induction items; cbn; [reflexivity|].
  rewrite SAME by (cbn; auto); rewrite IHitems; [reflexivity|intros; apply SAME; cbn; auto].
Qed.
Theorem memory_multi_pointer_source_footprint source (package : memory_multi_pointer_region_package source) counts values :
  length counts = length (memory_nest_iterators (multi_pointer_region_nest package)) ->
  memory_events_footprint (memory_loop_trace
    (memory_scalar_rectangle 0 (length counts) (length values) (memory_multi_pointer_region_instructions package))
    (counts++values)) = flat_map (memory_point_footprint (memory_multi_pointer_region_instructions package))
      (memory_rectangular_points counts []).
Proof.
  intro LENGTH; pose proof (@memory_scalar_rectangle_footprint counts (memory_multi_pointer_region_instructions package) values [] [] eq_refl) as FOOTPRINT.
  cbn [length rev app] in FOOTPRINT; rewrite FOOTPRINT.
  apply memory_flat_map_ext_in; intros coordinates POINT.
  apply memory_rectangular_points_origin in POINT; apply Forall2_length in POINT.
  unfold memory_multi_pointer_region_instructions.
  apply memory_multi_pointer_point_footprint_prefix with
    (limits := memory_recursive_limits (multi_pointer_region_nest package) (multi_pointer_region_limit package))
    (layout := memory_nest_iterators (multi_pointer_region_nest package)) (extent := multi_pointer_region_window package).
  - exact (multi_pointer_region_operations (multi_pointer_region_syntax package)).
  - lia.
Qed.
Definition memory_multi_pointer_region_items source (package : memory_multi_pointer_region_package source) :=
  memory_rectangular_activated_items (multi_pointer_region_limit package)
    (memory_nest_bounds (multi_pointer_region_nest package)) (memory_multi_pointer_region_instructions package).
Theorem memory_multi_pointer_selected_footprint source (package : memory_multi_pointer_region_package source) ge locals temps memory cell :
  Forall (fun bound => register_range bound (multi_pointer_region_limit package) (Entry ge locals temps memory))
    (memory_nest_bounds (multi_pointer_region_nest package)) ->
  (In cell (memory_selected_cells
    (memory_rectangular_item_active (memory_nest_bounds (multi_pointer_region_nest package)) (Entry ge locals temps memory))
    (memory_multi_pointer_region_items package)) <->
   In cell (memory_events_footprint (memory_loop_trace
     (memory_scalar_rectangle 0 (length (memory_nest_iterators (multi_pointer_region_nest package)))
       (length (multi_pointer_region_scalars package)) (memory_multi_pointer_region_instructions package))
     (memory_recursive_parameters (memory_nest_bounds (multi_pointer_region_nest package)) temps++
       memory_recursive_parameters (multi_pointer_region_scalars package) temps)))).
Proof.
  intro RANGES; unfold memory_multi_pointer_region_items.
  rewrite memory_rectangular_selected_members.
  - replace (length (memory_nest_iterators (multi_pointer_region_nest package))) with
      (length (memory_recursive_parameters (memory_nest_bounds (multi_pointer_region_nest package)) temps)) by
      (unfold memory_recursive_parameters; rewrite length_map,memory_nest_lengths; reflexivity).
    replace (length (multi_pointer_region_scalars package)) with
      (length (memory_recursive_parameters (multi_pointer_region_scalars package) temps)) by
      (unfold memory_recursive_parameters; rewrite length_map; reflexivity).
    rewrite memory_multi_pointer_source_footprint by
      (unfold memory_recursive_parameters; rewrite length_map,memory_nest_lengths; reflexivity).
    reflexivity.
  - exact (proj2 (multi_pointer_region_cap (multi_pointer_region_syntax package))).
  - eapply Forall_impl; [|exact RANGES]; intros bound RANGE; exact (proj2 (proj2 RANGE)).
Qed.
Print Assumptions memory_multi_pointer_source_footprint.
Print Assumptions memory_multi_pointer_selected_footprint.
