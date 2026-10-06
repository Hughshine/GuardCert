From Stdlib Require Import List ZArith Lia.
From compcert.common Require Import AST Values Memory.
From polcert.src Require Import PolyBase.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryNaryCompute
  GuardMemoryNaryAffineAccess GuardMemoryMultiPointerCompute GuardMemoryMultiPointerCells
  GuardMemoryRecursiveSource GuardMemoryRectangularFootprint
  GuardMemoryLinearPointerSyntax GuardMemoryInstructionPadding GuardMemoryMultiPointerFootprint
  GuardMemoryPointerAccessFootprint GuardMemoryLoopTrace GuardMemoryFiniteFootprint
  GuardMemoryFootprintCapabilities GuardMemoryAffineParameterLoops GuardMemoryAffineParameterFootprint.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_affine_parameter_pointer_footprint expression extra operations context :=
  memory_events_footprint (memory_loop_trace
    (memory_affine_parameter_sequence (length context) expression
      (memory_pad_instructions extra (map memory_nary_compute_instruction operations))) context).

Theorem memory_affine_parameter_pointer_footprint_member expression extra operations context cell :
  In cell (memory_affine_parameter_pointer_footprint expression extra operations context) <->
  exists access i j,
    In access (memory_linear_pointer_accesses operations) /\
    0 <= i < L.eval_expr context (L.Var 0) /\
    0 <= j < L.eval_expr (i::context) expression /\
    cell = memory_param_axis_pointer_access_cell access ([i;j]++context).
Proof.
  unfold memory_affine_parameter_pointer_footprint; rewrite memory_affine_parameter_sequence_footprint.
  rewrite in_flat_map; split.
  - intros [coordinates [POINT CELL]].
    apply memory_affine_parameter_point_member in POINT as [i [j [-> [I J]]]].
    rewrite memory_param_axis_pointer_point_footprint in CELL.
    apply in_map_iff in CELL as [access [SAME MEMBER]]; exists access,i,j; auto.
  - intros [access [i [j [MEMBER [I [J ->]]]]]].
    exists [i;j]; split.
    + apply memory_affine_parameter_point_member; exists i,j; auto.
    + rewrite memory_param_axis_pointer_point_footprint; apply in_map_iff; exists access; auto.
Qed.

Theorem memory_affine_parameter_pointer_geometry_footprint expression operations parameters scalars
  limits layout scalar_ids extent :
  Forall (memory_multi_pointer_compute_valid limits layout scalar_ids extent) operations ->
  (2+length parameters)%nat = length layout ->
  memory_affine_parameter_pointer_footprint expression (length scalar_ids) operations (parameters++scalars) =
    flat_map (fun coordinates => map (fun access => memory_param_axis_pointer_access_cell access
      (coordinates++parameters)) (memory_linear_pointer_accesses operations))
      (memory_affine_parameter_points expression (parameters++scalars)).
Proof.
  intros VALID LENGTH; unfold memory_affine_parameter_pointer_footprint.
  rewrite memory_affine_parameter_sequence_footprint.
  apply memory_flat_map_ext_in; intros coordinates POINT.
  apply memory_affine_parameter_point_member in POINT as [i [j [-> [I J]]]].
  rewrite app_assoc.
  rewrite (@memory_multi_pointer_point_footprint_prefix limits layout scalar_ids extent operations
    ([i;j]++parameters) scalars VALID ltac:(rewrite length_app; cbn; exact LENGTH)).
  apply memory_param_axis_pointer_point_footprint.
Qed.

Theorem memory_affine_parameter_pointer_geometry_member expression operations parameters scalars
  limits layout scalar_ids extent cell :
  Forall (memory_multi_pointer_compute_valid limits layout scalar_ids extent) operations ->
  (2+length parameters)%nat = length layout ->
  (In cell (memory_affine_parameter_pointer_footprint expression (length scalar_ids) operations (parameters++scalars)) <->
   exists access coordinates,
    In access (memory_linear_pointer_accesses operations) /\
    In coordinates (memory_affine_parameter_points expression (parameters++scalars)) /\
    cell = memory_param_axis_pointer_access_cell access (coordinates++parameters)).
Proof.
  intros VALID LENGTH; rewrite (@memory_affine_parameter_pointer_geometry_footprint expression operations
    parameters scalars limits layout scalar_ids extent VALID LENGTH).
  rewrite in_flat_map; split.
  - intros [coordinates [POINT CELL]]; apply in_map_iff in CELL as [access [SAME ACCESS]].
    exists access,coordinates; auto.
  - intros [access [coordinates [ACCESS [POINT ->]]]]; exists coordinates; split; [exact POINT|].
    apply in_map_iff; exists access; auto.
Qed.

Theorem memory_affine_parameter_pointer_footprint_box expression extra operations context column_cap :
  (forall i, 0 <= i < L.eval_expr context (L.Var 0) ->
    L.eval_expr (i::context) expression <= column_cap) ->
  forall cell, In cell (memory_affine_parameter_pointer_footprint expression extra operations context) ->
  exists access coordinates,
    In access (memory_linear_pointer_accesses operations) /\
    Forall2 (fun coordinate count => 0 <= coordinate < count) coordinates
      [L.eval_expr context (L.Var 0);column_cap] /\
    cell = memory_param_axis_pointer_access_cell access (coordinates++context).
Proof.
  intros BOUND cell MEMBER.
  apply memory_affine_parameter_pointer_footprint_member in MEMBER as [access [i [j [ACCESS [I [J SAME]]]]]].
  exists access,[i;j]; split; [exact ACCESS|split; [|exact SAME]].
  constructor; [exact I|constructor; [specialize (BOUND i I); lia|constructor]].
Qed.

(** Capability is obtained from source execution at these exact points.
    Nothing here provides capability for the extra points in the box. *)
Theorem memory_affine_parameter_pointer_source_capabilities expression extra operations context temps extent before after :
  L.loop_semantics
    (memory_affine_parameter_sequence (length context) expression
      (memory_pad_instructions extra (map memory_nary_compute_instruction operations))) context
    (RuntimeState (memory_multi_pointer_locations temps extent) before)
    (RuntimeState (memory_multi_pointer_locations temps extent) after) ->
  Forall (memory_cell_capable (memory_multi_pointer_locations temps extent) before)
    (memory_affine_parameter_pointer_footprint expression extra operations context).
Proof.
  intro SOURCE; pose proof (@memory_loop_source_capabilities _ _
    (RuntimeState (memory_multi_pointer_locations temps extent) before)
    (RuntimeState (memory_multi_pointer_locations temps extent) after)
    (memory_multi_pointer_locations_int32 temps extent) SOURCE) as CAPABLE.
  apply Forall_forall; intros cell MEMBER.
  unfold memory_affine_parameter_pointer_footprint,memory_events_footprint in MEMBER.
  apply in_flat_map in MEMBER as [event [EVENT ACCESS]].
  apply Forall_forall with (x := event) in CAPABLE; [|exact EVENT].
  apply Forall_forall with (x := cell) in CAPABLE; [exact CAPABLE|exact ACCESS].
Qed.

Print Assumptions memory_affine_parameter_pointer_footprint_member.
Print Assumptions memory_affine_parameter_pointer_footprint_box.
Print Assumptions memory_affine_parameter_pointer_geometry_footprint.
Print Assumptions memory_affine_parameter_pointer_geometry_member.
Print Assumptions memory_affine_parameter_pointer_source_capabilities.
