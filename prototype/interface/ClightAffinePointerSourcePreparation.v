From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightGuard ClightNoWrap.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryMultiPointerCells
  GuardMemoryParametricGuard GuardMemoryParametricWidth GuardMemoryParametricSourceClight
  GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineInnerPointerSourceDomain
  GuardMemoryAffineInnerPointerRegionSource.
From GuardInterface Require Import ClightAffinePointerGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition affine_inner_pointer_package_preparation_tree source (package : memory_affine_inner_pointer_package source) width_tree :=
  affine_inner_pointer_preparation_tree (affine_inner_pointer_shape package) (affine_inner_pointer_expression package)
    (affine_inner_pointer_row_limit package) (affine_inner_pointer_header_limits package)
    (affine_inner_pointer_body_parameters package) (affine_inner_pointer_body_limits package) width_tree.

(** One package and one actual entry connect C_guard to source/model
    correspondence. This does not establish non-alias, validate a candidate,
    or discharge C_host. Those remain distinct subsequent certificates. *)
Theorem affine_inner_pointer_preparation_source_execution source (package : memory_affine_inner_pointer_package source)
  width_tree fe ge locals temps memory after final :
  let shape := affine_inner_pointer_shape package in
  let expression := affine_inner_pointer_expression package in
  let values := memory_source_parameter_values (memory_affine_inner_pointer_region_context package) (Entry ge locals temps memory) in
  compile_memory_source_width (affine_inner_pointer_column_limit package) (affine_inner_pointer_row shape)
    (memory_affine_inner_pointer_header shape expression)
    (affine_inner_pointer_header_bounds (affine_inner_pointer_row_limit package) (affine_inner_pointer_header_limits package))
    expression = Some width_tree ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  decision_run (Entry ge locals temps memory) (affine_inner_pointer_package_preparation_tree package width_tree) true ->
  L.loop_semantics (memory_affine_inner_pointer_region_model package) values
    (RuntimeState (memory_multi_pointer_locations temps (affine_inner_pointer_extent package)) memory)
    (RuntimeState (memory_multi_pointer_locations temps (affine_inner_pointer_extent package)) final) /\
  after = PTree.set (affine_inner_pointer_row shape)
    (Vint (Int.repr (Int.signed (temp_word (affine_inner_pointer_bound shape) temps))))
    (memory_parametric_settle (affine_inner_pointer_column shape) (affine_inner_pointer_inner_bound shape)
      (fun i => L.eval_expr (i::values) (affine_inner_pointer_encoded package))
      (Int.signed (temp_word (affine_inner_pointer_bound shape) temps)-1) temps).
Proof.
  pose proof (@memory_affine_inner_pointer_region_source_under_ranges source package fe ge locals temps memory after final) as DECODE.
  destruct package as [shape expression encoded row_limit column_limit header_limits body_parameters body_limits
    pointers extent scalars operations CERT]; cbn; intros LOWER SOURCE RUN.
  assert (DOMAIN : memory_affine_inner_pointer_completed fe shape (Entry ge locals temps memory)).
  { exists after,final; rewrite <- (affine_inner_pointer_source_exact CERT); exact SOURCE. }
  destruct (@affine_inner_pointer_preparation_ranges source shape expression encoded row_limit column_limit
    header_limits body_limits body_parameters pointers scalars extent operations CERT fe fragment_observation
    (@eq fragment_observation) width_tree LOWER (Entry ge locals temps memory) DOMAIN RUN)
    as [HEADER [WIDTH [RANGES VIEW]]].
  apply DECODE; assumption.
Qed.
Print Assumptions affine_inner_pointer_preparation_source_execution.
