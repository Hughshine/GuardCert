From Stdlib Require Import List ZArith Lia Bool.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCountedLoop ClightStraightLine.
From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryNaryCompute GuardMemoryPointerCompute
  GuardMemorySourceParameters GuardMemoryPointerSourceWords GuardMemoryMultiPointerIdentifiers.
From GuardMemory Require Import GuardMemoryIntervalBox GuardMemoryWindowCompute.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition window_source_coordinate_bounds (root_lower : Z) (caps : list Z) :=
  match caps with [] => [] | first::rest => (root_lower,first)::map (fun cap => (0,cap)) rest end.
Lemma window_source_coordinate_bounds_length root_lower caps :
  length (window_source_coordinate_bounds root_lower caps) = length caps.
Proof. destruct caps; cbn; [reflexivity|rewrite length_map; reflexivity]. Qed.
Record window_source_certificate source nest caps root_lower parameters parameter_bounds pointers lower upper scalars operations :=
  WindowSourceCertificate {
  window_source_exact : source = memory_nest_source nest;
  window_source_nonempty : memory_nest_iterators nest <> [];
  window_source_shapes : memory_nest_shapes nest;
  window_source_fresh : memory_nest_fresh nest;
  window_source_caps_length : length caps = length (memory_nest_iterators nest);
  window_source_caps : Forall (fun cap => 0 < cap /\ signed_range cap) caps;
  window_source_root_lower : signed_range root_lower /\ root_lower < hd 1 caps;
  window_source_parameters_length : length parameter_bounds = length parameters;
  window_source_parameter_bounds : Forall (fun bound => fst bound < snd bound /\
    signed_range (fst bound) /\ signed_range (snd bound-1)) parameter_bounds;
  window_source_parameter_stable : forall identifier, In identifier parameters -> ~ In identifier (memory_nest_iterators nest);
  window_source_parameter_used : forall identifier, In identifier parameters -> exists operation,
    In operation operations /\ In identifier (memory_pointer_operation_address_reads operation);
  window_source_window : lower < upper /\ signed_range lower /\ signed_range (upper-1) /\ 4*(upper-lower) <= Ptrofs.modulus;
  window_source_pointers_stable : forall identifier, In identifier pointers -> ~ In identifier (memory_nest_iterators nest);
  window_source_registers : NoDup ((memory_nest_iterators nest++parameters)++scalars);
  window_source_scalar_stable : forall identifier, In identifier scalars -> ~ In identifier (memory_nest_iterators nest);
  window_source_scalar_used : forall identifier, In identifier scalars -> exists operation index,
    In operation operations /\ nth_error ((memory_nest_iterators nest++parameters)++scalars) index = Some identifier /\
    In index (memory_source_parameter_positions (memory_nary_compute_value operation));
  window_source_operations_nonempty : operations <> [];
  window_source_operations : Forall (window_compute_valid
    (window_source_coordinate_bounds root_lower caps++parameter_bounds)
    lower upper (memory_nest_iterators nest++parameters) scalars) operations;
  window_source_covered : Forall (memory_multi_pointer_operation_covered pointers) operations;
  window_source_body : flatten_region (memory_nest_leaf nest) = map memory_pointer_compute_statement operations
}.
