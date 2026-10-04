From Stdlib Require Import List ZArith.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryNaryCompute.
From GuardMemory Require Import GuardMemoryWindowPackage GuardMemoryWindowSourceCheck.
Set Implicit Arguments.
Definition make_window_region_package (source : statement) (nest : memory_source_nest) (caps : list Z) (root_lower : Z)
  (parameters : list ident) (parameter_bounds : list (Z*Z)) (pointers : list ident)
  (lower upper : Z) (scalars : list ident) (operations : list memory_nary_compute)
  : option (window_region_package source).
Proof.
  destruct (check_window_source source nest caps root_lower parameters parameter_bounds pointers lower upper scalars operations)
    as [CERT|]; [|exact None].
  exact (Some (@WindowRegionPackage source nest caps root_lower parameters parameter_bounds pointers lower upper scalars operations CERT)).
Defined.
Print Assumptions make_window_region_package.
