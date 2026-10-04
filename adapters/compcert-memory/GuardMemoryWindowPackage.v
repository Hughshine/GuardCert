From Stdlib Require Import List ZArith.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryNaryCompute GuardMemoryInstructionPadding.
From GuardMemory Require Import GuardMemoryWindowSyntax.
Import ListNotations.
Set Implicit Arguments.
Record window_region_package (source : statement) := WindowRegionPackage {
  window_region_nest : memory_source_nest;
  window_region_caps : list Z;
  window_region_root_lower : Z;
  window_region_parameters : list ident;
  window_region_parameter_bounds : list (Z*Z);
  window_region_pointers : list ident;
  window_region_lower : Z;
  window_region_upper : Z;
  window_region_scalars : list ident;
  window_region_operations : list memory_nary_compute;
  window_region_certificate : window_source_certificate source window_region_nest window_region_caps
    window_region_root_lower window_region_parameters window_region_parameter_bounds window_region_pointers
    window_region_lower window_region_upper window_region_scalars window_region_operations
}.
Definition window_region_instructions source (package : window_region_package source) :=
  memory_pad_instructions (length (window_region_scalars package))
    (map memory_nary_compute_instruction (window_region_operations package)).
