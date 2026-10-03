From Stdlib Require Import List.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightStraightLine ClightRectangularStore ClightRectangularSelector ClightRectangularLoops ClightFrontendLoopProtocol.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation
  GuardMemoryParametricSourceClight GuardMemoryParametricBody.
Import ListNotations.
Set Implicit Arguments.
Record memory_parametric_region_certificate source d expression := MemoryParametricRegionCertificate {
  parametric_region_source : source = rectangle_described_source d;
  parametric_region_body_model : memory_parametric_body_model (described_shape d)
    (rectangle_row d) (rectangle_column d) (rectangle_inner_body d);
  parametric_region_layout : rectangle_layout_valid (described_shape d);
  parametric_region_outer : flatten_region (rectangle_described_outer_body d) =
    [memory_parametric_setup (rectangle_inner_bound d) (memory_source_affine_code expression);
      rectangle_reset (rectangle_column d);
      frontend_counted_loop (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d)];
  parametric_region_rn : rectangle_row d <> rectangle_bound d;
  parametric_region_rc : rectangle_row d <> rectangle_column d;
  parametric_region_nc : rectangle_bound d <> rectangle_column d;
  parametric_region_rk : rectangle_row d <> rectangle_inner_bound d;
  parametric_region_nk : rectangle_bound d <> rectangle_inner_bound d;
  parametric_region_ck : rectangle_column d <> rectangle_inner_bound d;
  parametric_region_sc : ~ In (rectangle_column d) (memory_source_affine_parameters (rectangle_row d) expression);
  parametric_region_sk : ~ In (rectangle_inner_bound d) (memory_source_affine_parameters (rectangle_row d) expression)
}.
Record memory_parametric_region_package source := MemoryParametricRegionPackage {
  parametric_region_description : rectangle_description;
  parametric_region_expression : memory_source_affine;
  parametric_region_syntax : memory_parametric_region_certificate source parametric_region_description parametric_region_expression
}.
Definition memory_parametric_region_model source (package : memory_parametric_region_package source) :=
  parametric_region_body_model (parametric_region_syntax package).
Definition memory_parametric_region_instructions source (package : memory_parametric_region_package source) :=
  parametric_body_instructions (memory_parametric_region_model package).
Definition memory_parametric_region_descriptors source (package : memory_parametric_region_package source) :=
  parametric_body_descriptors (memory_parametric_region_model package).
