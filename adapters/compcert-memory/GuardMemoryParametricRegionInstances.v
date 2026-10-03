From Stdlib Require Import List.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightRectangularStore ClightRectangularSelector.
From GuardMemory Require Import GuardMemoryParametricBody GuardMemoryCommonLayout GuardMemoryNamedBodyModel GuardMemoryLayoutCopyBodyModel
  GuardMemoryParametricSyntax GuardMemoryLayoutCopySyntax GuardMemoryParametricRegion GuardMemoryLayoutSyntax GuardMemoryGeneralLayoutSyntax GuardMemoryOffsetSyntax.
Set Implicit Arguments.
Definition memory_named_parametric_region source (package : memory_parametric_package source) : memory_parametric_region_package source.
Proof.
  destruct package as [d expression operations CERT].
  destruct CERT as [SOURCE BODY OUTER RN RC NC RK NK CK SC SK VALID LAYOUTS NONEMPTY].
  refine (@MemoryParametricRegionPackage source d expression _).
  exact (@MemoryParametricRegionCertificate source d expression SOURCE
    (@memory_named_body_model (described_shape d) operations (rectangle_row d) (rectangle_column d) (rectangle_inner_body d) VALID LAYOUTS BODY)
    VALID OUTER RN RC NC RK NK CK SC SK).
Defined.
Definition memory_copy_parametric_region source (package : memory_layout_copy_package source) : memory_parametric_region_package source.
Proof.
  destruct package as [d expression ws rs wa ra CERT].
  destruct CERT as [SOURCE BODY OUTER RN RC NC RK NK CK SC SK COMMON WVALID RVALID COMPATIBLE].
  assert (VALID : rectangle_layout_valid (described_shape d)) by (rewrite COMMON; apply memory_common_layout_valid; assumption).
  assert (MODEL : memory_parametric_body_model (described_shape d) (rectangle_row d) (rectangle_column d) (rectangle_inner_body d)).
  { rewrite COMMON; exact (@memory_layout_copy_body_model ws rs wa ra (rectangle_row d) (rectangle_column d) (rectangle_inner_body d)
      WVALID RVALID COMPATIBLE BODY). }
  refine (@MemoryParametricRegionPackage source d expression _).
  exact (@MemoryParametricRegionCertificate source d expression SOURCE MODEL VALID OUTER RN RC NC RK NK CK SC SK).
Defined.
Definition describe_memory_parametric_region source :=
  match describe_memory_parametric source with
  | Some package => Some (memory_named_parametric_region package)
  | None => match describe_memory_layout_copy source with
    | Some package => Some (memory_copy_parametric_region package)
    | None => match describe_memory_layout_region source with
      | Some package => Some package
      | None => match describe_memory_general_layout_region source with
        | Some package => Some package
        | None => describe_memory_offset_region source end end end
  end.
Print Assumptions memory_named_parametric_region.
Print Assumptions memory_copy_parametric_region.
