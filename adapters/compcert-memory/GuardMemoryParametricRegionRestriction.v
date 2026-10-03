From Stdlib Require Import List Bool ZArith Lia.
From Guard Require Import ClightRectangularStore ClightRectangularGuard ClightRectangularSelector.
From GuardMemory Require Import GuardMemoryParametricBody GuardMemoryParametricRegion.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Restriction consumes only the source instance's range-indexed properties.
    It neither decodes source statements nor interprets memory operations. *)
Definition memory_parametric_body_restrict old new row column body
  (ROWS : rectangle_outer_limit new <= rectangle_outer_limit old)
  (COLUMNS : rectangle_stride new <= rectangle_stride old)
  (model : memory_parametric_body_model old row column body) : memory_parametric_body_model new row column body.
Proof.
  refine {| parametric_body_descriptors := parametric_body_descriptors model;
    parametric_body_instructions := parametric_body_instructions model;
    parametric_body_point := parametric_body_point model;
    parametric_body_normal := parametric_body_normal model;
    parametric_body_quiet := parametric_body_quiet model;
    parametric_body_writes := parametric_body_writes model;
    parametric_body_registry := parametric_body_registry model |}.
  - intros fe ge locals le before after final i j I J ROW COLUMN RUN.
    eapply parametric_body_decode; [| |exact ROW|exact COLUMN|exact RUN]; lia.
  - intros entries ge locals i j before after ARRAYS UNIQUE I J.
    eapply parametric_body_correspondence; [exact ARRAYS|exact UNIQUE| |]; lia.
Defined.
Definition memory_parametric_package_restrict source (package : memory_parametric_region_package source) shape
  (VALID : rectangle_layout_valid shape)
  (ROWS : rectangle_outer_limit shape <= rectangle_outer_limit (described_shape (parametric_region_description package)))
  (COLUMNS : rectangle_stride shape <= rectangle_stride (described_shape (parametric_region_description package))) :
  memory_parametric_region_package source.
Proof.
  destruct package as [d expression CERT]; destruct CERT as [SOURCE MODEL LAYOUT OUTER RN RC NC RK NK CK SC SK].
  refine (@MemoryParametricRegionPackage source
    (RectangleDescription shape (described_array d) (rectangle_row d) (rectangle_bound d)
      (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d) (rectangle_described_outer_body d)) expression _).
  refine (@MemoryParametricRegionCertificate source
    (RectangleDescription shape (described_array d) (rectangle_row d) (rectangle_bound d)
      (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d) (rectangle_described_outer_body d)) expression SOURCE
    (@memory_parametric_body_restrict (described_shape d) shape (rectangle_row d) (rectangle_column d)
      (rectangle_inner_body d) ROWS COLUMNS MODEL) VALID OUTER RN RC NC RK NK CK SC SK).
Defined.
Definition check_memory_parametric_package_restriction source (package : memory_parametric_region_package source) (shape : rectangle_shape) :
  option (memory_parametric_region_package source).
Proof.
  destruct (rectangle_layout_check shape) eqn:VALID; [|exact None].
  destruct (rectangle_outer_limit shape <=? rectangle_outer_limit (described_shape (parametric_region_description package))) eqn:ROWS;
    [|exact None].
  destruct (rectangle_stride shape <=? rectangle_stride (described_shape (parametric_region_description package))) eqn:COLUMNS;
    [|exact None].
  apply rectangle_layout_check_sound in VALID; apply Z.leb_le in ROWS,COLUMNS.
  exact (Some (memory_parametric_package_restrict package VALID ROWS COLUMNS)).
Defined.
Definition describe_memory_parametric_width columns
  (describe : forall source, option (memory_parametric_region_package source)) source :=
  match describe source with
  | None => None
  | Some package =>
      let base := described_shape (parametric_region_description package) in
      let width := Z.min columns (rectangle_stride base) in
      check_memory_parametric_package_restriction package
        (RectangleShape (rectangle_outer_limit base*width) width 0 0)
  end.
Print Assumptions memory_parametric_body_restrict.
Print Assumptions memory_parametric_package_restrict.
Print Assumptions check_memory_parametric_package_restriction.
