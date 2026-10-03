From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightSyntaxEquality ClightLoopSyntax ClightFrontendLoopProtocol ClightFrontendRegion ClightStraightLine
  ClightRectangularStore ClightRectangularSelector ClightRectangularLoops.
From GuardMemory Require Import GuardMemoryRegistryBackend GuardMemoryNamedCompiler GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceReifier
  GuardMemoryAffineSourceValuation GuardMemoryLayoutCopySyntax GuardMemoryLayoutOperations GuardMemoryLayoutRegistry
  GuardMemoryLayoutSequence GuardMemoryLayoutRanges GuardMemoryLayoutBodyModel GuardMemoryParametricBody
  GuardMemoryParametricSourceClight GuardMemoryParametricRegion.
Import ListNotations.
Set Implicit Arguments.
Definition propose_memory_layout_operation row bound column inner_bound source :=
  match source with
  | Sassign lhs rhs => match propose_memory_copy_lvalue lhs,propose_memory_copy_lvalue rhs with
    | Some (ws,wa),Some (rs,ra) => Some (MemoryLayoutCopy ws rs wa ra)
    | _,_ => match propose_named_array_operation row bound column inner_bound source with
      | Some operation => Some (MemoryLayoutNamed operation) | None => None end
    end
  | _ => None end.
Fixpoint propose_memory_layout_operations row bound column inner_bound sources :=
  match sources with
  | [] => Some []
  | source::rest => match propose_memory_layout_operation row bound column inner_bound source,
      propose_memory_layout_operations row bound column inner_bound rest with
    | Some operation,Some operations => Some (operation::operations)
    | _,_ => None end
  end.
Definition propose_memory_layout_region source :=
  match propose_frontend_shape source with
  | Some (row,bound,outer_body) => match flatten_region outer_body with
    | [Sset inner_bound expression;Sset column _;inner_loop] =>
      match propose_frontend_shape inner_loop,propose_memory_source_affine expression with
      | Some (_,_,inner_body),Some expression =>
        match propose_memory_layout_operations row bound column inner_bound (flatten_region inner_body) with
        | Some (operation::operations) =>
          let operations := operation::operations in
          let requests := memory_layout_sequence_requests operations in
          match propose_memory_layout_common requests,requests with
          | Some base,descriptor::_ => Some (RectangleDescription base (memory_descriptor_variable descriptor)
              row bound column inner_bound inner_body outer_body,expression,operations)
          | _,_ => None end
        | _ => None end
      | _,_ => None end
    | _ => None end
  | None => None end.
Definition check_memory_layout_region source (d : rectangle_description) (expression : memory_source_affine)
  (operations : list memory_layout_operation) : option (memory_parametric_region_package source).
Proof.
  destruct (statement_eq source (rectangle_described_source d)) as [SOURCE|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (rectangle_inner_body d))
    (map (memory_layout_operation_statement (rectangle_row d) (rectangle_column d)) operations)) as [BODY|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (rectangle_described_outer_body d))
    [memory_parametric_setup (rectangle_inner_bound d) (memory_source_affine_code expression); rectangle_reset (rectangle_column d);
      frontend_counted_loop (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d)]) as [OUTER|]; [|exact None].
  destruct (peq (rectangle_row d) (rectangle_bound d)) as [|RN]; [exact None|].
  destruct (peq (rectangle_row d) (rectangle_column d)) as [|RC]; [exact None|].
  destruct (peq (rectangle_bound d) (rectangle_column d)) as [|NC]; [exact None|].
  destruct (peq (rectangle_row d) (rectangle_inner_bound d)) as [|RK]; [exact None|].
  destruct (peq (rectangle_bound d) (rectangle_inner_bound d)) as [|NK]; [exact None|].
  destruct (peq (rectangle_column d) (rectangle_inner_bound d)) as [|CK]; [exact None|].
  destruct (in_dec peq (rectangle_column d) (memory_source_affine_parameters (rectangle_row d) expression)) as [|SC]; [exact None|].
  destruct (in_dec peq (rectangle_inner_bound d) (memory_source_affine_parameters (rectangle_row d) expression)) as [|SK]; [exact None|].
  destruct (rectangle_layout_check (described_shape d)) eqn:LAYOUT; [|exact None].
  destruct (memory_layout_requests_check (described_shape d) (memory_layout_sequence_requests operations)) eqn:REQUESTS; [|exact None].
  destruct (memory_descriptors_cover_check (memory_unique_descriptors (memory_layout_sequence_requests operations))
    (memory_layout_sequence_requests operations)) eqn:COVER; [|exact None].
  assert (VALID : rectangle_layout_valid (described_shape d)) by (apply rectangle_layout_check_sound; exact LAYOUT).
  pose proof (@memory_layout_requests_check_sound (described_shape d) (memory_layout_sequence_requests operations) REQUESTS) as RANGES.
  pose proof (@memory_descriptors_cover_check_sound (memory_unique_descriptors (memory_layout_sequence_requests operations))
    (memory_layout_sequence_requests operations) COVER) as COVERED.
  exact (Some (@MemoryParametricRegionPackage source d expression
    (@MemoryParametricRegionCertificate source d expression SOURCE
      (@memory_layout_body_model (described_shape d) operations (rectangle_row d) (rectangle_column d) (rectangle_inner_body d)
        VALID RANGES COVERED BODY) VALID OUTER RN RC NC RK NK CK SC SK))).
Defined.
Definition describe_memory_layout_region source :=
  match propose_memory_layout_region source with
  | Some (d,expression,operations) => check_memory_layout_region source d expression operations
  | None => None end.
Print Assumptions check_memory_layout_region.
