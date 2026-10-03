From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightSyntaxEquality ClightLoopSyntax ClightFrontendLoopProtocol ClightFrontendRegion ClightStraightLine
  ClightRectangularStore ClightRectangularSelector ClightRectangularLoops.
From GuardMemory Require Import GuardMemoryRegistryBackend GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceReifier
  GuardMemoryAffineSourceValuation GuardMemoryAffineAccessExpressions GuardMemoryAffineAccess
  GuardMemoryLayoutRegistry GuardMemoryLayoutOperations GuardMemoryLayoutRanges GuardMemoryCommonLayout GuardMemoryLayoutSyntax
  GuardMemoryGeneralLayoutOperations GuardMemoryGeneralLayoutSequence GuardMemoryGeneralLayoutBodyModel
  GuardMemoryParametricBody GuardMemoryParametricSourceClight GuardMemoryParametricRegion.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition propose_memory_affine_access row column source : option memory_affine_access :=
  match source with
  | Ederef (Ebinop Oadd (Evar array (Tarray _ extent _)) index _) _ =>
      match propose_memory_source_affine index with
      | Some expression => match memory_encode_index row column expression with
          | Some term => Some (MemoryAffineAccess array (RectangleShape extent 1 0 0) expression term)
          | None => None end
      | None => None end
  | _ => None end.
Definition propose_memory_general_layout_operation row bound column inner_bound source :=
  match source with
  | Sassign lhs rhs => match propose_memory_affine_access row column lhs,propose_memory_affine_access row column rhs with
      | Some write,Some read => Some (MemoryGeneralAffineCopy write read)
      | _,_ => option_map MemoryGeneralLayout (propose_memory_layout_operation row bound column inner_bound source)
      end
  | _ => None end.
Fixpoint propose_memory_general_layout_operations row bound column inner_bound sources :=
  match sources with
  | [] => Some []
  | source::rest => match propose_memory_general_layout_operation row bound column inner_bound source,
      propose_memory_general_layout_operations row bound column inner_bound rest with
      | Some operation,Some operations => Some (operation::operations)
      | _,_ => None end
  end.
Definition propose_memory_affine_access_side access :=
  let term := memory_access_index access in
  let coefficient := memory_index_row term+memory_index_column term in
  if 0 <? coefficient then Z.min 1024 (1+(rectangle_extent (memory_access_shape access)-1)/coefficient) else 1024.
Definition propose_memory_affine_access_base access :=
  let term := memory_access_index access in
  let extent := rectangle_extent (memory_access_shape access) in
  if (0 <? memory_index_row term) && (memory_index_row term <=? extent) &&
      (memory_index_column term =? 1) && (memory_index_bias term =? 0) then
    RectangleShape extent (memory_index_row term) 0 0
  else let side := propose_memory_affine_access_side access in RectangleShape (side*side) side 0 0.
Definition propose_memory_general_layout_base operation := match operation with
  | MemoryGeneralLayout operation => propose_memory_layout_common (memory_layout_operation_requests operation)
  | MemoryGeneralAffineCopy write read =>
      Some (memory_common_layout (propose_memory_affine_access_base write)
        (propose_memory_affine_access_base read)) end.
Fixpoint propose_memory_general_layout_bases operations : option (list rectangle_shape) := match operations with
  | [] => Some []
  | operation::operations => match propose_memory_general_layout_base operation,propose_memory_general_layout_bases operations with
      | Some base,Some bases => Some (base::bases) | _,_ => None end end.
Definition propose_memory_general_layout_region source :=
  match propose_frontend_shape source with
  | Some (row,bound,outer_body) => match flatten_region outer_body with
      | [Sset inner_bound expression;Sset column _;inner_loop] =>
          match propose_frontend_shape inner_loop,propose_memory_source_affine expression with
          | Some (_,_,inner_body),Some expression =>
              match propose_memory_general_layout_operations row bound column inner_bound (flatten_region inner_body) with
              | Some operations => match propose_memory_general_layout_bases operations,memory_general_sequence_requests operations with
                  | Some (base::bases),descriptor::_ =>
                      Some (RectangleDescription (fold_left memory_common_layout bases base) (memory_descriptor_variable descriptor)
                        row bound column inner_bound inner_body outer_body,expression,operations)
                  | _,_ => None end
              | None => None end
          | _,_ => None end
      | _ => None end
  | None => None end.
Definition check_memory_general_layout_region source (d : rectangle_description) (expression : memory_source_affine)
  (operations : list memory_general_layout_operation) : option (memory_parametric_region_package source).
Proof.
  destruct (statement_eq source (rectangle_described_source d)) as [SOURCE|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (rectangle_inner_body d))
    (map (memory_general_layout_statement (rectangle_row d) (rectangle_column d)) operations)) as [BODY|]; [|exact None].
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
  destruct (forallb (memory_general_layout_check (described_shape d) (rectangle_row d) (rectangle_column d)) operations) eqn:REQUESTS; [|exact None].
  destruct (memory_descriptors_cover_check (memory_unique_descriptors (memory_general_sequence_requests operations))
    (memory_general_sequence_requests operations)) eqn:COVER; [|exact None].
  assert (VALID : rectangle_layout_valid (described_shape d)) by (apply rectangle_layout_check_sound; exact LAYOUT).
  assert (CERT : Forall (memory_general_layout_valid (described_shape d) (rectangle_row d) (rectangle_column d)) operations).
  { apply Forall_forall; intros operation MEMBER; apply memory_general_layout_check_sound.
    apply forallb_forall with (x := operation) in REQUESTS; assumption. }
  pose proof (@memory_descriptors_cover_check_sound (memory_unique_descriptors (memory_general_sequence_requests operations))
    (memory_general_sequence_requests operations) COVER) as COVERED.
  exact (Some (@MemoryParametricRegionPackage source d expression
    (@MemoryParametricRegionCertificate source d expression SOURCE
      (@memory_general_layout_body_model (described_shape d) operations (rectangle_row d) (rectangle_column d) (rectangle_inner_body d)
        VALID RC CERT COVERED BODY) VALID OUTER RN RC NC RK NK CK SC SK))).
Defined.
Definition describe_memory_general_layout_region source :=
  match propose_memory_general_layout_region source with
  | Some (d,expression,operations) => check_memory_general_layout_region source d expression operations
  | None => None end.
Print Assumptions check_memory_general_layout_region.
