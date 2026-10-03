From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightSyntaxEquality ClightLoopSyntax ClightFrontendLoopProtocol ClightFrontendRegion ClightStraightLine
  ClightRectangularStore ClightRectangularSelector ClightRectangularLoops.
From GuardMemory Require Import GuardMemoryNamedOperations GuardMemoryNamedCompiler GuardMemoryArrayFamilyBackend GuardMemoryAffineSourceExpressions
  GuardMemoryAffineSourceReifier GuardMemoryAffineSourceValuation GuardMemoryAffineSourceContext GuardMemoryAffineSourceLoop GuardMemoryParametricSourceClight.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition propose_named_parametric_region source :=
  match propose_frontend_shape source with
  | Some (row,bound,outer_body) => match flatten_region outer_body with
    | [Sset inner_bound expression;Sset column _;inner_loop] =>
      match propose_frontend_shape inner_loop,propose_memory_source_affine expression with
      | Some (_,_,inner_body),Some expression =>
        match propose_named_array_operations row bound column inner_bound (flatten_region inner_body) with
        | Some (operation::operations) => Some
          (RectangleDescription (named_operation_shape operation) (named_operation_array operation)
            row bound column inner_bound inner_body outer_body,expression,operation::operations)
        | _ => None end
      | _,_ => None end
    | _ => None end
  | None => None end.
Record named_parametric_certificate source d expression operations := NamedParametricCertificate {
  parametric_source : source = rectangle_described_source d;
  parametric_body : flatten_region (rectangle_inner_body d) =
    map (named_operation_statement (rectangle_row d) (rectangle_column d)) operations;
  parametric_outer : flatten_region (rectangle_described_outer_body d) =
    [memory_parametric_setup (rectangle_inner_bound d) (memory_source_affine_code expression);
      rectangle_reset (rectangle_column d);
      frontend_counted_loop (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d)];
  parametric_rn : rectangle_row d <> rectangle_bound d;
  parametric_rc : rectangle_row d <> rectangle_column d;
  parametric_nc : rectangle_bound d <> rectangle_column d;
  parametric_rk : rectangle_row d <> rectangle_inner_bound d;
  parametric_nk : rectangle_bound d <> rectangle_inner_bound d;
  parametric_ck : rectangle_column d <> rectangle_inner_bound d;
  parametric_sc : ~ In (rectangle_column d) (memory_source_affine_parameters (rectangle_row d) expression);
  parametric_sk : ~ In (rectangle_inner_bound d) (memory_source_affine_parameters (rectangle_row d) expression);
  parametric_layout : rectangle_layout_valid (described_shape d);
  parametric_layouts : Forall (named_operation_layout (described_shape d)) operations;
  parametric_nonempty : operations <> []
}.
Definition check_named_parametric source d expression operations : option (named_parametric_certificate source d expression operations).
Proof.
  destruct (statement_eq source (rectangle_described_source d)) as [SOURCE|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (rectangle_inner_body d))
    (map (named_operation_statement (rectangle_row d) (rectangle_column d)) operations)) as [BODY|]; [|exact None].
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
  destruct (forallb (fun operation => same_array_layout_check (described_shape d) (named_operation_shape operation)) operations) eqn:LAYOUTS; [|exact None].
  assert (ALL : Forall (named_operation_layout (described_shape d)) operations).
  { apply Forall_forall; intros operation MEMBER; unfold named_operation_layout; apply same_array_layout_check_sound.
    exact (proj1 (forallb_forall _ _) LAYOUTS operation MEMBER). }
  destruct operations as [|operation operations]; [exact None|].
  exact (Some (@NamedParametricCertificate source d expression (operation::operations) SOURCE BODY OUTER
    RN RC NC RK NK CK SC SK (@rectangle_layout_check_sound (described_shape d) LAYOUT) ALL ltac:(discriminate))).
Defined.
Record memory_parametric_package source := MemoryParametricPackage {
  parametric_description : rectangle_description;
  parametric_expression : memory_source_affine;
  parametric_operations : list named_array_operation;
  parametric_syntax : named_parametric_certificate source parametric_description parametric_expression parametric_operations
}.
Definition describe_memory_parametric source : option (memory_parametric_package source) :=
  match propose_named_parametric_region source with
  | Some (d,expression,operations) => match check_named_parametric source d expression operations with
    | Some CERT => Some (@MemoryParametricPackage source d expression operations CERT) | None => None end
  | None => None end.
