From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightSyntaxEquality ClightLoopSyntax ClightFrontendLoopProtocol ClightFrontendRegion ClightStraightLine
  ClightRectangularStore ClightRectangularSelector ClightRectangularLoops.
From GuardMemory Require Import GuardMemoryNamedOperations GuardMemoryNamedCompiler GuardMemoryArrayFamilyBackend GuardMemoryAffineSourceExpressions
  GuardMemoryAffineSourceReifier GuardMemoryAffineSourceValuation GuardMemoryAffineSourceContext GuardMemoryAffineSourceLoop GuardMemoryParametricSourceClight
  GuardMemoryLayoutCopy GuardMemoryCommonLayout GuardMemoryCopyLayoutRegistry.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition rectangle_shape_eq : forall first second : rectangle_shape, {first = second}+{first <> second}.
Proof. decide equality; apply Z.eq_dec. Defined.
Definition propose_memory_copy_lvalue expression : option (rectangle_shape * ident) :=
  match expression with
  | Ederef (Ebinop _ (Evar array (Tarray _ extent _))
      (Ebinop _ (Ebinop _ _ stride_expression _) _ _) _) _ =>
    match propose_rectangle_constant stride_expression with
    | Some stride => Some (RectangleShape extent stride 0 0,array)
    | None => None end
  | _ => None end.
Definition propose_memory_layout_copy_region source :=
  match propose_frontend_shape source with
  | Some (row,bound,outer_body) => match flatten_region outer_body with
    | [Sset inner_bound expression;Sset column _;inner_loop] =>
      match propose_frontend_shape inner_loop,propose_memory_source_affine expression with
      | Some (_,_,inner_body),Some expression =>
        match flatten_region inner_body with
        | [Sassign lhs rhs] => match propose_memory_copy_lvalue lhs,propose_memory_copy_lvalue rhs with
          | Some (write_shape,write_array),Some (read_shape,read_array) =>
            Some (RectangleDescription (memory_common_layout write_shape read_shape) write_array
              row bound column inner_bound inner_body outer_body,expression,write_shape,read_shape,write_array,read_array)
          | _,_ => None end
        | _ => None end
      | _,_ => None end
    | _ => None end
  | None => None end.
Record memory_layout_copy_certificate source d expression write_shape read_shape write_array read_array := MemoryLayoutCopyCertificate {
  layout_copy_source : source = rectangle_described_source d;
  layout_copy_body : flatten_region (rectangle_inner_body d) =
    [memory_layout_copy_statement write_shape read_shape write_array read_array (rectangle_row d) (rectangle_column d)];
  layout_copy_outer : flatten_region (rectangle_described_outer_body d) =
    [memory_parametric_setup (rectangle_inner_bound d) (memory_source_affine_code expression);
      rectangle_reset (rectangle_column d);
      frontend_counted_loop (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d)];
  layout_copy_rn : rectangle_row d <> rectangle_bound d;
  layout_copy_rc : rectangle_row d <> rectangle_column d;
  layout_copy_nc : rectangle_bound d <> rectangle_column d;
  layout_copy_rk : rectangle_row d <> rectangle_inner_bound d;
  layout_copy_nk : rectangle_bound d <> rectangle_inner_bound d;
  layout_copy_ck : rectangle_column d <> rectangle_inner_bound d;
  layout_copy_sc : ~ In (rectangle_column d) (memory_source_affine_parameters (rectangle_row d) expression);
  layout_copy_sk : ~ In (rectangle_inner_bound d) (memory_source_affine_parameters (rectangle_row d) expression);
  layout_copy_common : described_shape d = memory_common_layout write_shape read_shape;
  layout_copy_write_layout : rectangle_layout_valid write_shape;
  layout_copy_read_layout : rectangle_layout_valid read_shape;
  layout_copy_arrays_compatible : memory_copy_layout_compatible write_shape read_shape write_array read_array
}.
Definition check_memory_layout_copy source d expression write_shape read_shape write_array read_array : option (memory_layout_copy_certificate source d expression write_shape read_shape write_array read_array).
Proof.
  destruct (statement_eq source (rectangle_described_source d)) as [SOURCE|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (rectangle_inner_body d))
    ([memory_layout_copy_statement write_shape read_shape write_array read_array (rectangle_row d) (rectangle_column d)])) as [BODY|]; [|exact None].
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
  destruct (rectangle_layout_check write_shape) eqn:WL; [|exact None].
  destruct (rectangle_layout_check read_shape) eqn:RL; [|exact None].
  destruct (peq write_array read_array) as [SAME|DIFFERENT].
  - destruct (Z.eq_dec (rectangle_extent write_shape) (rectangle_extent read_shape)) as [EXTENT|]; [|exact None].
    assert (ARRAYS : memory_copy_layout_compatible write_shape read_shape write_array read_array) by (right; exact EXTENT).
    destruct (rectangle_shape_eq (described_shape d) (memory_common_layout write_shape read_shape)) as [COMMON|]; [|exact None].
    exact (Some (@MemoryLayoutCopyCertificate source d expression write_shape read_shape write_array read_array
      SOURCE BODY OUTER RN RC NC RK NK CK SC SK COMMON
      (@rectangle_layout_check_sound write_shape WL) (@rectangle_layout_check_sound read_shape RL) ARRAYS)).
  - assert (ARRAYS : memory_copy_layout_compatible write_shape read_shape write_array read_array) by (left; exact DIFFERENT).
    destruct (rectangle_shape_eq (described_shape d) (memory_common_layout write_shape read_shape)) as [COMMON|]; [|exact None].
    exact (Some (@MemoryLayoutCopyCertificate source d expression write_shape read_shape write_array read_array
    SOURCE BODY OUTER RN RC NC RK NK CK SC SK COMMON
    (@rectangle_layout_check_sound write_shape WL) (@rectangle_layout_check_sound read_shape RL) ARRAYS)).
Defined.
Record memory_layout_copy_package source := MemoryLayoutCopyPackage {
  layout_copy_description : rectangle_description;
  layout_copy_expression : memory_source_affine;
  layout_copy_write_shape : rectangle_shape;
  layout_copy_read_shape : rectangle_shape;
  layout_copy_write_array : ident;
  layout_copy_read_array : ident;
  layout_copy_syntax : memory_layout_copy_certificate source layout_copy_description layout_copy_expression
    layout_copy_write_shape layout_copy_read_shape layout_copy_write_array layout_copy_read_array
}.
Definition describe_memory_layout_copy source : option (memory_layout_copy_package source) :=
  match propose_memory_layout_copy_region source with
  | Some (d,expression,ws,rs,wa,ra) => match check_memory_layout_copy source d expression ws rs wa ra with
    | Some CERT => Some (@MemoryLayoutCopyPackage source d expression ws rs wa ra CERT) | None => None end
  | None => None end.
