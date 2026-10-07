From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight Ctypes.
From Guard Require Import ClightSyntaxEquality ClightTempFootprint ClightNoWrap.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions GuardMemoryRecursiveSyntax GuardMemoryLoops.
From GuardAffineNest Require Import AffineNestSyntax AffineNestGuardPackage AffineNestExit
  AffineNestScanNamespace AffineNestStaticPackage AffineNestLoopEncoding AffineNestLeafDecode.
From GuardInterface Require Import ClightConstantBoundModel ClightNestedConstantModel ClightNestedExpressionCapture
  ClightLoadedOffsetHeader ClightSignedIndexedOffsetHeader ClightCheckPlanFrame.
Import ListNotations.
Set Implicit Arguments.

(** Data supplied by a source proposer. The checker below binds the exact
    original AST, not a manually cached replacement supplied as the source. *)
Record nested_constant_shape := NestedConstantShape {
  ncs_row : ident; ncs_column : ident; ncs_iterator : ident;
  ncs_root_cache : ident; ncs_child_cache : ident;
  ncs_child_helper : ident; ncs_component_helper : ident;
  ncs_upper : Z; ncs_leaf : statement;
  ncs_pointer : ident; ncs_index : int; ncs_delta : int; ncs_child_delta : int
}.
Definition ncs_original shape := nested_expression_source(ncs_row shape)
  (signed_load_offset(ncs_pointer shape)(ncs_delta shape))(ncs_column shape)
  (signed_indexed_offset(ncs_pointer shape)(ncs_index shape)(ncs_child_delta shape))
  (constant_body_source(ncs_iterator shape)(Int.repr(ncs_upper shape))(ncs_leaf shape)).
Definition ncs_model shape := nested_constant_model_source(ncs_row shape)(ncs_root_cache shape)
  (ncs_column shape)(ncs_child_cache shape)(ncs_child_helper shape)(ncs_iterator shape)
  (ncs_component_helper shape)(ncs_upper shape)(ncs_leaf shape).
Definition ncs_nest shape := nested_constant_model_nest(ncs_row shape)(ncs_root_cache shape)
  (ncs_column shape)(ncs_child_cache shape)(ncs_child_helper shape)(ncs_iterator shape)
  (ncs_component_helper shape)(ncs_upper shape)(ncs_leaf shape)(AffineSourceLeaf(ncs_leaf shape)).
Definition ncs_component shape := AffineSourceAxis(ncs_iterator shape)(ncs_component_helper shape)
  (MemorySourceConstant(ncs_upper shape))(ncs_leaf shape)(AffineSourceLeaf(ncs_leaf shape)).
Definition ncs_coordinates shape := [ncs_row shape;ncs_column shape;ncs_iterator shape].
Definition ncs_helpers shape := [ncs_child_helper shape;ncs_component_helper shape].
Definition ncs_caches shape := [ncs_root_cache shape;ncs_child_cache shape].
Definition ncs_names shape := ncs_coordinates shape++ncs_caches shape++ncs_helpers shape.
Definition ncs_scope source live := statement_temps source++live.
Definition ncs_package_live source live shape := ncs_scope source live++ncs_helpers shape.
Definition ncs_ports source parameters live shape :=
  parameters++[ncs_row shape;ncs_root_cache shape]++ncs_package_live source live shape.
Definition ncs_stable source parameters live shape := filter
  (fun identifier=>negb(affine_ident_member_check identifier(ncs_coordinates shape)))
  (ncs_ports source parameters live shape).

Definition ncs_affine_expression_eq (first second:memory_source_affine) : {first=second}+{first<>second}.
Proof. decide equality; try apply peq; apply zeq. Defined.
Definition ncs_nest_eq (first second:affine_source_nest) : {first=second}+{first<>second}.
Proof. decide equality; try apply statement_eq; try apply ncs_affine_expression_eq; apply peq. Defined.
Definition ncs_private_check names scope := forallb(fun identifier=>negb(affine_ident_member_check identifier scope)) names.
Lemma ncs_private_check_sound names scope : ncs_private_check names scope=true ->
  forall identifier,In identifier names -> ~In identifier scope.
Proof.
  intros CHECK identifier MEMBER; apply forallb_forall with(x:=identifier) in CHECK; [|exact MEMBER].
  apply affine_ident_private_check_sound; apply negb_true_iff; exact CHECK.
Qed.

(** All fields below are produced by decidable checks or existing data-only
    checkers. No header, source execution, effect, or condition callback is an
    input to this factory. A complete guarded-candidate rule is a later stage. *)
Record nested_constant_site source parameters live proposal shape := NestedConstantSite {
  ncs_exact : source=ncs_original shape;
  ncs_original_unique : NoDup(ncs_names shape);
  ncs_cache_private : forall identifier,In identifier(ncs_caches shape) -> ~In identifier(ncs_scope source live);
  ncs_helper_private : forall identifier,In identifier(ncs_helpers shape) -> ~In identifier(ncs_scope source live++parameters);
  ncs_frameable : check_plan_frameable source=true;
  ncs_literal_positive : Int.lt Int.zero(Int.repr(ncs_upper shape))=true;
  ncs_cache_parameters : incl(ncs_caches shape) parameters;
  ncs_pointer_scope : incl(ncs_pointer shape::affine_proposed_pointers proposal)(ncs_scope source live);
  ncs_pointer_coordinates : forall identifier,In identifier(ncs_pointer shape::affine_proposed_pointers proposal) ->
    ~In identifier(ncs_coordinates shape);
  ncs_package : affine_guard_package(ncs_model shape) parameters(ncs_package_live source live shape) proposal;
  ncs_model_exact : affine_proposal_nest proposal=ncs_nest shape;
  ncs_scan_names : affine_scan_namespace(ncs_nest shape) parameters(ncs_ports source parameters live shape)
    (affine_proposal_rename proposal)(affine_proposed_result proposal);
  ncs_component_code : L.stmt;
  ncs_component_lower : affine_lower_nest(ncs_component shape)[ncs_row shape;ncs_column shape] parameters(L.Constant 0)
    (affine_checked_leaf_code(ncs_coordinates shape) parameters [](affine_proposed_operations proposal))=Some ncs_component_code
}.

Definition check_nested_constant_site source parameters live proposal shape :
  option(nested_constant_site source parameters live proposal shape).
Proof.
  destruct(statement_eq source(ncs_original shape)) as [EXACT|]; [|exact None].
  destruct(memory_identifiers_unique_check(ncs_names shape)) eqn:UNIQUE; [|exact None].
  destruct(ncs_private_check(ncs_caches shape)(ncs_scope source live)) eqn:CACHES; [|exact None].
  destruct(ncs_private_check(ncs_helpers shape)(ncs_scope source live++parameters)) eqn:HELPERS; [|exact None].
  destruct(check_plan_frameable source) eqn:FRAMEABLE; [|exact None].
  destruct(Int.lt Int.zero(Int.repr(ncs_upper shape))) eqn:LITERAL; [|exact None].
  destruct(affine_names_allocated_check(ncs_caches shape) parameters) eqn:PARAMETERS; [|exact None].
  destruct(affine_names_allocated_check(ncs_pointer shape::affine_proposed_pointers proposal)(ncs_scope source live)) eqn:POINTERS;
    [|exact None].
  destruct(ncs_private_check(ncs_pointer shape::affine_proposed_pointers proposal)(ncs_coordinates shape)) eqn:SEPARATION;
    [|exact None].
  destruct(check_affine_guard_package(ncs_model shape) parameters(ncs_package_live source live shape) proposal) as [package|];
    [|exact None].
  destruct(ncs_nest_eq(affine_proposal_nest proposal)(ncs_nest shape)) as [MODEL|]; [|exact None].
  destruct(check_affine_scan_namespace(ncs_nest shape) parameters(ncs_ports source parameters live shape)
    (affine_proposal_rename proposal)(affine_proposed_result proposal)) as [namespace|]; [|exact None].
  destruct(affine_lower_nest(ncs_component shape)[ncs_row shape;ncs_column shape] parameters(L.Constant 0)
    (affine_checked_leaf_code(ncs_coordinates shape) parameters [](affine_proposed_operations proposal))) as [code|] eqn:LOWER;
    [|exact None].
  exact(Some(@NestedConstantSite source parameters live proposal shape EXACT
    (@memory_identifiers_unique_check_sound _ UNIQUE)(@ncs_private_check_sound _ _ CACHES)
    (@ncs_private_check_sound _ _ HELPERS) FRAMEABLE LITERAL
    (@affine_names_allocated_check_sound _ _ PARAMETERS)(@affine_names_allocated_check_sound _ _ POINTERS)
    (@ncs_private_check_sound _ _ SEPARATION) package MODEL namespace code LOWER)).
Defined.

Print Assumptions ncs_private_check_sound.
Print Assumptions check_nested_constant_site.
