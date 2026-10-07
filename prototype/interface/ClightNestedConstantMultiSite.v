From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightTempFootprint.
From GuardAffineNest Require Import AffineNestGuardPackage AffineNestStaticPackage AffineNestMultiStaticPackage
  AffineNestAliasOnlyGuard AffineNestShadowTransport.
From GuardInterface Require Import ClightNestedConstantSite ClightNestedConstantPhysicalGuard
  ClightMaterializedCheck ClightSharedGuard.
Import ListNotations.
Set Implicit Arguments.

Definition ncs_multi_body source parameters live allocated proposal shape
  (site:nested_constant_site source parameters live proposal shape)
  (package:affine_multi_static_package(ncs_model shape) parameters(ncs_ports source parameters live shape) allocated proposal) :=
  Ssequence(ncs_physical_guard site)
    (Sifthenelse(shared_guard_choice(affine_proposed_result proposal))(affine_multi_alias_only_code package) Sskip).

Record ncs_multi_site source parameters live allocated proposal shape := NCSMultiSite {
  ncs_multi_original : nested_constant_site source parameters live proposal shape;
  ncs_multi_package : affine_multi_static_package(ncs_model shape) parameters(ncs_ports source parameters live shape) allocated proposal;
  ncs_multi_model_scope : statement_scope(ncs_ports source parameters live shape)(ncs_model shape);
  ncs_multi_test : materialized_check;
  ncs_multi_describe : describe_materialized_check(ncs_multi_body ncs_multi_original ncs_multi_package)
    (shared_guard_choice(affine_proposed_result proposal))=Some ncs_multi_test
}.

(** Compile-time data only. In particular, no source/model execution,
    future stability, alias, or candidate correctness callback is supplied. *)
Definition check_ncs_multi_site source parameters live allocated proposal shape :
  option(ncs_multi_site source parameters live allocated proposal shape).
Proof.
  destruct(check_nested_constant_site source parameters live proposal shape) as [site|]; [|exact None].
  destruct(check_affine_multi_static_package(ncs_model shape) parameters(ncs_ports source parameters live shape)
    allocated proposal) as [package|]; [|exact None].
  destruct(affine_statement_scope_check(ncs_ports source parameters live shape)(ncs_model shape)) eqn:SCOPE; [|exact None].
  destruct(describe_materialized_check(ncs_multi_body site package)(shared_guard_choice(affine_proposed_result proposal)))
    as [test|] eqn:TEST; [|exact None].
  exact(Some(@NCSMultiSite source parameters live allocated proposal shape site package
    (@affine_statement_scope_check_sound _ _ SCOPE) test TEST)).
Defined.

Print Assumptions check_ncs_multi_site.
