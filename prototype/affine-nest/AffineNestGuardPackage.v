From Stdlib Require Import List ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightSyntaxEquality.
From GuardMemory Require Import GuardMemoryNaryCompute GuardMemoryAffineSourceExpressions GuardMemoryAffineAxisRenaming GuardMemoryRecursiveSyntax.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestLeafModel AffineNestProfile
  AffineNestGuardParameterCheck AffineNestNumericGuard AffineNestNamespace.
Import ListNotations.
Set Implicit Arguments.

(** The proposal carries syntax, interval data and a finite private-name list.
    It carries no semantic correctness callback or trusted guard encoder. *)
Record affine_guard_proposal := AffineGuardProposal {
  affine_proposed_iterator : ident;
  affine_proposed_bound : ident;
  affine_proposed_body : statement;
  affine_proposed_child : affine_source_nest;
  affine_proposed_leaf_bounds : list(Z*Z);
  affine_proposed_window_lower : Z;
  affine_proposed_window_upper : Z;
  affine_proposed_pointers : list ident;
  affine_proposed_operations : list memory_nary_compute;
  affine_proposed_parameter_ranges : list(Z*Z);
  affine_proposed_floor : Z;
  affine_proposed_cap : Z;
  affine_proposed_remaining : list(Z*Z);
  affine_proposed_private_controls : list ident;
  affine_proposed_result : ident
}.
Definition affine_proposal_nest proposal := AffineSourceAxis(affine_proposed_iterator proposal)(affine_proposed_bound proposal)
  (MemorySourceTemp(affine_proposed_bound proposal))(affine_proposed_body proposal)(affine_proposed_child proposal).
Definition affine_proposal_layout proposal parameters := affine_nest_iterators(affine_proposal_nest proposal)++parameters.
Definition affine_proposal_rename proposal := memory_affine_axis_rename
  (affine_nest_controls(affine_proposal_nest proposal))(affine_proposed_private_controls proposal).

Record affine_guard_package source parameters live proposal := AffineGuardPackage {
  affine_package_description : affine_nest_description source parameters;
  affine_package_nest : described_affine_nest affine_package_description=affine_proposal_nest proposal;
  affine_package_leaf : affine_leaf_certificate(affine_nest_leaf(affine_proposal_nest proposal))
    (affine_proposed_leaf_bounds proposal)(affine_proposed_window_lower proposal)(affine_proposed_window_upper proposal)
    (affine_proposal_layout proposal parameters) [](affine_proposed_pointers proposal)(affine_proposed_operations proposal);
  affine_package_used : check_affine_guard_parameters(affine_proposal_nest proposal)(affine_proposal_layout proposal parameters)
    [](affine_proposed_operations proposal) parameters=true;
  affine_package_profile : check_affine_math_profile(affine_proposal_nest proposal) [] parameters []
    (affine_proposed_parameter_ranges proposal)((affine_proposed_floor proposal,affine_proposed_cap proposal)::affine_proposed_remaining proposal)
    (affine_proposed_leaf_bounds proposal)(affine_proposal_layout proposal parameters)=true;
  affine_package_parameter_intervals : affine_parameter_intervals_check(affine_proposed_parameter_ranges proposal)=true;
  affine_package_namespace : affine_guard_namespace(affine_proposed_iterator proposal)(affine_proposed_bound proposal)
    (MemorySourceTemp(affine_proposed_bound proposal))(affine_proposed_body proposal)(affine_proposed_child proposal)
    parameters live(affine_proposal_rename proposal)(affine_proposed_result proposal)
}.

Definition check_affine_guard_package source parameters live proposal : option(affine_guard_package source parameters live proposal).
Proof.
  destruct(check_affine_nest_full source parameters(affine_proposal_nest proposal)) as [[description NEST]|]; [|exact None].
  destruct(check_affine_leaf(affine_nest_leaf(affine_proposal_nest proposal))(affine_proposed_leaf_bounds proposal)
    (affine_proposed_window_lower proposal)(affine_proposed_window_upper proposal)(affine_proposal_layout proposal parameters) []
    (affine_proposed_pointers proposal)(affine_proposed_operations proposal)) as [leaf|]; [|exact None].
  destruct(check_affine_guard_parameters(affine_proposal_nest proposal)(affine_proposal_layout proposal parameters)
    [](affine_proposed_operations proposal) parameters) eqn:USED; [|exact None].
  destruct(check_affine_math_profile(affine_proposal_nest proposal) [] parameters [] (affine_proposed_parameter_ranges proposal)
    ((affine_proposed_floor proposal,affine_proposed_cap proposal)::affine_proposed_remaining proposal)
    (affine_proposed_leaf_bounds proposal)(affine_proposal_layout proposal parameters)) eqn:PROFILE; [|exact None].
  destruct(affine_parameter_intervals_check(affine_proposed_parameter_ranges proposal)) eqn:INTERVALS; [|exact None].
  destruct(check_affine_guard_namespace(affine_proposed_iterator proposal)(affine_proposed_bound proposal)
    (MemorySourceTemp(affine_proposed_bound proposal))(affine_proposed_body proposal)(affine_proposed_child proposal)
    parameters live(affine_proposal_rename proposal)(affine_proposed_result proposal)) as [namespace|]; [|exact None].
  exact(Some(@AffineGuardPackage source parameters live proposal description NEST leaf USED PROFILE INTERVALS namespace)).
Defined.
Print Assumptions check_affine_guard_package.
