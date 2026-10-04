From Stdlib Require Import List Arith.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightPrivateRegion.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestGuardPackage AffineNestCheckedCompiler.
Import ListNotations PrivateRegion.
Set Implicit Arguments.

(** This data-only wrapper reserves two private copies of all source controls.
    It supplies no semantic evidence; the multi-source checker verifies names. *)
Definition affine_reserve_multi_scans (describe:affine_source_proposer) : affine_source_proposer :=
  fun live pool source=>match describe live pool source with
  | None=>None
  | Some(parameters,proposal)=>match affine_proposed_pointers proposal with
    | _::_::_=>match nth_error(var_names pool)(2*length(affine_nest_controls(affine_proposal_nest proposal))) with
      | None=>None
      | Some result=>Some(parameters,
          AffineGuardProposal(affine_proposed_iterator proposal)(affine_proposed_bound proposal)
            (affine_proposed_body proposal)(affine_proposed_child proposal)(affine_proposed_leaf_bounds proposal)
            (affine_proposed_window_lower proposal)(affine_proposed_window_upper proposal)
            (affine_proposed_pointers proposal)(affine_proposed_operations proposal)
            (affine_proposed_parameter_ranges proposal)(affine_proposed_floor proposal)(affine_proposed_cap proposal)
            (affine_proposed_remaining proposal)(affine_proposed_private_controls proposal) result)
      end
    | _=>Some(parameters,proposal) end end.
Print Assumptions affine_reserve_multi_scans.
