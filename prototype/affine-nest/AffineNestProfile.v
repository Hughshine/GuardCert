From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Integers Coqlib.
From compcert.common Require Import AST.
From Guard Require Import ClightCountedLoop.
From GuardMemory Require Import GuardMemoryArrayBackend GuardMemoryLoops GuardMemoryIntervalBox
  GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation.
From GuardAffineNest Require Import AffineNestSyntax AffineNestLoopEncoding AffineNestBoundEncoding
  AffineNestValuation AffineNestMathDomain.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition affine_profile_interval (range : Z*Z) := MemoryNested.A.Interval (fst range) (snd range-1).
Definition affine_signed_range_check value := (Int.min_signed<=?value)&&(value<=?Int.max_signed).
Lemma affine_signed_range_check_sound value : affine_signed_range_check value=true -> signed_range value.
Proof. unfold affine_signed_range_check,signed_range; rewrite andb_true_iff,!Z.leb_le; tauto. Qed.

Lemma affine_profile_ranges_within bounds values : interval_ranges bounds values ->
  MemoryNested.A.env_within (map affine_profile_interval bounds) values.
Proof.
  intro RANGES; induction RANGES; cbn [map].
  - intros index bound LOOKUP; destruct index; discriminate.
  - apply MemoryNested.A.env_within_cons; [|exact IHRANGES].
    destruct x as [lower upper]; unfold affine_profile_interval,MemoryNested.A.contains;
      cbn in *; lia.
Qed.

Definition affine_range_eq_dec : forall first second : Z*Z, {first=second}+{first<>second}.
Proof. decide equality; apply Z.eq_dec. Defined.

Definition affine_child_profile_start_check child (remaining : list(Z*Z)) := match child,remaining with
  | AffineSourceLeaf _,_ => true
  | AffineSourceAxis _ _ _ _ _,(floor,_)::_ => floor<=?0
  | _,_ => false end.

(** All interval profiles are untrusted proposals. Every bound is checked
    against the actual reversed coordinate prefix before its own coordinate
    is introduced. Leaf layout and leaf box must match the entire payload. *)
Fixpoint check_affine_math_profile nest (prefix parameters : list ident)
  (prefix_ranges parameter_ranges axis_ranges leaf_bounds : list(Z*Z)) (leaf_layout : list ident) :=
  match nest with
  | AffineSourceLeaf _ => match axis_ranges with
      | [] => if list_eq_dec peq leaf_layout (prefix++parameters) then
          if list_eq_dec affine_range_eq_dec leaf_bounds (prefix_ranges++parameter_ranges)
          then true else false else false
      | _ => false end
  | AffineSourceAxis iterator _ expression _ child => match axis_ranges with
      | (floor,cap)::remaining =>
          affine_signed_range_check floor && affine_signed_range_check cap && (floor<?cap) &&
          check_affine_bound_cap (rev prefix++parameters)
            (map affine_profile_interval (rev prefix_ranges++parameter_ranges)) expression cap &&
          affine_child_profile_start_check child remaining &&
          check_affine_math_profile child (prefix++[iterator]) parameters
            (prefix_ranges++[(floor,cap)]) parameter_ranges remaining leaf_bounds leaf_layout
      | [] => false end end.

Theorem affine_checked_math_bound layout bounds expression cap valuation :
  check_affine_bound_cap layout bounds expression cap=true ->
  MemoryNested.A.env_within bounds (map valuation layout) ->
  signed_range(memory_source_affine_math valuation expression) /\
  memory_source_affine_math valuation expression<=cap.
Proof.
  unfold check_affine_bound_cap.
  destruct(affine_loop_expression layout expression) as [encoded|] eqn:ENCODE; [|discriminate].
  destruct(MemoryNested.A.analyze bounds encoded) as [interval|] eqn:ANALYZE; [|discriminate].
  intros CAP VIEW; apply Z.leb_le in CAP.
  destruct(@MemoryNested.A.analyze_sound encoded bounds interval (map valuation layout) ANALYZE VIEW)
    as [CONTAINS SAFE].
  pose proof(@MemoryNested.A.affine_safe_range encoded (map valuation layout) SAFE) as RANGE.
  pose proof(@affine_loop_expression_value expression layout encoded valuation ENCODE) as VALUE.
  split.
  - unfold signed_range; rewrite <-VALUE; exact RANGE.
  - rewrite <-VALUE; eapply Z.le_trans; [exact(proj2 CONTAINS)|exact CAP].
Qed.
Print Assumptions affine_checked_math_bound.
Print Assumptions check_affine_math_profile.
