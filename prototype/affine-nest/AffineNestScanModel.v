From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST.
From GuardMemory Require Import GuardMemoryBooleanScan GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation.
From GuardAffineNest Require Import AffineNestSyntax.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Finite traversal of the actual affine domain, including empty children.
    A leaf test receives the complete source valuation, never a box point. *)
Definition affine_scan_count lower upper := Z.to_nat(Z.max 0 (upper-lower)).
Lemma affine_scan_count_value lower upper :
  Z.of_nat(affine_scan_count lower upper)=Z.max 0 (upper-lower).
Proof. unfold affine_scan_count; rewrite Z2Nat.id; lia. Qed.

Fixpoint affine_scan_result nest valuation lower (test:(ident->Z)->bool) := match nest with
  | AffineSourceLeaf _=>test valuation
  | AffineSourceAxis iterator _ expression _ child=>
    memory_boolean_scan_result
      (fun value=>affine_scan_result child(memory_source_set_valuation valuation iterator value) 0 test)
      lower(affine_scan_count lower(memory_source_affine_math valuation expression)) end.

Inductive affine_scan_point : affine_source_nest -> (ident->Z) -> Z -> (ident->Z) -> Prop :=
  | affine_scan_leaf : forall source valuation lower, affine_scan_point(AffineSourceLeaf source) valuation lower valuation
  | affine_scan_axis : forall iterator bound expression body child valuation lower value point,
      lower<=value<memory_source_affine_math valuation expression ->
      affine_scan_point child(memory_source_set_valuation valuation iterator value) 0 point ->
      affine_scan_point(AffineSourceAxis iterator bound expression body child) valuation lower point.

Lemma affine_scan_result_points nest : forall valuation lower test,
  affine_scan_result nest valuation lower test=true <->
  forall point, affine_scan_point nest valuation lower point -> test point=true.
Proof.
  induction nest as [source|iterator bound expression body child IH]; intros valuation lower test.
  - cbn; split.
    + intros TEST point POINT; inversion POINT; subst; exact TEST.
    + intro ALL; apply ALL; constructor.
  - cbn [affine_scan_result]; rewrite memory_boolean_scan_member.
    split.
    + intros ALL point POINT; inversion POINT; subst.
      apply (proj1(IH (memory_source_set_valuation valuation iterator value) 0 test)).
      * apply ALL; rewrite affine_scan_count_value; lia.
      * assumption.
    + intros ALL value RANGE.
      rewrite affine_scan_count_value in RANGE.
      assert (ACTIVE:lower<=value<memory_source_affine_math valuation expression) by lia.
      apply (proj2(IH (memory_source_set_valuation valuation iterator value) 0 test)).
      intros point POINT; apply ALL; econstructor; eassumption.
Qed.

Lemma affine_scan_result_ext nest : forall first second valuation lower,
  (forall point, first point=second point) ->
  affine_scan_result nest valuation lower first=affine_scan_result nest valuation lower second.
Proof.
  induction nest; intros first second valuation lower SAME; cbn [affine_scan_result].
  - apply SAME.
  - apply memory_boolean_scan_ext; intro value; apply IHnest; exact SAME.
Qed.
Print Assumptions affine_scan_result_points.
