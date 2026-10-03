From Stdlib Require Import List Bool ZArith Lia.
From GuardMemory Require Import GuardMemoryBooleanScan GuardMemoryRectangularFootprint.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint memory_boolean_rectangle_result (test : list Z -> bool) counts prefix :=
  match counts with
  | [] => test prefix
  | count::rest => memory_boolean_scan_result
      (fun coordinate => memory_boolean_rectangle_result test rest (prefix++[coordinate]))
      0 (Z.to_nat count)
  end.

Lemma memory_boolean_rectangle_member test counts :
  Forall (fun count => 0 <= count) counts -> forall prefix,
  memory_boolean_rectangle_result test counts prefix = true <->
  forall suffix, Forall2 (fun coordinate count => 0 <= coordinate < count) suffix counts ->
    test (prefix++suffix) = true.
Proof.
  intro COUNTS; induction COUNTS as [|count counts NONNEG REST IH]; intro prefix.
  - cbn; split.
    + intros CHECK suffix RANGE; inversion RANGE; subst; rewrite app_nil_r; exact CHECK.
    + intro CHECK; specialize (CHECK [] ltac:(constructor)); rewrite app_nil_r in CHECK; exact CHECK.
  - cbn [memory_boolean_rectangle_result]; rewrite memory_boolean_scan_member.
    rewrite Z2Nat.id by exact NONNEG; split.
    + intros CHECK suffix RANGE.
      inversion RANGE as [|coordinate upper suffix_tail rest INDEX TAIL]; subst.
      specialize (CHECK coordinate ltac:(lia)); rewrite IH in CHECK.
      specialize (CHECK suffix_tail TAIL); rewrite <-app_assoc in CHECK; exact CHECK.
    + intros CHECK coordinate RANGE; rewrite IH; intros suffix SUFFIX.
      rewrite <-app_assoc; apply CHECK; constructor; [lia|exact SUFFIX].
Qed.

Theorem memory_boolean_rectangle_enumeration test counts prefix :
  Forall (fun count => 0 <= count) counts ->
  memory_boolean_rectangle_result test counts prefix =
    forallb test (memory_rectangular_points counts prefix).
Proof.
  intro COUNTS; apply Bool.eq_true_iff_eq.
  rewrite memory_boolean_rectangle_member by exact COUNTS; rewrite forallb_forall.
  split.
  - intros CHECK point MEMBER.
    apply memory_rectangular_points_member in MEMBER as [suffix [-> RANGE]]; apply CHECK; exact RANGE.
  - intros CHECK suffix RANGE; apply CHECK.
    apply memory_rectangular_points_member; exists suffix; auto.
Qed.
Print Assumptions memory_boolean_rectangle_enumeration.

Lemma memory_boolean_rectangle_prepend test counts fixed : forall prefix,
  memory_boolean_rectangle_result (fun coordinates => test (fixed++coordinates)) counts prefix =
    memory_boolean_rectangle_result test counts (fixed++prefix).
Proof.
  induction counts as [|count counts IH]; intro prefix; [reflexivity|].
  cbn [memory_boolean_rectangle_result]; apply memory_boolean_scan_ext; intro coordinate.
  rewrite IH,app_assoc; reflexivity.
Qed.
