From Stdlib Require Import ZArith List Lia.
From polcert.lib Require Import Linalg ImpureAlarmConfig.
From polcert.polygen Require Import Projection Canonizer.
From Vpl Require Import Impure.
Local Open Scope Z_scope.

(** Reduce explicit equalities before forming Fourier--Motzkin pairs. This is
    a domain service: its contract is the existing scaled exact projection,
    not an integer quantifier-elimination or machine-check safety claim. *)
Module EqualityReducedProject (Import Imp : FullImpureMonad)
  (Canon : PolyCanonizer Imp) <: ProjectOperator Imp.
  Module FM := FourierMotzkinProject Imp.
  Module Simplifier := PolyProjectImpl Imp Canon FM.

  Definition reduce n pol := Simplifier.simplify_poly (S n) pol.
  Definition pure_project n pol := FM.pure_project n (reduce n pol).
  Definition project (np : nat * polyhedron) :=
    pure (pure_project (fst np) (snd np)).

  Lemma reduce_scaled_exact n pol p scale :
    0 < scale ->
    in_poly p (expand_poly scale (reduce n pol)) =
    in_poly p (expand_poly scale pol).
  Proof. unfold reduce; apply Simplifier.simplify_poly_correct. Qed.

  Lemma pure_project_exact n pol :
    isExactProjection n pol (pure_project n pol).
  Proof.
    intros p scale POSITIVE; unfold pure_project.
    rewrite (FM.pure_project_in_iff n (reduce n pol) p scale POSITIVE).
    split.
    - intros [factor [value [FACTOR MEMBER]]].
      exists factor, value; split; [exact FACTOR|].
      rewrite reduce_scaled_exact in MEMBER by nia; exact MEMBER.
    - intros [factor [value [FACTOR MEMBER]]].
      exists factor, value; split; [exact FACTOR|].
      rewrite reduce_scaled_exact by nia; exact MEMBER.
  Qed.

  Theorem project_projected :
    forall n pol, WHEN projected <- project (n, pol) THEN absent_var projected n.
  Proof.
    intros n pol projected RUN; unfold project in RUN.
    apply mayReturn_pure in RUN; subst projected.
    unfold pure_project, absent_var; intros c MEMBER.
    eapply FM.pure_project_projected; exact MEMBER.
  Qed.

  Theorem project_no_new_var :
    forall n k pol, absent_var pol k ->
    WHEN projected <- project (n, pol) THEN absent_var projected k.
  Proof.
    intros n k pol ABSENT projected RUN; unfold project in RUN.
    apply mayReturn_pure in RUN; subst projected; unfold pure_project.
    pose proof (Simplifier.simplify_poly_preserve_zeros (S n) k pol ABSENT) as REDUCED.
    exact (FM.pure_project_no_new_var n k (reduce n pol) REDUCED).
  Qed.

  Theorem project_in_iff :
    forall n pol, WHEN projected <- project (n, pol) THEN
      isExactProjection n pol projected.
  Proof.
    intros n pol projected RUN; unfold project in RUN.
    apply mayReturn_pure in RUN; subst projected; apply pure_project_exact.
  Qed.
End EqualityReducedProject.

Module EqualityReducedOperator := EqualityReducedProject CoreAlarmed Canon.
Module EqualityReducedPolyProject :=
  PolyProjectImpl CoreAlarmed Canon EqualityReducedOperator.

Print Assumptions EqualityReducedOperator.reduce_scaled_exact.
Print Assumptions EqualityReducedOperator.pure_project_exact.
Print Assumptions EqualityReducedOperator.project_projected.
Print Assumptions EqualityReducedOperator.project_no_new_var.
Print Assumptions EqualityReducedOperator.project_in_iff.
