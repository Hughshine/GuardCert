From Stdlib Require Import List Bool ZArith Lia.
From polcert.polygen Require Import InstrTy Loop.
From Guard Require Import PolCertLoopGuard PolCertParameterExtension.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma quotient_residual_exact numerator divisor quotient :
  0 < divisor ->
  (0 <= numerator-divisor*quotient <= divisor-1 <-> quotient=numerator/divisor).
Proof.
  intro POSITIVE.
  pose proof (Z.mod_pos_bound numerator divisor POSITIVE) as REMAINDER.
  pose proof (Z.div_mod numerator divisor ltac:(lia)) as DECOMPOSITION.
  split; intro FACT; [nia|subst quotient; nia].
Qed.

Module PolCertQuotientParameterFor (I : INSTR) (M : LOOP_MODEL I).
Module L := M.
Module Extension := PolCertParameterExtensionFor I M.
Module Choice := PolCertLoopGuardFor I M.
Definition quotient_residual numerator divisor :=
  L.Sum (Extension.lift_expression 0 numerator) (L.Mult (-divisor) (L.Var 0)).
Definition quotient_relation numerator divisor :=
  L.And (L.LE (L.Constant 0) (quotient_residual numerator divisor))
    (L.LE (quotient_residual numerator divisor) (L.Constant (divisor-1))).
Lemma quotient_relation_exact numerator divisor environment quotient :
  0 < divisor ->
  (L.eval_test (quotient::environment) (quotient_relation numerator divisor)=true <->
   quotient=L.eval_expr environment numerator/divisor).
Proof.
  intro POSITIVE.
  change ((0 <=? L.eval_expr (quotient::environment) (Extension.lift_expression 0 numerator)+
      (-divisor)*quotient) &&
    (L.eval_expr (quotient::environment) (Extension.lift_expression 0 numerator)+
      (-divisor)*quotient <=? divisor-1)=true <->
    quotient=L.eval_expr environment numerator/divisor).
  pose proof (@Extension.lift_expression_exact numerator [] environment quotient) as LIFT.
  cbn [length app] in LIFT; rewrite LIFT.
  rewrite andb_true_iff, !Z.leb_le.
  rewrite <- quotient_residual_exact by exact POSITIVE; lia.
Qed.
Definition extended_assumed_source numerator divisor source :=
  L.Guard (quotient_relation numerator divisor) (Extension.lift_statement 0 source).
Theorem extended_assumed_source_execution numerator divisor source environment quotient before after :
  0 < divisor -> quotient=L.eval_expr environment numerator/divisor ->
  (L.loop_semantics (extended_assumed_source numerator divisor source)
     (quotient::environment) before after <->
   L.loop_semantics source environment before after).
Proof.
  intros POSITIVE VALUE; unfold extended_assumed_source.
  rewrite Choice.guard_execution.
  rewrite (proj2 (@quotient_relation_exact numerator divisor environment quotient POSITIVE) VALUE).
  apply Extension.parameter_extension_exact.
Qed.
End PolCertQuotientParameterFor.

Print Assumptions quotient_residual_exact.
