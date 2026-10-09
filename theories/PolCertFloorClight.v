From Stdlib Require Import List Bool ZArith.
From polcert.polygen Require Import InstrTy Loop.
From Guard Require Import PolCertLoopGuard PolCertFloorMembership PolCertAffineClight
  ClightCondition ClightPureExpr.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A Clight realization of the predicate service. Successful construction is
    distinct from safe invocation: callers must supply a typed parameter view
    and values within the checked intervals. No public or private state changes
    are needed to evaluate these conditions. *)
Module PolCertFloorClightFor (I : INSTR) (M : LOOP_MODEL I).
Module L := M.
Module Predicate := PolCertFloorMembershipFor I M.
Module Machine := PolCertAffineClightFor I M.

Definition lower_bound layout ranges bound point :=
  match Predicate.lower_membership bound point with
  | Some test => Machine.lower_test layout ranges test
  | None => None end.
Definition upper_bound layout ranges point bound :=
  match Predicate.upper_membership point bound with
  | Some test => Machine.lower_test layout ranges test
  | None => None end.

Lemma lower_predicate_boolean bound point test parameters :
  Predicate.lower_membership bound point = Some test ->
  L.eval_test parameters test =
    (L.eval_expr parameters bound <=? L.eval_expr parameters point).
Proof.
  intro GENERATED. apply eq_true_iff_eq.
  rewrite (@Predicate.lower_membership_correct bound point test parameters GENERATED), Z.leb_le.
  reflexivity.
Qed.
Lemma upper_predicate_boolean bound point test parameters :
  Predicate.upper_membership point bound = Some test ->
  L.eval_test parameters test =
    (L.eval_expr parameters point <? L.eval_expr parameters bound).
Proof.
  intro GENERATED. apply eq_true_iff_eq.
  rewrite (@Predicate.upper_membership_correct bound point test parameters GENERATED), Z.ltb_lt.
  reflexivity.
Qed.

Theorem lower_bound_exact layout ranges bound point tree parameters ge locals temps memory result :
  lower_bound layout ranges bound point = Some tree ->
  Machine.env_within ranges parameters -> Machine.typed_view layout parameters temps ->
  (decision_run (Entry ge locals temps memory) tree result <->
   result = (L.eval_expr parameters bound <=? L.eval_expr parameters point)).
Proof.
  unfold lower_bound.
  destruct (Predicate.lower_membership bound point) as [test|] eqn:GENERATED;
    try discriminate.
  intros LOWER RANGE VIEW.
  rewrite (@Machine.lower_test_exact test layout ranges tree parameters temps ge locals memory result
    LOWER RANGE VIEW), (@lower_predicate_boolean bound point test parameters GENERATED).
  reflexivity.
Qed.
Theorem upper_bound_exact layout ranges point bound tree parameters ge locals temps memory result :
  upper_bound layout ranges point bound = Some tree ->
  Machine.env_within ranges parameters -> Machine.typed_view layout parameters temps ->
  (decision_run (Entry ge locals temps memory) tree result <->
   result = (L.eval_expr parameters point <? L.eval_expr parameters bound)).
Proof.
  unfold upper_bound.
  destruct (Predicate.upper_membership point bound) as [test|] eqn:GENERATED;
    try discriminate.
  intros LOWER RANGE VIEW.
  rewrite (@Machine.lower_test_exact test layout ranges tree parameters temps ge locals memory result
    LOWER RANGE VIEW), (@upper_predicate_boolean bound point test parameters GENERATED).
  reflexivity.
Qed.

Lemma lower_bound_pure layout ranges bound point tree :
  lower_bound layout ranges bound point = Some tree -> pure_tree tree.
Proof.
  unfold lower_bound.
  destruct (Predicate.lower_membership bound point); try discriminate.
  eapply Machine.lower_test_pure.
Qed.
Lemma upper_bound_pure layout ranges point bound tree :
  upper_bound layout ranges point bound = Some tree -> pure_tree tree.
Proof.
  unfold upper_bound.
  destruct (Predicate.upper_membership point bound); try discriminate.
  eapply Machine.lower_test_pure.
Qed.
End PolCertFloorClightFor.
