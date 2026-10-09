From Stdlib Require Import List Bool ZArith Lia.
From polcert.polygen Require Import InstrTy Loop.
From Guard Require Import PolCertLoopGuard.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Exact predicate encoding above the semantic kernel. Clearing a positive
    constant divisor avoids division in the resulting test. Concrete machine
    lowering must still check the arithmetic ranges and parameter bindings. *)
Lemma floor_le_cleared numerator divisor point :
  0 < divisor ->
  (numerator / divisor <= point <-> numerator <= divisor * (point + 1) - 1).
Proof.
  intro POSITIVE.
  pose proof (Z.mod_pos_bound numerator divisor POSITIVE) as REMAINDER.
  pose proof (Z.div_mod numerator divisor ltac:(lia)) as DECOMPOSITION.
  split; intro BOUND; nia.
Qed.
Lemma lt_floor_cleared numerator divisor point :
  0 < divisor ->
  (point < numerator / divisor <-> divisor * (point + 1) <= numerator).
Proof.
  intro POSITIVE.
  pose proof (Z.mod_pos_bound numerator divisor POSITIVE) as REMAINDER.
  pose proof (Z.div_mod numerator divisor ltac:(lia)) as DECOMPOSITION.
  split; intro BOUND; nia.
Qed.

Module PolCertFloorMembershipFor (I : INSTR) (M : LOOP_MODEL I).
Module L := M.
Fixpoint affine_expression expression :=
  match expression with
  | L.Constant _ | L.Var _ => true
  | L.Sum a b => affine_expression a && affine_expression b
  | L.Mult _ a => affine_expression a
  | _ => false end.
Definition conjunction left right :=
  match left,right with Some a,Some b => Some (L.And a b) | _,_ => None end.
Definition plus_one expression := L.Sum expression (L.Constant 1).
Definition minus_constant expression value := L.Sum expression (L.Constant (-value)).

Fixpoint lower_membership bound point : option L.test :=
  if affine_expression bound && affine_expression point then Some (L.LE bound point)
  else match bound with
  | L.Max a b => conjunction (lower_membership a point) (lower_membership b point)
  | L.Div numerator divisor =>
      if (0 <? divisor) && affine_expression numerator && affine_expression point then
        Some (L.LE numerator (L.Sum (L.Mult divisor (plus_one point)) (L.Constant (-1))))
      else None
  | L.Sum a (L.Constant value) => lower_membership a (minus_constant point value)
  | _ => None end.
Fixpoint upper_membership point bound : option L.test :=
  if affine_expression bound && affine_expression point then Some (L.LE (plus_one point) bound)
  else match bound with
  | L.Min a b => conjunction (upper_membership point a) (upper_membership point b)
  | L.Div numerator divisor =>
      if (0 <? divisor) && affine_expression numerator && affine_expression point then
        Some (L.LE (L.Mult divisor (plus_one point)) numerator)
      else None
  | L.Sum a (L.Constant value) => upper_membership (minus_constant point value) a
  | _ => None end.

Lemma lower_membership_correct bound : forall point test parameters,
  lower_membership bound point = Some test ->
  (L.eval_test parameters test = true <-> L.eval_expr parameters bound <= L.eval_expr parameters point).
Proof.
  induction bound; intros point test parameters GENERATED;
    cbn [lower_membership] in GENERATED;
    destruct (affine_expression _ && affine_expression point) eqn:AFFINE;
    try (inversion GENERATED; subst; cbn [L.eval_test]; rewrite Z.leb_le; reflexivity);
    try discriminate.
  - destruct bound2; try discriminate.
    rewrite (IHbound1 (minus_constant point z) test parameters GENERATED).
    cbn [minus_constant L.eval_expr]; lia.
  - destruct ((0 <? z) && affine_expression bound && affine_expression point) eqn:DOMAIN;
      try discriminate.
    apply andb_true_iff in DOMAIN as [DOMAIN _]; apply andb_true_iff in DOMAIN as [POSITIVE _].
    apply Z.ltb_lt in POSITIVE; inversion GENERATED; subst.
    cbn [L.eval_test L.eval_expr plus_one]. rewrite Z.leb_le.
    rewrite floor_le_cleared by exact POSITIVE; lia.
  - unfold conjunction in GENERATED.
    destruct (lower_membership bound1 point) as [left|] eqn:LEFT; try discriminate.
    destruct (lower_membership bound2 point) as [right|] eqn:RIGHT; try discriminate.
    inversion GENERATED; subst. cbn [L.eval_test L.eval_expr].
    rewrite andb_true_iff, (IHbound1 _ _ _ LEFT), (IHbound2 _ _ _ RIGHT).
    symmetry; apply Z.max_lub_iff.
Qed.
Lemma upper_membership_correct bound : forall point test parameters,
  upper_membership point bound = Some test ->
  (L.eval_test parameters test = true <-> L.eval_expr parameters point < L.eval_expr parameters bound).
Proof.
  induction bound; intros point test parameters GENERATED;
    cbn [upper_membership] in GENERATED;
    destruct (affine_expression _ && affine_expression point) eqn:AFFINE;
    try (inversion GENERATED; subst; cbn [L.eval_test L.eval_expr plus_one]; rewrite Z.leb_le; lia);
    try discriminate.
  - destruct bound2; try discriminate.
    rewrite (IHbound1 (minus_constant point z) test parameters GENERATED).
    cbn [minus_constant L.eval_expr]; lia.
  - destruct ((0 <? z) && affine_expression bound && affine_expression point) eqn:DOMAIN;
      try discriminate.
    apply andb_true_iff in DOMAIN as [DOMAIN _]; apply andb_true_iff in DOMAIN as [POSITIVE _].
    apply Z.ltb_lt in POSITIVE; inversion GENERATED; subst.
    cbn [L.eval_test L.eval_expr plus_one]. rewrite Z.leb_le.
    rewrite lt_floor_cleared by exact POSITIVE; reflexivity.
  - unfold conjunction in GENERATED.
    destruct (upper_membership point bound1) as [left|] eqn:LEFT; try discriminate.
    destruct (upper_membership point bound2) as [right|] eqn:RIGHT; try discriminate.
    inversion GENERATED; subst. cbn [L.eval_test L.eval_expr].
    rewrite andb_true_iff, (IHbound1 _ _ _ LEFT), (IHbound2 _ _ _ RIGHT).
    destruct (Z.min_spec (L.eval_expr parameters bound1) (L.eval_expr parameters bound2))
      as [[ORDER VALUE]|[ORDER VALUE]]; rewrite VALUE; lia.
Qed.
End PolCertFloorMembershipFor.

Print Assumptions floor_le_cleared.
Print Assumptions lt_floor_cleared.
