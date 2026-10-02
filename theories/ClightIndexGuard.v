From Stdlib Require Import Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import Values.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import AbstractGuard SemanticFacts ClightCondition ClightPureExpr.
Set Implicit Arguments.
Open Scope Z_scope.

Inductive index_atom := FirstNonnegative | FirstBelow | SecondNonnegative | SecondBelow | DistinctIndices.

Definition index_domain first second (s : clight_entry) :=
  exists x y, (entry_temps s) ! first = Some (Vint x) /\
    (entry_temps s) ! second = Some (Vint y).

Definition index_requirement count atom x y : Prop :=
  match atom with
  | FirstNonnegative => 0 <= x | FirstBelow => x < count
  | SecondNonnegative => 0 <= y | SecondBelow => y < count
  | DistinctIndices => x <> y end.

Definition index_flag count atom x y :=
  match atom with
  | FirstNonnegative => 0 <=? x | FirstBelow => x <? count
  | SecondNonnegative => 0 <=? y | SecondBelow => y <? count
  | DistinctIndices => negb (x =? y) end.

Lemma index_flag_spec count atom x y :
  index_flag count atom x y = true <-> index_requirement count atom x y.
Proof. destruct atom; cbn; rewrite ?Z.leb_le, ?Z.ltb_lt, ?negb_true_iff, ?Z.eqb_neq; tauto. Qed.

Definition index_property count first second atom (s : clight_entry) :=
  exists x y, (entry_temps s) ! first = Some (Vint x) /\
    (entry_temps s) ! second = Some (Vint y) /\
    index_requirement count atom (Int.signed x) (Int.signed y).

Definition index_decide count first second atom (s : clight_entry) : option bool :=
  match (entry_temps s) ! first, (entry_temps s) ! second with
  | Some (Vint x), Some (Vint y) => Some (index_flag count atom (Int.signed x) (Int.signed y))
  | _, _ => None end.

Definition index_dimension (count : Z) first second :
  property_dimension clight_entry index_atom (index_domain first second).
Proof.
  refine {| atom_property := index_property count first second;
            decide_atom := index_decide count first second |}.
  intros atom s result [x [y [X Y]]] CHECK.
  unfold index_decide in CHECK; rewrite X, Y in CHECK; inversion CHECK; subst result.
  destruct (index_flag count atom (Int.signed x) (Int.signed y)) eqn:FLAG;
    cbn [decision_evidence].
  - exists x, y; repeat split; auto. apply index_flag_spec; exact FLAG.
  - intros [x' [y' [X' [Y' PROPERTY]]]].
    assert (x' = x /\ y' = y) as [-> ->] by (split; congruence).
    apply index_flag_spec in PROPERTY; congruence.
Defined.

Definition index_temp id := Etempvar id type_int32s.
Definition index_check count first second atom :=
  match atom with
  | FirstNonnegative => Ebinop Ole (Econst_int Int.zero type_int32s) (index_temp first) type_int32s
  | FirstBelow => Ebinop Olt (index_temp first) (Econst_int (Int.repr count) type_int32s) type_int32s
  | SecondNonnegative => Ebinop Ole (Econst_int Int.zero type_int32s) (index_temp second) type_int32s
  | SecondBelow => Ebinop Olt (index_temp second) (Econst_int (Int.repr count) type_int32s) type_int32s
  | DistinctIndices => Ebinop One (index_temp first) (index_temp second) type_int32s end.

Lemma index_check_pure count first second atom : pure_scalar (index_check count first second atom).
Proof. destruct atom; repeat constructor. Qed.

Lemma integer_comparison_flags x y :
  Int.cmp Cle x y = (Int.signed x <=? Int.signed y) /\
  Int.lt x y = (Int.signed x <? Int.signed y) /\
  negb (Int.eq x y) = negb (Int.signed x =? Int.signed y).
Proof.
  assert (LT : forall a b, Int.lt a b = (Int.signed a <? Int.signed b)).
  { intros a b; unfold Int.lt; destruct (zlt (Int.signed a) (Int.signed b));
      symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia. }
  split.
  - change (negb (Int.lt y x) = (Int.signed x <=? Int.signed y)). rewrite LT.
    destruct (Int.signed y <? Int.signed x) eqn:REV; cbn.
    + apply Z.ltb_lt in REV; symmetry; apply Z.leb_gt; lia.
    + apply Z.ltb_ge in REV; symmetry; apply Z.leb_le; lia.
  - split; [apply LT |]. f_equal. rewrite Int.eq_signed.
    destruct (zeq (Int.signed x) (Int.signed y)); symmetry;
      [apply Z.eqb_eq | apply Z.eqb_neq]; assumption.
Qed.

Lemma index_check_run count first second atom s x y :
  Int.min_signed <= count <= Int.max_signed ->
  (entry_temps s) ! first = Some (Vint x) -> (entry_temps s) ! second = Some (Vint y) ->
  expression_test (index_check count first second atom) s
    (index_flag count atom (Int.signed x) (Int.signed y)).
Proof.
  intros COUNT X Y. destruct s as [ge e le m]; cbn in *.
  destruct (integer_comparison_flags Int.zero x) as [LOWX _].
  destruct (integer_comparison_flags Int.zero y) as [LOWY _].
  destruct (integer_comparison_flags x (Int.repr count)) as [_ [UPX _]].
  destruct (integer_comparison_flags y (Int.repr count)) as [_ [UPY _]].
  destruct (integer_comparison_flags x y) as [_ [_ NE]].
  change (Int.signed Int.zero) with 0 in LOWX, LOWY.
  rewrite Int.signed_repr in UPX, UPY by exact COUNT.
  unfold expression_test; exists (Val.of_bool (index_flag count atom (Int.signed x) (Int.signed y))).
  split.
  - destruct atom; cbn [index_check index_flag];
      eapply eval_Ebinop; try (constructor; eassumption); try constructor.
    + change (Some (Val.of_bool (Int.cmp Cle Int.zero x)) = Some (Val.of_bool (0 <=? Int.signed x))). rewrite LOWX; reflexivity.
    + change (Some (Val.of_bool (Int.lt x (Int.repr count))) = Some (Val.of_bool (Int.signed x <? count))). rewrite UPX; reflexivity.
    + change (Some (Val.of_bool (Int.cmp Cle Int.zero y)) = Some (Val.of_bool (0 <=? Int.signed y))). rewrite LOWY; reflexivity.
    + change (Some (Val.of_bool (Int.lt y (Int.repr count))) = Some (Val.of_bool (Int.signed y <? count))). rewrite UPY; reflexivity.
    + change (Some (Val.of_bool (negb (Int.eq x y))) = Some (Val.of_bool (negb (Int.signed x =? Int.signed y)))). rewrite NE; reflexivity.
  - destruct atom; cbn [index_check index_flag];
      destruct (0 <=? Int.signed x), (Int.signed x <? count),
        (0 <=? Int.signed y), (Int.signed y <? count),
        (negb (Int.signed x =? Int.signed y)); reflexivity.
Qed.

Definition index_primitives count first second (COUNT : Int.min_signed <= count <= Int.max_signed) :
  check_primitives decision_test_language (index_domain first second)
    (decide_atom (index_dimension count first second)).
Proof.
  refine (@CheckPrimitives clight_entry index_atom decision_test_language (index_domain first second)
    (decide_atom (index_dimension count first second)) (fun _ => Decision true)
    (fun atom => Test (index_check count first second atom) (Decision true) (Decision false)) _ _).
  - intros atom s result [x [y [X Y]]]. cbn [decision_test_language].
    unfold index_dimension; cbn [decide_atom]; unfold index_decide; rewrite X, Y.
    cbn [checked_valid]. split; intro RUN; [inversion RUN; reflexivity | subst; constructor].
  - intros atom s result expected [x [y [X Y]]] CHECK. cbn [decision_test_language].
    change (index_decide count first second atom s = Some expected) in CHECK.
    unfold index_decide in CHECK; rewrite X, Y in CHECK; inversion CHECK; subst expected.
    assert (RUN : decision_run s (Test (index_check count first second atom)
      (Decision true) (Decision false)) (index_flag count atom (Int.signed x) (Int.signed y))).
    { eapply run_test; [eapply index_check_run; eauto |].
      destruct (index_flag count atom (Int.signed x) (Int.signed y)); constructor. }
    split; [intro OTHER; eapply pure_tree_determinate; [constructor; [apply index_check_pure | constructor | constructor] | exact OTHER | exact RUN] |
            intro EQ; subst; exact RUN].
Defined.

Definition independent_indices : formula index_atom :=
  Conjunction (Fact FirstNonnegative) (Conjunction (Fact FirstBelow)
    (Conjunction (Fact SecondNonnegative) (Conjunction (Fact SecondBelow) (Fact DistinctIndices)))).

Definition independent_indices_flag count x y :=
  (0 <=? x) && ((x <? count) && ((0 <=? y) && ((y <? count) && negb (x =? y)))).

Lemma index_formula_execute count first second s x y :
  (entry_temps s) ! first = Some (Vint x) -> (entry_temps s) ! second = Some (Vint y) ->
  formula_execute (index_decide count first second) independent_indices s =
    Some (independent_indices_flag count (Int.signed x) (Int.signed y)).
Proof.
  intros X Y; unfold independent_indices; cbn [formula_execute].
  unfold index_decide; rewrite X, Y.
  unfold independent_indices_flag; cbn [index_flag].
  destruct (0 <=? Int.signed x), (Int.signed x <? count),
    (0 <=? Int.signed y), (Int.signed y <? count); reflexivity.
Qed.

Lemma independent_indices_property count first second s :
  formula_property (index_property count first second) independent_indices s ->
  exists x y, (entry_temps s) ! first = Some (Vint x) /\
    (entry_temps s) ! second = Some (Vint y) /\
    0 <= Int.signed x < count /\ 0 <= Int.signed y < count /\ Int.signed x <> Int.signed y.
Proof.
  cbn [formula_property independent_indices]; unfold index_property.
  intros [[x [y [X [Y LOWX]]]] [[x1 [y1 [X1 [Y1 UPX]]]]
    [[x2 [y2 [X2 [Y2 LOWY]]]] [[x3 [y3 [X3 [Y3 UPY]]]] [x4 [y4 [X4 [Y4 NE]]]]]]]].
  assert (x1 = x /\ y1 = y /\ x2 = x /\ y2 = y /\ x3 = x /\ y3 = y /\ x4 = x /\ y4 = y)
    as [-> [-> [-> [-> [-> [-> [-> ->]]]]]]] by (repeat split; congruence).
  exists x, y; repeat split; assumption.
Qed.

Print Assumptions index_primitives.
Print Assumptions independent_indices_property.

Example runtime_distinct_indices : independent_indices_flag 2 0 1 = true.
Proof. vm_compute; reflexivity. Qed.
Example runtime_reverse_indices : independent_indices_flag 2 1 0 = true.
Proof. vm_compute; reflexivity. Qed.
Example runtime_same_index_refused : independent_indices_flag 2 1 1 = false.
Proof. vm_compute; reflexivity. Qed.
Example runtime_negative_index_refused : independent_indices_flag 2 (-1) 1 = false.
Proof. vm_compute; reflexivity. Qed.
Example runtime_extent_refused : independent_indices_flag 2 0 2 = false.
Proof. vm_compute; reflexivity. Qed.
