From Stdlib Require Import Bool ZArith Lia.
From compcert.lib Require Import Integers Coqlib.
From compcert.common Require Import Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightCondition ClightPureExpr.
Open Scope Z_scope.
Set Implicit Arguments.

(** Wider arithmetic computes each guard only after its operands are known
    to fit signed32. Signed32 addition and multiplication then fit signed64. *)
Definition wide_type := Tlong Signed noattr.
Definition word_range z := Int.min_signed <= z <= Int.max_signed.
Definition long_range z := Int64.min_signed <= z <= Int64.max_signed.
Definition widen a := Ecast a wide_type.
Definition wide_add a b := Ebinop Oadd (widen a) (widen b) wide_type.
Definition wide_mul a b := Ebinop Omul (widen a) (widen b) wide_type.

Lemma word_is_long z : word_range z -> long_range z.
Proof.
  unfold word_range, long_range.
  change (-2147483648 <= z <= 2147483647 -> -9223372036854775808 <= z <= 9223372036854775807).
  lia.
Qed.

Lemma word_sum_is_long x y : word_range x -> word_range y -> long_range (x + y).
Proof.
  unfold word_range, long_range.
  change (-2147483648 <= x <= 2147483647 -> -2147483648 <= y <= 2147483647 ->
    -9223372036854775808 <= x + y <= 9223372036854775807).
  lia.
Qed.

Lemma word_product_is_long x y : word_range x -> word_range y -> long_range (x * y).
Proof.
  unfold word_range, long_range.
  change (-2147483648 <= x <= 2147483647 -> -2147483648 <= y <= 2147483647 ->
    -9223372036854775808 <= x * y <= 9223372036854775807).
  intros X Y; nia.
Qed.

Lemma widen_eval ge locals le m a z : typeof a = type_int32s -> word_range z ->
  eval_expr ge locals le m a (Vint (Int.repr z)) ->
  eval_expr ge locals le m (widen a) (Vlong (Int64.repr z)).
Proof.
  intros TYPE RANGE RUN. eapply eval_Ecast; [exact RUN |].
  rewrite TYPE. change (Some (Vlong (Int64.repr (Int.signed (Int.repr z)))) =
    Some (Vlong (Int64.repr z))).
  rewrite Int.signed_repr by exact RANGE; reflexivity.
Qed.

Lemma wide_add_eval ge locals le m a b x y :
  typeof a = type_int32s -> typeof b = type_int32s -> word_range x -> word_range y ->
  eval_expr ge locals le m a (Vint (Int.repr x)) ->
  eval_expr ge locals le m b (Vint (Int.repr y)) ->
  eval_expr ge locals le m (wide_add a b) (Vlong (Int64.repr (x + y))).
Proof.
  intros TA TB RX RY A B. eapply eval_Ebinop.
  - eapply widen_eval with (z := x); eauto.
  - eapply widen_eval with (z := y); eauto.
  -
  change (Some (Vlong (Int64.add (Int64.repr x) (Int64.repr y))) =
    Some (Vlong (Int64.repr (x + y)))).
  rewrite Int64.add_signed, (Int64.signed_repr x (@word_is_long x RX)),
    (Int64.signed_repr y (@word_is_long y RY)); reflexivity.
Qed.

Lemma wide_mul_eval ge locals le m a b x y :
  typeof a = type_int32s -> typeof b = type_int32s -> word_range x -> word_range y ->
  eval_expr ge locals le m a (Vint (Int.repr x)) ->
  eval_expr ge locals le m b (Vint (Int.repr y)) ->
  eval_expr ge locals le m (wide_mul a b) (Vlong (Int64.repr (x * y))).
Proof.
  intros TA TB RX RY A B. eapply eval_Ebinop.
  - eapply widen_eval with (z := x); eauto.
  - eapply widen_eval with (z := y); eauto.
  -
  change (Some (Vlong (Int64.mul (Int64.repr x) (Int64.repr y))) =
    Some (Vlong (Int64.repr (x * y)))).
  rewrite Int64.mul_signed, (Int64.signed_repr x (@word_is_long x RX)),
    (Int64.signed_repr y (@word_is_long y RY)); reflexivity.
Qed.

Lemma long_le_exact x y : long_range x -> long_range y ->
  Int64.cmp Cle (Int64.repr x) (Int64.repr y) = (x <=? y).
Proof.
  intros RX RY. unfold Int64.cmp, Int64.lt.
  rewrite !Int64.signed_repr by assumption.
  destruct (zlt y x); simpl; symmetry.
  - apply Z.leb_gt; auto.
  - apply Z.leb_le; lia.
Qed.

Lemma long_le_test ge locals le m a b x y :
  typeof a = wide_type -> typeof b = wide_type -> long_range x -> long_range y ->
  eval_expr ge locals le m a (Vlong (Int64.repr x)) ->
  eval_expr ge locals le m b (Vlong (Int64.repr y)) ->
  expression_test (Ebinop Ole a b type_int32s) (Entry ge locals le m) (x <=? y).
Proof.
  intros TA TB RX RY A B. unfold expression_test.
  exists (Val.of_bool (x <=? y)); split.
  - eapply eval_Ebinop; [exact A | exact B |].
    rewrite TA, TB. change (Some (Val.of_bool (Int64.cmp Cle (Int64.repr x) (Int64.repr y))) =
      Some (Val.of_bool (x <=? y))).
    rewrite long_le_exact by assumption; reflexivity.
  - destruct (x <=? y); reflexivity.
Qed.

Definition word_range_bool z := (Int.min_signed <=? z) && (z <=? Int.max_signed).
Lemma word_range_bool_spec z : word_range_bool z = true <-> word_range z.
Proof. unfold word_range_bool, word_range; rewrite andb_true_iff, !Z.leb_le; tauto. Qed.

Definition wide_bounds_tree a :=
  Test (Ebinop Ole (Econst_long (Int64.repr Int.min_signed) wide_type) a type_int32s)
    (Test (Ebinop Ole a (Econst_long (Int64.repr Int.max_signed) wide_type) type_int32s)
      (Decision true) (Decision false)) (Decision false).

Lemma wide_bounds_run ge locals le m a z : typeof a = wide_type -> long_range z ->
  eval_expr ge locals le m a (Vlong (Int64.repr z)) ->
  decision_run (Entry ge locals le m) (wide_bounds_tree a) (word_range_bool z).
Proof.
  intros TYPE RANGE RUN. unfold wide_bounds_tree, word_range_bool.
  eapply run_test with (b := Int.min_signed <=? z).
  - eapply long_le_test with (x := Int.min_signed) (y := z).
    + reflexivity.
    + exact TYPE.
    + apply word_is_long. change (-2147483648 <= -2147483648 <= 2147483647); lia.
    + exact RANGE.
    + constructor.
    + exact RUN.
  - destruct (Int.min_signed <=? z); cbn [andb]; [|constructor].
    eapply run_test with (b := z <=? Int.max_signed).
    + eapply long_le_test with (x := z) (y := Int.max_signed).
      * exact TYPE.
      * reflexivity.
      * exact RANGE.
      * apply word_is_long. change (-2147483648 <= 2147483647 <= 2147483647); lia.
      * exact RUN.
      * constructor.
    + destruct (z <=? Int.max_signed); constructor.
Qed.

Lemma wide_bounds_pure a : pure_scalar a -> pure_tree (wide_bounds_tree a).
Proof.
  intro PURE; unfold wide_bounds_tree. repeat constructor; exact PURE.
Qed.

Print Assumptions wide_bounds_run.
