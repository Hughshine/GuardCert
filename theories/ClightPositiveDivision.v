From Stdlib Require Import ZArith Bool Lia.
From compcert.lib Require Import Integers Coqlib.
From compcert.common Require Import Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
Open Scope Z_scope.

Lemma signed_nonnegative_division ce x divisor memory :
  0 <= x <= Int.max_signed -> 0 < divisor <= Int.max_signed ->
  sem_binary_operation ce Odiv (Vint (Int.repr x)) type_int32s
    (Vint (Int.repr divisor)) type_int32s memory = Some (Vint (Int.repr (x / divisor))).
Proof.
  intros X D.
  assert (XR : Int.min_signed <= x <= Int.max_signed) by (change Int.min_signed with (-2147483648); lia).
  assert (DR : Int.min_signed <= divisor <= Int.max_signed) by (change Int.min_signed with (-2147483648); lia).
  assert (NONZERO : Int.repr divisor <> Int.zero).
  { intro SAME; apply (f_equal Int.signed) in SAME; rewrite Int.signed_repr, Int.signed_zero in SAME by exact DR; lia. }
  assert (NOTMONE : Int.repr divisor <> Int.mone).
  { intro SAME; apply (f_equal Int.signed) in SAME; rewrite Int.signed_repr, Int.signed_mone in SAME by exact DR; lia. }
  change ((if Int.eq (Int.repr divisor) Int.zero ||
    Int.eq (Int.repr x) (Int.repr Int.min_signed) && Int.eq (Int.repr divisor) Int.mone
    then None else Some (Vint (Int.divs (Int.repr x) (Int.repr divisor)))) = Some (Vint (Int.repr (x / divisor)))).
  rewrite (Int.eq_false _ _ NONZERO), (Int.eq_false _ _ NOTMONE), andb_false_r; cbn.
  unfold Int.divs; rewrite !Int.signed_repr by assumption.
  rewrite Z.quot_div_nonneg by lia; reflexivity.
Qed.

Lemma positive_division_evaluation ge locals temps memory code x divisor :
  typeof code = type_int32s ->
  eval_expr ge locals temps memory code (Vint (Int.repr x)) ->
  0 <= x <= Int.max_signed -> 0 < divisor <= Int.max_signed ->
  eval_expr ge locals temps memory
    (Ebinop Odiv code (Econst_int (Int.repr divisor) type_int32s) type_int32s)
    (Vint (Int.repr (x / divisor))).
Proof.
  intros TYPE EVAL X D; eapply eval_Ebinop; [exact EVAL|constructor|].
  rewrite TYPE; eapply signed_nonnegative_division; eauto.
Qed.
Print Assumptions signed_nonnegative_division.
Print Assumptions positive_division_evaluation.
