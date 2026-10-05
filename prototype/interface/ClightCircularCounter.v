From Stdlib Require Import Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightPureExpr ClightCountedProtocol ClightRegionProgress ClightFrontendRegion.
From GuardInterface Require Import ClightCounterProgress ClightQuietDeterminacy ClightStableLoopCondition.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition cyclic_distance word bound :=
  if zle (Int.unsigned word) (Int.unsigned bound)
  then Int.unsigned bound - Int.unsigned word
  else Int.modulus + Int.unsigned bound - Int.unsigned word.
Lemma cyclic_distance_nonnegative word bound : 0 <= cyclic_distance word bound.
Proof.
  unfold cyclic_distance; pose proof (Int.unsigned_range word); pose proof (Int.unsigned_range bound).
  destruct (zle (Int.unsigned word) (Int.unsigned bound)); lia.
Qed.
Lemma cyclic_distance_positive word bound : word <> bound -> 0 < cyclic_distance word bound.
Proof.
  intro DIFFERENT; assert (VALUES : Int.unsigned word <> Int.unsigned bound).
  { intro SAME; apply DIFFERENT; rewrite <- (Int.repr_unsigned word), <- (Int.repr_unsigned bound); f_equal; exact SAME. }
  unfold cyclic_distance; pose proof (Int.unsigned_range word); pose proof (Int.unsigned_range bound).
  destruct (zle (Int.unsigned word) (Int.unsigned bound)); lia.
Qed.
Lemma unsigned_increment_value word :
  Int.unsigned (Int.add word Int.one) =
    if zeq (Int.unsigned word) (Int.modulus-1) then 0 else Int.unsigned word+1.
Proof.
  rewrite Int.add_unsigned; change (Int.unsigned Int.one) with 1; rewrite Int.unsigned_repr_eq.
  pose proof (Int.unsigned_range word); destruct (zeq (Int.unsigned word) (Int.modulus-1)).
  - replace (Int.unsigned word+1) with Int.modulus by lia; apply Z.mod_same; pose proof Int.modulus_pos; lia.
  - apply Z.mod_small; lia.
Qed.
Theorem cyclic_distance_decreases word bound : word <> bound ->
  cyclic_distance word bound = cyclic_distance (Int.add word Int.one) bound + 1.
Proof.
  intro DIFFERENT; assert (VALUES : Int.unsigned word <> Int.unsigned bound).
  { intro SAME; apply DIFFERENT; rewrite <- (Int.repr_unsigned word), <- (Int.repr_unsigned bound); f_equal; exact SAME. }
  pose proof (Int.unsigned_range word); pose proof (Int.unsigned_range bound).
  unfold cyclic_distance; rewrite unsigned_increment_value.
  destruct (zeq (Int.unsigned word) (Int.modulus-1)) as [WRAP|LINEAR].
  - destruct (zle (Int.unsigned word) (Int.unsigned bound));
      destruct (zle 0 (Int.unsigned bound)); lia.
  - destruct (zle (Int.unsigned word) (Int.unsigned bound));
      destruct (zle (Int.unsigned word+1) (Int.unsigned bound)); lia.
Qed.

Definition unsigned_increment_expression iterator :=
  Ebinop Oadd (Etempvar iterator type_int32u) (Econst_int Int.one type_int32u) type_int32u.
Definition circular_active iterator bound (le : temp_env) := exists word upper,
  le ! iterator = Some (Vint word) /\ le ! bound = Some (Vint upper) /\ word <> upper.
Definition circular_remaining iterator bound (le : temp_env) :=
  match le ! iterator, le ! bound with
  | Some (Vint word), Some (Vint upper) => Z.to_nat (cyclic_distance word upper)
  | _, _ => 0%nat end.
Definition circular_counter_facts iterator bound (DISTINCT : iterator <> bound) :
  counter_progress_facts iterator (unsigned_increment_expression iterator).
Proof.
  refine (@CounterProgressFacts iterator (unsigned_increment_expression iterator)
    (circular_active iterator bound) (circular_remaining iterator bound) (increment_temps iterator) _ _ _ _).
  - intros le [word [upper [ITER [BOUND DIFFERENT]]]]; unfold circular_remaining; rewrite ITER, BOUND.
    pose proof (cyclic_distance_positive DIFFERENT) as POS.
    pose proof (Z2Nat.id (cyclic_distance word upper) ltac:(lia)); lia.
  - intros le [word [upper [ITER [BOUND DIFFERENT]]]]; unfold circular_remaining, increment_temps;
      rewrite ITER, BOUND, PTree.gss, PTree.gso by congruence; rewrite BOUND.
    rewrite <- Z2Nat.inj_succ by apply cyclic_distance_nonnegative; f_equal.
    pose proof (cyclic_distance_decreases DIFFERENT); unfold Z.succ; lia.
  - intros ge locals le memory [word [upper [ITER [BOUND DIFFERENT]]]]; exists (Vint (Int.add word Int.one)); split.
    + eapply eval_Ebinop with (v1 := Vint word) (v2 := Vint Int.one); [constructor; exact ITER|constructor|reflexivity].
    + unfold increment_temps; rewrite ITER; reflexivity.
  - repeat constructor.
Defined.

Definition signed_word_view iterator := Ecast (Etempvar iterator type_int32u) type_int32s.
Definition unsigned_equality_test iterator bound :=
  Ebinop One (signed_word_view iterator) (signed_word_view bound) type_int32s.
Definition unsigned_order_test iterator bound :=
  Ebinop Olt (signed_word_view iterator) (signed_word_view bound) type_int32s.
Definition unsigned_equality_loop iterator bound body :=
  generic_frontend_loop iterator (unsigned_increment_expression iterator) (unsigned_equality_test iterator bound) body.
Definition unsigned_order_loop iterator bound body :=
  generic_frontend_loop iterator (unsigned_increment_expression iterator) (unsigned_order_test iterator bound) body.
Lemma signed_word_view_inverse ge locals le memory iterator word :
  eval_expr ge locals le memory (signed_word_view iterator) (Vint word) -> le ! iterator = Some (Vint word).
Proof.
  intro RUN; unfold signed_word_view in RUN; inversion RUN; subst.
  all: try match goal with LV : eval_lvalue _ _ _ _ (Ecast _ _) _ _ _ |- _ => inversion LV end.
  match goal with TEMP : eval_expr _ _ _ _ (Etempvar _ _) _, CAST : sem_cast _ _ _ _ = _ |- _ =>
    apply scalar_temp_inv in TEMP; destruct v1; cbn in CAST; try discriminate;
    inversion CAST; subst; exact TEMP end.
Qed.
Lemma signed_word_view_evaluation ge locals le memory iterator word :
  le ! iterator = Some (Vint word) -> eval_expr ge locals le memory (signed_word_view iterator) (Vint word).
Proof. intro ITER; eapply eval_Ecast with (v1 := Vint word); [constructor; exact ITER|reflexivity]. Qed.
Theorem unsigned_equality_test_facts ge locals le memory iterator bound answer :
  expression_test (unsigned_equality_test iterator bound) (Entry ge locals le memory) answer ->
  exists word upper, le ! iterator = Some (Vint word) /\ le ! bound = Some (Vint upper) /\
    answer = negb (Int.eq word upper).
Proof.
  intros [value [EVAL BOOL]]; apply scalar_binary_inv in EVAL;
    destruct EVAL as [word [upper [ITER [BOUND OP]]]].
  destruct word, upper; try discriminate OP.
  apply signed_word_view_inverse in ITER; apply signed_word_view_inverse in BOUND.
  change (Some (Val.of_bool (negb (Int.eq i i0))) = Some value) in OP; injection OP as SAME; subst value.
  rewrite bool_of_bool in BOOL; exists i, i0; repeat split; try assumption; congruence.
Qed.
Lemma unsigned_order_test_eval ge locals le memory iterator bound word upper :
  le ! iterator = Some (Vint word) -> le ! bound = Some (Vint upper) ->
  expression_test (unsigned_order_test iterator bound) (Entry ge locals le memory) (Int.lt word upper).
Proof.
  intros ITER BOUND; exists (Val.of_bool (Int.lt word upper)); split; [|apply bool_of_bool].
  eapply eval_Ebinop with (v1 := Vint word) (v2 := Vint upper);
    [apply signed_word_view_evaluation; exact ITER|apply signed_word_view_evaluation; exact BOUND|reflexivity].
Qed.
Lemma unsigned_increment_execution_exact fe ge locals iterator bound le memory trace after final outcome
  (DISTINCT : iterator <> bound) :
  circular_active iterator bound le ->
  exec_stmt fe ge locals le memory (Ssequence Sskip (Sset iterator (unsigned_increment_expression iterator)))
    trace after final outcome ->
  trace = E0 /\ after = increment_temps iterator le /\ final = memory /\ outcome = Out_normal.
Proof.
  intros ACTIVE RUN; apply skip_prefix_exec in RUN.
  eapply quiet_execution_determinate; [exact RUN|reflexivity|].
  apply (@generic_increment_normal fe ge locals iterator (unsigned_increment_expression iterator)
    (@circular_counter_facts iterator bound DISTINCT)); exact ACTIVE.
Qed.
Definition unsigned_equality_progress iterator bound body (DISTINCT : iterator <> bound) (BODY : memory_body body = true) :
  region_progress (unsigned_equality_loop iterator bound body).
Proof.
  apply generic_frontend_progress with (FACTS := circular_counter_facts DISTINCT); [exact BODY|].
  intros ge locals le memory TEST; destruct (unsigned_equality_test_facts TEST) as [word [upper [ITER [BOUND DIFFERENT]]]].
  symmetry in DIFFERENT; apply negb_true_iff in DIFFERENT.
  exists word, upper; split; [exact ITER|split; [exact BOUND|]].
  pose proof (Int.eq_spec word upper); rewrite DIFFERENT in H; exact H.
Defined.
Print Assumptions cyclic_distance_nonnegative.
Print Assumptions cyclic_distance_positive.
Print Assumptions unsigned_increment_value.
Print Assumptions cyclic_distance_decreases.
Print Assumptions circular_counter_facts.
Print Assumptions unsigned_equality_test_facts.
Print Assumptions unsigned_equality_progress.
Print Assumptions unsigned_order_test_eval.
Print Assumptions unsigned_increment_execution_exact.
