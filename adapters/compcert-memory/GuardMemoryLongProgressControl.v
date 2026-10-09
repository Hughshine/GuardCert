From Stdlib Require Import List ZArith Arith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightFragmentProgress ClightPureExpr.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryLongControl.
Import ListNotations.
Set Implicit Arguments.

(** A control bound, independent of the repeatedly loaded bound expression.
    A successful signed-I64 test excludes increment at max_signed. This rank
    rules out infinite internal stuttering; it does not assert load safety. *)
Definition long_counter_remaining iterator (le : temp_env) : nat :=
  match le ! iterator with
  | Some (Vlong value) => Z.to_nat (Int64.max_signed - Int64.signed value)
  | _ => 0 end.
Definition maximum_long_counter_distance := Z.to_nat (Int64.max_signed - Int64.min_signed).
Definition long_counter_active iterator (le : temp_env) : Prop :=
  exists value, le ! iterator=Some (Vlong value) /\ (Int64.signed value<Int64.max_signed)%Z.
Definition long_increment_temps iterator (le : temp_env) :=
  match le ! iterator with
  | Some (Vlong value) => PTree.set iterator (Vlong (Int64.add value Int64.one)) le
  | _ => le end.
Definition long_counter_condition iterator bound :=
  Ebinop Olt (Etempvar iterator memory_long_type) bound memory_signed_int_type.
Definition long_counter_increment iterator :=
  Sset iterator (memory_long_plus_int (Etempvar iterator memory_long_type) 1).

Lemma long_counter_distance_bounded iterator le :
  (long_counter_remaining iterator le <= maximum_long_counter_distance)%nat.
Proof.
  unfold long_counter_remaining,maximum_long_counter_distance.
  destruct (le ! iterator) as [value|]; [destruct value|]; try lia.
  apply Z2Nat.inj_le; pose proof (Int64.signed_range i); lia.
Qed.
Lemma long_counter_active_positive iterator le : long_counter_active iterator le ->
  (0<long_counter_remaining iterator le)%nat.
Proof.
  intros [value [VALUE LESS]]; unfold long_counter_remaining; rewrite VALUE.
  pose proof (Z2Nat.id (Int64.max_signed-Int64.signed value) ltac:(lia)); lia.
Qed.
Lemma long_counter_increment_distance iterator le : long_counter_active iterator le ->
  long_counter_remaining iterator le=S (long_counter_remaining iterator (long_increment_temps iterator le)).
Proof.
  intros [value [VALUE LESS]]; unfold long_counter_remaining,long_increment_temps.
  rewrite VALUE,PTree.gss,Int64.add_signed.
  change (Int64.signed Int64.one) with 1%Z.
  rewrite Int64.signed_repr by (pose proof (Int64.signed_range value); lia).
  rewrite <- Z2Nat.inj_succ by lia; f_equal; lia.
Qed.
Lemma long_counter_increment_evaluation ge locals iterator le memory :
  long_counter_active iterator le -> exists value,
  eval_expr ge locals le memory (memory_long_plus_int (Etempvar iterator memory_long_type) 1) value /\
  PTree.set iterator value le=long_increment_temps iterator le.
Proof.
  intros [counter [COUNTER LESS]]; exists (Vlong (Int64.add counter Int64.one)); split.
  - eapply eval_Ebinop; [constructor; exact COUNTER|constructor|reflexivity].
  - unfold long_increment_temps; rewrite COUNTER; reflexivity.
Qed.
Lemma long_counter_increment_normal fe ge locals iterator le memory : long_counter_active iterator le ->
  exec_stmt fe ge locals le memory (long_counter_increment iterator) E0
    (long_increment_temps iterator le) memory Out_normal.
Proof.
  intro ACTIVE; destruct (long_counter_increment_evaluation ge locals memory ACTIVE) as [value [EVAL TEMPS]].
  unfold long_counter_increment; rewrite <- TEMPS; constructor; exact EVAL.
Qed.
Lemma long_counter_condition_active ge locals le memory iterator bound : typeof bound=memory_long_type ->
  expression_test (long_counter_condition iterator bound) (Entry ge locals le memory) true ->
  long_counter_active iterator le.
Proof.
  intros TYPE [value [EVAL BOOL]]. cbn [entry_ge entry_env entry_temps entry_memory long_counter_condition] in EVAL,BOOL.
  inversion EVAL; subst;
    try match goal with LV : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion LV end.
  match goal with LEFT : eval_expr _ _ _ _ (Etempvar iterator _) _ |- _ => inversion LEFT; subst end;
    try match goal with LV : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion LV end.
  match goal with SEM : sem_binary_operation _ _ _ _ _ _ _=Some _ |- _ => rename SEM into OP end.
  rewrite TYPE in OP; destruct v1; destruct v2; try discriminate OP.
  change (Some (Val.of_bool (Int64.lt i i0))=Some value) in OP.
  inversion OP; subst.
  match goal with COUNTER : le ! iterator=Some (Vlong ?counter) |- _ => exists counter; split; [exact COUNTER|] end.
  unfold Int64.lt in BOOL; destruct (zlt _ _) as [LESS|GE]; [pose proof (Int64.signed_range i0); lia|discriminate BOOL].
Qed.
Lemma long_counter_frame_distance iterator protected before after :
  preserves_temporaries (iterator::protected) before after ->
  long_counter_remaining iterator after=long_counter_remaining iterator before.
Proof. intro FRAME; unfold long_counter_remaining; rewrite (FRAME iterator (or_introl eq_refl)); reflexivity. Qed.
Lemma long_counter_frame_active iterator protected before after :
  preserves_temporaries (iterator::protected) before after ->
  long_counter_active iterator before -> long_counter_active iterator after.
Proof.
  intros FRAME [value [VALUE LESS]]; exists value; split; [rewrite (FRAME iterator (or_introl eq_refl)); exact VALUE|exact LESS].
Qed.

Print Assumptions long_counter_distance_bounded.
Print Assumptions long_counter_increment_distance.
Print Assumptions long_counter_condition_active.
