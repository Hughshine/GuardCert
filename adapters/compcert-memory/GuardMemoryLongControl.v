From Stdlib Require Import ZArith Lia.
From compcert.lib Require Import Integers Maps Coqlib.
From compcert.common Require Import Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightPureExpr.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryObservationDeterminism.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_signed_int_type := Tint I32 Signed noattr.
Definition memory_long_plus_int code amount :=
  Ebinop Oadd code (Econst_int (Int.repr amount) memory_signed_int_type) memory_long_type.
Definition memory_long_zero :=
  Ecast (Econst_int Int.zero memory_signed_int_type) memory_long_type.

Lemma memory_long_repr_add first second :
  Int64.add (Int64.repr first) (Int64.repr second) = Int64.repr (first+second).
Proof.
  unfold Int64.add; apply Int64.eqm_samerepr; apply Int64.eqm_add;
    apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Theorem memory_long_plus_int_execution ge locals temps memory code value amount :
  typeof code = memory_long_type -> Int.min_signed <= amount <= Int.max_signed ->
  eval_expr ge locals temps memory code (Vlong (Int64.repr value)) ->
  eval_expr ge locals temps memory (memory_long_plus_int code amount) (Vlong (Int64.repr (value+amount))).
Proof.
  intros TYPE RANGE RUN; unfold memory_long_plus_int.
  eapply eval_Ebinop; [exact RUN|constructor|].
  rewrite TYPE; change (Some (Vlong (Int64.add (Int64.repr value)
    (Int64.repr (Int.signed (Int.repr amount))))) = Some (Vlong (Int64.repr (value+amount)))).
  rewrite Int.signed_repr by exact RANGE; rewrite memory_long_repr_add; reflexivity.
Qed.

Theorem memory_long_plus_int_decode ge locals temps memory code value amount result :
  typeof code = memory_long_type -> Int.min_signed <= amount <= Int.max_signed ->
  eval_expr ge locals temps memory code (Vlong (Int64.repr value)) ->
  eval_expr ge locals temps memory (memory_long_plus_int code amount) result ->
  result = Vlong (Int64.repr (value+amount)).
Proof.
  intros TYPE RANGE INPUT RUN; eapply memory_expression_unique; [exact RUN|].
  eapply memory_long_plus_int_execution; eauto.
Qed.

Theorem memory_long_zero_execution ge locals temps memory :
  eval_expr ge locals temps memory memory_long_zero (Vlong Int64.zero).
Proof. unfold memory_long_zero; eapply eval_Ecast; [constructor|reflexivity]. Qed.

Theorem memory_long_initialization_execution fe ge locals temps memory iterator :
  exec_stmt fe ge locals temps memory (Sset iterator memory_long_zero) E0
    (PTree.set iterator (Vlong Int64.zero) temps) memory Out_normal.
Proof. apply exec_Sset; apply memory_long_zero_execution. Qed.

Theorem memory_long_increment_execution fe ge locals temps memory iterator value :
  temps ! iterator = Some (Vlong (Int64.repr value)) ->
  exec_stmt fe ge locals temps memory
    (Sset iterator (memory_long_plus_int (Etempvar iterator memory_long_type) 1)) E0
    (PTree.set iterator (Vlong (Int64.repr (value+1))) temps) memory Out_normal.
Proof.
  intro TEMP; apply exec_Sset; apply memory_long_plus_int_execution;
    [reflexivity|unfold Int.min_signed, Int.max_signed; cbn; lia|constructor; exact TEMP].
Qed.

Lemma memory_long_lt_exact ge memory first second :
  Int64.min_signed <= first <= Int64.max_signed ->
  Int64.min_signed <= second <= Int64.max_signed ->
  sem_binary_operation ge Olt (Vlong (Int64.repr first)) memory_long_type
    (Vlong (Int64.repr second)) memory_long_type memory = Some (Val.of_bool (Z.ltb first second)).
Proof.
  intros FIRST SECOND.
  change (Some (Val.of_bool (Int64.lt (Int64.repr first) (Int64.repr second))) =
    Some (Val.of_bool (Z.ltb first second))).
  unfold Int64.lt; rewrite !Int64.signed_repr by assumption.
  destruct (zlt first second) as [LT|GE].
  - rewrite (proj2 (Z.ltb_lt first second) LT); reflexivity.
  - rewrite (proj2 (Z.ltb_ge first second) ltac:(lia)); reflexivity.
Qed.

Theorem memory_long_test_execution ge locals temps memory first second i n :
  typeof first = memory_long_type -> typeof second = memory_long_type ->
  Int64.min_signed <= i <= Int64.max_signed -> Int64.min_signed <= n <= Int64.max_signed ->
  eval_expr ge locals temps memory first (Vlong (Int64.repr i)) ->
  eval_expr ge locals temps memory second (Vlong (Int64.repr n)) ->
  eval_expr ge locals temps memory (Ebinop Olt first second memory_signed_int_type)
    (Val.of_bool (Z.ltb i n)).
Proof.
  intros FT ST I N FIRST SECOND; eapply eval_Ebinop; [exact FIRST|exact SECOND|].
  rewrite FT,ST; apply memory_long_lt_exact; assumption.
Qed.

Print Assumptions memory_long_plus_int_execution.
Print Assumptions memory_long_plus_int_decode.
Print Assumptions memory_long_initialization_execution.
Print Assumptions memory_long_increment_execution.
Print Assumptions memory_long_test_execution.
