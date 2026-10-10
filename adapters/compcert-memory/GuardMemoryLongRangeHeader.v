From Stdlib Require Import ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightLoopSyntax.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryLongControl
  GuardMemoryLongLoopControl GuardMemoryLongHeaderLicense GuardMemoryLongRangeSource
  GuardMemoryObservationDeterminism.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_long_from_first_header fe ge locals temps memory iterator initial condition body lower after final :
  eval_expr ge locals temps memory initial (Vlong (Int64.repr lower)) ->
  normal_statement body=true ->
  exec_stmt fe ge locals temps memory (memory_long_from_loop iterator initial condition body)
    E0 after final Out_normal ->
  exists flag, expression_test condition
    (Entry ge locals (PTree.set iterator (Vlong (Int64.repr lower)) temps) memory) flag /\
    (flag=true -> exists body_temps body_memory,
      exec_stmt fe ge locals (PTree.set iterator (Vlong (Int64.repr lower)) temps) memory
        body E0 body_temps body_memory Out_normal).
Proof.
  intros INITIAL NORMAL RUN; apply memory_long_from_loop_decode with (lower:=lower) in RUN;
    [eapply memory_long_first_header; eauto|exact INITIAL].
Qed.

(** A successful source comparison supplies actual bound evaluation even for
    an empty interval. Mere global binding or expression stability would not
    supply that read permission. The receipt is after source initialization. *)
Theorem memory_long_strict_bound_license ge locals temps memory iterator bound lower flag :
  typeof bound=memory_long_type -> temps ! iterator=Some (Vlong (Int64.repr lower)) ->
  expression_test (Ebinop Olt (Etempvar iterator memory_long_type) bound memory_signed_int_type)
    (Entry ge locals temps memory) flag ->
  exists word, eval_expr ge locals temps memory bound (Vlong word) /\
    flag=(Int64.signed (Int64.repr lower) <? Int64.signed word).
Proof.
  intros TYPE TEMP [value [EVAL BOOL]].
  destruct (scalar_binary_inv EVAL) as [left [right [LEFT [RIGHT OP]]]].
  apply scalar_temp_inv in LEFT; change (temps ! iterator=Some left) in LEFT.
  rewrite TEMP in LEFT; inversion LEFT; subst left; rewrite TYPE in OP.
  destruct right; try solve [change (None=Some value) in OP; discriminate].
  change (Some (Val.of_bool (Int64.lt (Int64.repr lower) i))=Some value) in OP.
  inversion OP; subst value; exists i; split; [exact RIGHT|].
  change (bool_val (Val.of_bool (Int64.lt (Int64.repr lower) i)) memory_signed_int_type memory=Some flag) in BOOL.
  assert (FLAG : flag=Int64.lt (Int64.repr lower) i).
  { destruct (Int64.lt (Int64.repr lower) i); [change (Some true=Some flag) in BOOL|
      change (Some false=Some flag) in BOOL]; congruence. }
  rewrite FLAG; unfold Int64.lt.
  destruct (zlt (Int64.signed (Int64.repr lower)) (Int64.signed i)); symmetry;
    [apply Z.ltb_lt|apply Z.ltb_ge]; lia.
Qed.
Theorem memory_long_from_bound_license fe ge locals temps memory iterator initial bound body lower after final :
  typeof bound=memory_long_type ->
  eval_expr ge locals temps memory initial (Vlong (Int64.repr lower)) ->
  normal_statement body=true ->
  exec_stmt fe ge locals temps memory
    (memory_long_from_loop iterator initial
      (Ebinop Olt (Etempvar iterator memory_long_type) bound memory_signed_int_type) body)
    E0 after final Out_normal ->
  exists word, eval_expr ge locals (PTree.set iterator (Vlong (Int64.repr lower)) temps) memory bound (Vlong word) /\
    (Int64.signed (Int64.repr lower)<Int64.signed word -> exists body_temps body_memory,
      exec_stmt fe ge locals (PTree.set iterator (Vlong (Int64.repr lower)) temps) memory
        body E0 body_temps body_memory Out_normal).
Proof.
  intros TYPE INITIAL NORMAL RUN.
  destruct (@memory_long_from_first_header fe ge locals temps memory iterator initial _ body lower after final
    INITIAL NORMAL RUN) as [flag [TEST BODY]].
  destruct (@memory_long_strict_bound_license ge locals _ memory iterator bound lower flag
    TYPE (PTree.gss _ _ _) TEST) as [word [SAFE FLAG]].
  exists word; split; [exact SAFE|intro ACTIVE; apply BODY; rewrite FLAG; apply Z.ltb_lt; exact ACTIVE].
Qed.

(** For a signed-I32 offset, an actual subtraction result in signed I32
    implies the mathematical subtraction did not wrap in I64. This fact
    does not generalize to arbitrary affine multiplication. *)
Theorem long_sub_i32_accepted_no_wrap input (offset : int) result :
  result=Int64.sub input (Int64.repr (Int.signed offset)) ->
  Int.min_signed<=Int64.signed result<=Int.max_signed ->
  Int64.signed input-Int.signed offset=Int64.signed result.
Proof.
  intros RESULT RANGE.
  assert (BACK : Int64.add result (Int64.repr (Int.signed offset))=input).
  { rewrite RESULT,Int64.sub_add_opp,Int64.add_assoc.
    rewrite (Int64.add_commut (Int64.neg (Int64.repr (Int.signed offset))) (Int64.repr (Int.signed offset))),
      Int64.add_neg_zero,Int64.add_zero; reflexivity. }
  assert (MATH : input=Int64.repr (Int64.signed result+Int.signed offset)).
  { rewrite <- BACK at 1; rewrite <- (Int64.repr_signed result) at 1.
    rewrite memory_long_repr_add; reflexivity. }
  assert (SAFE : Int64.min_signed<=Int64.signed result+Int.signed offset<=Int64.max_signed).
  { pose proof (Int.signed_range offset) as OFFSET.
    change (-2147483648<=Int64.signed result<=2147483647) in RANGE.
    change (-2147483648<=Int.signed offset<=2147483647) in OFFSET.
    change (-9223372036854775808<=Int64.signed result+Int.signed offset<=9223372036854775807); lia. }
  rewrite MATH,Int64.signed_repr by exact SAFE; lia.
Qed.

Print Assumptions memory_long_from_first_header.
Print Assumptions memory_long_strict_bound_license.
Print Assumptions memory_long_from_bound_license.
Print Assumptions long_sub_i32_accepted_no_wrap.
