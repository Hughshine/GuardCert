From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightFragmentProgress.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryLongControl GuardMemoryLongProgressControl.
Set Implicit Arguments.

(** Usual arithmetic conversion permits an I32 bound in an I64 comparison.
    This type capability supports original frontend literals without casts. *)
Definition signed_long_bound_type bound :=
  typeof bound=memory_long_type \/ typeof bound=memory_signed_int_type.
Theorem signed_long_bound_condition_active ge locals le memory iterator bound :
  signed_long_bound_type bound ->
  expression_test (long_counter_condition iterator bound) (Entry ge locals le memory) true ->
  long_counter_active iterator le.
Proof.
  intros [TYPE|TYPE] TEST.
  - apply (@long_counter_condition_active ge locals le memory iterator bound TYPE TEST).
  - destruct TEST as [value [EVAL BOOL]].
    cbn [entry_ge entry_env entry_temps entry_memory long_counter_condition] in EVAL,BOOL.
    inversion EVAL; subst;
      try match goal with LV : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion LV end.
    match goal with LEFT : eval_expr _ _ _ _ (Etempvar iterator _) _ |- _ => inversion LEFT; subst end;
      try match goal with LV : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion LV end.
    match goal with SEM : sem_binary_operation _ _ _ _ _ _ _=Some _ |- _ => rename SEM into OP end.
    rewrite TYPE in OP; destruct v1; destruct v2; try discriminate OP.
    change (Some (Val.of_bool (Int64.lt i (Int64.repr (Int.signed i0))))=Some value) in OP.
    inversion OP; subst.
    match goal with COUNTER : le ! iterator=Some (Vlong ?counter) |- _ =>
      exists counter; split; [exact COUNTER|] end.
    unfold Int64.lt in BOOL; destruct (zlt _ _) as [LESS|GE];
      [pose proof (Int64.signed_range (Int64.repr (Int.signed i0))); lia|discriminate BOOL].
Qed.
Print Assumptions signed_long_bound_condition_active.
