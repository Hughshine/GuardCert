From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightCondition ClightRectangularStore CompCertStoreSchedule.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryMultipleArrays.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** This primitive compares bases of actual array objects.  Both offsets are
    zero; pointer inequality would not establish disjointness for slices. *)
Definition memory_array_separation_test first_shape first second_shape second :=
  Ebinop One (Evar first (rect_array_type first_shape))
    (Evar second (rect_array_type second_shape)) type_int32s.

Lemma memory_array_base_comparison memory first second :
  Mem.valid_pointer memory first 0 = true ->
  Mem.valid_pointer memory second 0 = true ->
  Cop.cmp_ptr memory Cne (Vptr first Ptrofs.zero) (Vptr second Ptrofs.zero) =
    Some (Val.of_bool (negb (Pos.eqb first second))).
Proof.
  intros FIRST SECOND; unfold Cop.cmp_ptr.
  destruct Archi.ptr64 eqn:ARCH;
    unfold Val.cmplu_bool, Val.cmpu_bool; rewrite ARCH; cbn.
  all: rewrite Ptrofs.unsigned_zero;
    destruct (eq_block first second) as [SAME|DISTINCT].
  all: try (subst second; rewrite FIRST; cbn;
    rewrite Pos.eqb_refl; unfold Ptrofs.cmpu; rewrite Ptrofs.eq_true; reflexivity).
  all: rewrite FIRST,SECOND; cbn; assert (Pos.eqb first second = false) as DIFFERENT
    by (apply Pos.eqb_neq; exact DISTINCT); rewrite DIFFERENT; reflexivity.
Qed.

Theorem memory_array_separation_evaluation first_shape first second_shape second
  ge locals temps memory first_block second_block :
  rect_array_binding first_shape ge locals first first_block ->
  rect_array_binding second_shape ge locals second second_block ->
  Mem.valid_pointer memory first_block 0 = true ->
  Mem.valid_pointer memory second_block 0 = true ->
  expression_test (memory_array_separation_test first_shape first second_shape second)
    (Entry ge locals temps memory) (negb (Pos.eqb first_block second_block)).
Proof.
  intros FIRST SECOND VALID_FIRST VALID_SECOND.
  exists (Val.of_bool (negb (Pos.eqb first_block second_block))); split.
  - eapply eval_Ebinop.
    + apply rect_reference_evaluation; exact FIRST.
    + apply rect_reference_evaluation; exact SECOND.
    + change (Cop.cmp_ptr memory Cne (Vptr first_block Ptrofs.zero)
        (Vptr second_block Ptrofs.zero) =
        Some (Val.of_bool (negb (Pos.eqb first_block second_block)))).
      apply memory_array_base_comparison; assumption.
  - destruct (negb (Pos.eqb first_block second_block)); reflexivity.
Qed.

Theorem memory_two_arrays_separation_sound first second :
  negb (Pos.eqb (memory_array_block first) (memory_array_block second)) = true ->
  locations_nonalias (memory_array_registry [first;second]).
Proof.
  intro DISTINCT; apply memory_array_registry_nonalias.
  cbn; constructor; [|constructor; [cbn; tauto|constructor]].
  cbn; apply negb_true_iff in DISTINCT; apply Pos.eqb_neq in DISTINCT.
  intuition congruence.
Qed.

Lemma memory_array_separation_exact first_shape first second_shape second
  ge locals temps memory first_block second_block flag :
  rect_array_binding first_shape ge locals first first_block ->
  rect_array_binding second_shape ge locals second second_block ->
  Mem.valid_pointer memory first_block 0 = true ->
  Mem.valid_pointer memory second_block 0 = true ->
  (expression_test (memory_array_separation_test first_shape first second_shape second)
    (Entry ge locals temps memory) flag <-> flag = negb (Pos.eqb first_block second_block)).
Proof.
  intros FIRST SECOND VF VS; split.
  - intros [value [EVAL BOOL]].
    cbn [entry_ge entry_env entry_temps entry_memory] in EVAL,BOOL.
    unfold memory_array_separation_test in EVAL,BOOL.
    inversion EVAL; subst;
      try match goal with BAD : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion BAD end.
    match goal with LEFT : eval_expr _ _ _ _ (Evar first _) ?left,
      RIGHT : eval_expr _ _ _ _ (Evar second _) ?right |- _ =>
      destruct (@rect_reference_inverse first_shape ge locals temps memory first left LEFT)
        as [actual_first [B1 ->]];
      destruct (@rect_reference_inverse second_shape ge locals temps memory second right RIGHT)
        as [actual_second [B2 ->]];
      assert (actual_first = first_block) by (eapply rect_array_binding_unique; eauto);
      assert (actual_second = second_block) by (eapply rect_array_binding_unique; eauto);
      subst actual_first actual_second
    end.
    match goal with SEM : sem_binary_operation _ One _ _ _ _ _ = Some value |- _ =>
      change (Cop.cmp_ptr memory Cne (Vptr first_block Ptrofs.zero)
        (Vptr second_block Ptrofs.zero) = Some value) in SEM;
      rewrite (@memory_array_base_comparison memory first_block second_block VF VS) in SEM;
      inversion SEM; subst value
    end.
    destruct (negb (Pos.eqb first_block second_block)).
    + change (Some true = Some flag) in BOOL; congruence.
    + change (Some false = Some flag) in BOOL; congruence.
  - intro SAME; subst flag; apply memory_array_separation_evaluation; assumption.
Qed.

Print Assumptions memory_array_base_comparison.
Print Assumptions memory_array_separation_evaluation.
Print Assumptions memory_two_arrays_separation_sound.
