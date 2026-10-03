From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight Ctypes Cop.
From Guard Require Import ClightCondition ClightPureExpr CompCertMemoryActions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Inequality of actual, aligned int32 cell addresses gives separation even
    when two pointer temporaries name slices of the same physical block. *)
Definition memory_pointer_cells_unequal first_block first_offset second_block second_offset :=
  negb (Pos.eqb first_block second_block && Ptrofs.eq first_offset second_offset).
Lemma memory_pointer_cells_comparison memory first_block first_offset second_block second_offset :
  Mem.valid_pointer memory first_block (Ptrofs.unsigned first_offset) = true ->
  Mem.valid_pointer memory second_block (Ptrofs.unsigned second_offset) = true ->
  Cop.cmp_ptr memory Cne (Vptr first_block first_offset) (Vptr second_block second_offset) =
    Some (Val.of_bool (memory_pointer_cells_unequal first_block first_offset second_block second_offset)).
Proof.
  intros FIRST SECOND; unfold Cop.cmp_ptr,memory_pointer_cells_unequal.
  destruct Archi.ptr64 eqn:ARCH; unfold Val.cmplu_bool,Val.cmpu_bool; rewrite ARCH; cbn.
  all: destruct (eq_block first_block second_block) as [SAME|DIFFERENT].
  all: try (subst second_block; rewrite FIRST,SECOND,Pos.eqb_refl; reflexivity).
  all: rewrite FIRST,SECOND; cbn;
    assert (Pos.eqb first_block second_block = false) as DISTINCT
      by (apply Pos.eqb_neq; exact DIFFERENT); rewrite DISTINCT; reflexivity.
Qed.
Theorem memory_pointer_cells_unequal_separated first_block first_offset second_block second_offset :
  (4 | Ptrofs.unsigned first_offset) -> (4 | Ptrofs.unsigned second_offset) ->
  memory_pointer_cells_unequal first_block first_offset second_block second_offset = true ->
  location_disjoint (MemoryLocation Mint32 first_block (Ptrofs.unsigned first_offset))
    (MemoryLocation Mint32 second_block (Ptrofs.unsigned second_offset)).
Proof.
  intros [first_cells FIRST] [second_cells SECOND] DIFFERENT.
  unfold memory_pointer_cells_unequal in DIFFERENT.
  unfold location_disjoint; cbn [location_block location_offset location_chunk size_chunk].
  destruct (peq first_block second_block) as [SAME|DISTINCT]; [subst second_block|left; exact DISTINCT].
  rewrite Pos.eqb_refl in DIFFERENT; cbn in DIFFERENT.
  apply negb_true_iff in DIFFERENT.
  assert (OFFSETS : first_offset <> second_offset) by (intro SAME; subst; rewrite Ptrofs.eq_true in DIFFERENT; discriminate).
  assert (UNSIGNED : Ptrofs.unsigned first_offset <> Ptrofs.unsigned second_offset).
  { intro SAME; apply OFFSETS; pose proof (f_equal Ptrofs.repr SAME) as EQUAL; rewrite !Ptrofs.repr_unsigned in EQUAL; exact EQUAL. }
  right; nia.
Qed.
Definition memory_pointer_cells_test first second := Ebinop One first second type_int32s.
Theorem memory_pointer_cells_test_evaluation ge locals temps memory first second
    first_block first_offset second_block second_offset :
  typeof first = Tpointer type_int32s noattr -> typeof second = Tpointer type_int32s noattr ->
  eval_expr ge locals temps memory first (Vptr first_block first_offset) ->
  eval_expr ge locals temps memory second (Vptr second_block second_offset) ->
  Mem.valid_pointer memory first_block (Ptrofs.unsigned first_offset) = true ->
  Mem.valid_pointer memory second_block (Ptrofs.unsigned second_offset) = true ->
  expression_test (memory_pointer_cells_test first second) (Entry ge locals temps memory)
    (memory_pointer_cells_unequal first_block first_offset second_block second_offset).
Proof.
  intros FIRST_TYPE SECOND_TYPE FIRST SECOND VALID_FIRST VALID_SECOND.
  exists (Val.of_bool (memory_pointer_cells_unequal first_block first_offset second_block second_offset)); split.
  - eapply eval_Ebinop; [exact FIRST|exact SECOND|].
    rewrite FIRST_TYPE,SECOND_TYPE; change (Cop.cmp_ptr memory Cne (Vptr first_block first_offset)
      (Vptr second_block second_offset) = Some (Val.of_bool
        (memory_pointer_cells_unequal first_block first_offset second_block second_offset))).
    apply memory_pointer_cells_comparison; assumption.
  - destruct (memory_pointer_cells_unequal first_block first_offset second_block second_offset); reflexivity.
Qed.
Theorem memory_pointer_cells_test_exact ge locals temps memory first second
    first_block first_offset second_block second_offset flag :
  pure_scalar first -> pure_scalar second ->
  typeof first = Tpointer type_int32s noattr -> typeof second = Tpointer type_int32s noattr ->
  eval_expr ge locals temps memory first (Vptr first_block first_offset) ->
  eval_expr ge locals temps memory second (Vptr second_block second_offset) ->
  Mem.valid_pointer memory first_block (Ptrofs.unsigned first_offset) = true ->
  Mem.valid_pointer memory second_block (Ptrofs.unsigned second_offset) = true ->
  (expression_test (memory_pointer_cells_test first second) (Entry ge locals temps memory) flag <->
    flag = memory_pointer_cells_unequal first_block first_offset second_block second_offset).
Proof.
  intros FIRST_PURE SECOND_PURE FIRST_TYPE SECOND_TYPE FIRST SECOND VALID_FIRST VALID_SECOND.
  pose proof (@memory_pointer_cells_test_evaluation ge locals temps memory first second
    first_block first_offset second_block second_offset FIRST_TYPE SECOND_TYPE FIRST SECOND
    VALID_FIRST VALID_SECOND) as EVALUATION.
  split.
  - intro RUN; eapply (@pure_test_determinate (memory_pointer_cells_test first second)
      (Entry ge locals temps memory)); [constructor; assumption|exact RUN|exact EVALUATION].
  - intro SAME; subst flag; exact EVALUATION.
Qed.
Theorem memory_pointer_cells_test_separated ge locals temps memory first second
    first_block first_offset second_block second_offset :
  pure_scalar first -> pure_scalar second ->
  typeof first = Tpointer type_int32s noattr -> typeof second = Tpointer type_int32s noattr ->
  eval_expr ge locals temps memory first (Vptr first_block first_offset) ->
  eval_expr ge locals temps memory second (Vptr second_block second_offset) ->
  Mem.valid_pointer memory first_block (Ptrofs.unsigned first_offset) = true ->
  Mem.valid_pointer memory second_block (Ptrofs.unsigned second_offset) = true ->
  (4 | Ptrofs.unsigned first_offset) -> (4 | Ptrofs.unsigned second_offset) ->
  expression_test (memory_pointer_cells_test first second) (Entry ge locals temps memory) true ->
  location_disjoint (MemoryLocation Mint32 first_block (Ptrofs.unsigned first_offset))
    (MemoryLocation Mint32 second_block (Ptrofs.unsigned second_offset)).
Proof.
  intros FIRST_PURE SECOND_PURE FIRST_TYPE SECOND_TYPE FIRST SECOND VALID_FIRST VALID_SECOND ALIGN_FIRST ALIGN_SECOND TEST.
  apply (@memory_pointer_cells_test_exact ge locals temps memory first second first_block first_offset
    second_block second_offset true FIRST_PURE SECOND_PURE FIRST_TYPE SECOND_TYPE FIRST SECOND VALID_FIRST VALID_SECOND) in TEST.
  eapply memory_pointer_cells_unequal_separated; [exact ALIGN_FIRST|exact ALIGN_SECOND|symmetry; exact TEST].
Qed.
Print Assumptions memory_pointer_cells_comparison.
Print Assumptions memory_pointer_cells_unequal_separated.
Print Assumptions memory_pointer_cells_test_evaluation.
Print Assumptions memory_pointer_cells_test_exact.
Print Assumptions memory_pointer_cells_test_separated.
