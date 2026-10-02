From Stdlib Require Import List ZArith Lia Sorting.Permutation.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import AbstractSchedule AbstractScheduleChecker CompCertStoreSchedule
  CompCertIndexSchedule ClightMatrixStore ClightMatrixLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Lower a certified finite point order to actual Clight stores. The immutable
    payload map is captured by the language instance, not interpreted by the
    scheduling kernel. This first encoder uses the four cells of the matrix
    example and introduces no compiler temporaries. *)
Definition indexed_store_statement array index value :=
  Sassign
    (Ederef (Ebinop Oadd (Evar array matrix_array_type)
      (matrix_constant (Z.of_nat index)) (Tpointer type_int32s noattr)) type_int32s)
    (Econst_int value type_int32s).

Lemma indexed_store_statement_encode fe ge locals le memory array block index value final :
  matrix_array_binding ge locals array block -> (index < 4)%nat ->
  store_action_run (indexed_store_action block (fun _ => value) index) memory final ->
  exec_stmt fe ge locals le memory (indexed_store_statement array index value) E0 le final Out_normal.
Proof.
  intros ARRAY RANGE STORE.
  assert (BOUNDS : 0 <= Z.of_nat index <= 3) by lia.
  unfold indexed_store_statement; eapply exec_Sassign with
    (loc := block) (ofs := Ptrofs.repr (4 * Z.of_nat index)) (bf := Full)
    (v := Vint value) (v2 := Vint value).
  - apply eval_Ederef. eapply eval_Ebinop with
      (v1 := Vptr block Ptrofs.zero) (v2 := Vint (Int.repr (Z.of_nat index))).
    + apply matrix_reference_evaluation; exact ARRAY.
    + unfold matrix_constant; constructor.
    + apply matrix_pointer_add; exact BOUNDS.
  - constructor.
  - reflexivity.
  - apply assign_loc_value with (chunk := Mint32); [reflexivity|].
    cbn [Mem.storev]; rewrite Ptrofs.unsigned_repr by (apply matrix_small_offset_bound; lia).
    destruct (zle (4 * Z.of_nat index + size_chunk Mint32) Ptrofs.modulus); [exact STORE|].
    exfalso; pose proof (@matrix_small_offset_bound (4 * Z.of_nat index + 4) ltac:(lia)) as END.
    unfold Ptrofs.max_unsigned in END; change (size_chunk Mint32) with 4 in *; lia.
Qed.

Fixpoint indexed_store_code array (values : nat -> Int.int) indices :=
  match indices with
  | [] => Sskip
  | index :: rest => Ssequence (indexed_store_statement array index (values index))
      (indexed_store_code array values rest)
  end.

Theorem indexed_store_code_encode fe ge locals array block values indices :
  matrix_array_binding ge locals array block -> Forall (fun index => (index < 4)%nat) indices ->
  forall le memory final,
  schedule_run compcert_store_scheduling (map (indexed_store_action block values) indices) memory final ->
  exec_stmt fe ge locals le memory (indexed_store_code array values indices) E0 le final Out_normal.
Proof.
  intros ARRAY RANGE; induction RANGE as [|index rest BOUND RANGE IH]; intros le memory final RUN.
  - inversion RUN; subst; constructor.
  - inversion RUN; subst; cbn [indexed_store_code].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply indexed_store_statement_encode; [exact ARRAY|exact BOUND|eassumption].
    + apply IH; eassumption.
Qed.

Lemma checked_matrix_schedule_bounds target :
  check_index_schedule row_index_order target = true -> Forall (fun index => (index < 4)%nat) target.
Proof.
  intro CHECK.
  pose proof (@check_schedule_sound mem nat (indexed_store_model 1%positive matrix_index_values)
    Nat.eq_dec index_independentb index_independentb_sound row_index_order target CHECK) as CERT.
  pose proof (schedule_certificate_permutation CERT) as ORDER.
  eapply Permutation_Forall; [exact ORDER|].
  unfold row_index_order; repeat constructor; lia.
Qed.

Definition matrix_scheduled_target array row column indices :=
  Ssequence (indexed_store_code array matrix_index_values indices)
    (Ssequence (Sset column (matrix_constant 2)) (Sset row (matrix_constant 2))).

Theorem matrix_scheduled_target_encode fe ge locals le memory array row column block indices final :
  matrix_array_binding ge locals array block ->
  check_index_schedule row_index_order indices = true ->
  schedule_run compcert_store_scheduling (map (indexed_store_action block matrix_index_values) indices)
    memory final ->
  exec_stmt fe ge locals le memory (matrix_scheduled_target array row column indices) E0
    (PTree.set row (Vint (Int.repr 2)) (PTree.set column (Vint (Int.repr 2)) le)) final Out_normal.
Proof.
  intros ARRAY CHECK RUN; unfold matrix_scheduled_target.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := final).
  - eapply indexed_store_code_encode; [exact ARRAY|apply checked_matrix_schedule_bounds; exact CHECK|exact RUN].
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0);
      unfold matrix_constant; constructor; constructor.
Qed.

Print Assumptions indexed_store_code_encode.
Print Assumptions matrix_scheduled_target_encode.
