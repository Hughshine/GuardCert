From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Integers Coqlib.
From compcert.cfrontend Require Import Clight Ctypes Cop.
From Guard Require Import ClightSyntaxEquality ClightCountedLoop.
From GuardMemory Require Import GuardMemoryNaryAffineAccess GuardMemoryNaryAffineExpressions GuardMemoryNaryAccessCheck
  GuardMemoryNaryCompute GuardMemoryFlatArrayBackend GuardMemoryPointerCompute GuardMemoryPointerNaryAccess
  GuardMemorySourceParameters GuardMemorySourceValueInterface.
From GuardMemory Require Import GuardMemoryIntervalBox GuardMemoryWindowAccess GuardMemoryWindowCompute.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition window_signed_check value := (Int.min_signed <=? value) && (value <=? Int.max_signed).
Lemma window_signed_check_sound value : window_signed_check value = true -> signed_range value.
Proof. unfold window_signed_check,signed_range; rewrite andb_true_iff,!Z.leb_le; tauto. Qed.
Definition window_access_check bounds lower upper layout access :=
  window_signed_check lower && window_signed_check (upper-1) &&
  interval_window_box_check bounds lower upper (memory_nary_access_index access) &&
  match memory_encode_nary_index layout (memory_nary_access_expression access) with
  | Some term => if memory_nary_term_eq term (memory_nary_access_index access) then true else false
  | None => false end.
Lemma window_access_check_sound bounds lower upper layout access :
  window_access_check bounds lower upper layout access = true -> window_access_valid bounds lower upper layout access.
Proof.
  unfold window_access_check; rewrite !andb_true_iff; intros [[[LOW HIGH] BOX] ENCODE].
  destruct (memory_encode_nary_index layout (memory_nary_access_expression access)) as [term|] eqn:EXPRESSION;
    [|discriminate].
  destruct (memory_nary_term_eq term (memory_nary_access_index access)) as [SAME|]; [subst term|discriminate].
  split; [apply window_signed_check_sound; exact LOW|].
  split; [apply window_signed_check_sound; exact HIGH|].
  split; [exact EXPRESSION|].
  intros values RANGE; eapply interval_window_box_sound; eassumption.
Qed.
Definition window_compute_check bounds lower upper layout scalars operation :=
  window_access_check bounds lower upper layout (memory_nary_compute_write operation) &&
  forallb (window_access_check bounds lower upper layout) (memory_nary_compute_reads operation) &&
  match compile_flat_value (memory_pointer_register_codes (layout++scalars))
    (map memory_pointer_nary_code (memory_nary_compute_reads operation))
    (memory_nary_compute_value operation) with
  | Some code => if expression_eq code (memory_nary_compute_source operation)
      then memory_source_reads_check (map memory_pointer_nary_code (memory_nary_compute_reads operation))
        (memory_nary_compute_value operation) else false
  | None => false end.
Lemma window_compute_check_sound bounds lower upper layout scalars operation :
  window_compute_check bounds lower upper layout scalars operation = true ->
  window_compute_valid bounds lower upper layout scalars operation.
Proof.
  unfold window_compute_check; rewrite !andb_true_iff; intros [[WRITE READS] VALUE].
  destruct (compile_flat_value (memory_pointer_register_codes (layout++scalars))
    (map memory_pointer_nary_code (memory_nary_compute_reads operation)) (memory_nary_compute_value operation))
    as [code|] eqn:COMPILE; [|discriminate].
  destruct (expression_eq code (memory_nary_compute_source operation)) as [SAME|]; [|discriminate].
  split; [apply window_access_check_sound; exact WRITE|]; split.
  - apply Forall_forall; intros access MEMBER; apply window_access_check_sound.
    apply forallb_forall with (x := access) in READS; assumption.
  - split; [rewrite SAME in COMPILE; exact COMPILE|exact VALUE].
Qed.
Print Assumptions window_access_check_sound.
Print Assumptions window_compute_check_sound.
