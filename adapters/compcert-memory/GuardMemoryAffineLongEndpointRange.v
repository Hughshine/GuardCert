From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import Linalg.
From Guard Require Import AffineIntegerIntervals.
From GuardMemory Require Import GuardMemoryAffineLongEndpoint GuardMemoryLongExpressionCapture.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Definition affine_long_endpoint_interval_check intervals (row : constraint) :=
  match affine_integer_interval (fst row) (snd row) intervals with
  | Some (lower,upper) => (Int64.min_signed <=? lower) && (upper <=? Int64.max_signed)
  | None => false end.
Theorem affine_long_endpoint_interval_nonwrap intervals row valuation controls :
  Forall2 integer_interval_contains intervals (map valuation controls) ->
  affine_long_endpoint_interval_check intervals row = true ->
  affine_long_endpoint_nonwrap row valuation controls.
Proof.
  intros FACTS CHECK; unfold affine_long_endpoint_interval_check in CHECK.
  destruct (affine_integer_interval (fst row) (snd row) intervals) as [[lower upper]|] eqn:INTERVAL;
    [|discriminate].
  apply Bool.andb_true_iff in CHECK; destruct CHECK as [LOWER UPPER].
  apply Z.leb_le in LOWER; apply Z.leb_le in UPPER.
  pose proof (@affine_integer_interval_sound (fst row) (snd row) intervals
    (map valuation controls) (lower,upper) FACTS INTERVAL) as BOUNDS.
  unfold affine_long_endpoint_nonwrap,affine_long_endpoint_value,
    GuardMemoryNaryAffineExpressions.memory_nary_index_value,integer_interval_contains in *; cbn in *; lia.
Qed.

Theorem checked_affine_long_endpoint_capture intervals controls source row valuation fe ge locals temps memory
  cache flag lower upper :
  GuardMemoryLongSourceAffine.decode_long_source_index controls source = Some row ->
  affine_long_endpoint_words valuation controls temps ->
  Forall2 integer_interval_contains intervals (map valuation controls) ->
  affine_long_endpoint_interval_check intervals row = true ->
  Int.min_signed <= lower <= Int.max_signed -> Int.min_signed <= upper <= Int.max_signed ->
  let value := affine_long_endpoint_value row valuation controls in
  exec_stmt fe ge locals temps memory
    (memory_long_expression_capture source cache flag lower upper) E0
    (memory_long_expression_captured temps cache flag (Int64.repr value) lower upper) memory Out_normal /\
  (memory_long_expression_accept (Int64.repr value) lower upper = true ->
    lower <= value <= upper /\ Int.signed (Int64.loword (Int64.repr value)) = value).
Proof.
  intros DECODE WORDS FACTS CHECK LOWER UPPER.
  apply decoded_affine_long_endpoint_capture; try assumption.
  eapply affine_long_endpoint_interval_nonwrap; eauto.
Qed.

(** A small wrapped result does not certify the mathematical affine value.
    The interval checker refuses this 4*x example before capture is licensed
    to supply mathematical facts. It may still be used as an actual I64 check. *)
Example affine_long_wrapped_word_passes_small_machine_check :
  memory_long_expression_accept (Int64.repr 18446744073709551616) 0 98 = true.
Proof. vm_compute; reflexivity. Qed.
Example affine_long_overflow_interval_refused :
  affine_long_endpoint_interval_check [(4611686018427387904,4611686018427387904)] ([4],0) = false.
Proof. vm_compute; reflexivity. Qed.
Example affine_long_constant_endpoint_interval :
  affine_long_endpoint_interval_check [] ([],100) = true.
Proof. vm_compute; reflexivity. Qed.
Example affine_long_outer_endpoint_interval :
  affine_long_endpoint_interval_check [(0,98)] ([1],0) = true.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions affine_long_endpoint_interval_nonwrap.
Print Assumptions checked_affine_long_endpoint_capture.
