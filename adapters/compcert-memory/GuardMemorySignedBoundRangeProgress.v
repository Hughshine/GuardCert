From Stdlib Require Import List.
From compcert.lib Require Import Coqlib.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightRegionProgress ClightFragmentProgress ClightSequenceProgress.
From GuardMemory Require Import GuardMemoryLongControl GuardMemoryLongProgressControl GuardMemoryLongRangeSource
  GuardMemorySignedLongBoundControl GuardMemorySignedBoundLoadedProgress GuardMemorySignedBoundRawProgress.
Set Implicit Arguments.

Definition signed_bound_from_framed_progress iterator initial bound
  (BOUND_TYPE : signed_long_bound_type bound) protected (FRESH : ~ In iterator protected)
  body (F : framed_progress body (iterator::protected)) :
  framed_progress (memory_long_from_loop iterator initial (long_counter_condition iterator bound) body) protected.
Proof.
  apply sequence_framed_progress.
  - apply finite_framed_progress; cbn [frame_statement].
    destruct (in_dec peq iterator protected); [contradiction|reflexivity].
  - apply signed_bound_loaded_framed_progress; assumption.
Defined.
Definition signed_bound_from_region_progress iterator initial bound
  (BOUND_TYPE : signed_long_bound_type bound) protected (FRESH : ~ In iterator protected)
  body (F : framed_progress body (iterator::protected)) :
  region_progress (memory_long_from_loop iterator initial (long_counter_condition iterator bound) body).
Proof.
  apply sequence_region_progress with (protected:=protected).
  - apply finite_framed_progress; cbn [frame_statement].
    destruct (in_dec peq iterator protected); [contradiction|reflexivity].
  - apply signed_bound_loaded_framed_progress; assumption.
Defined.
Definition signed_bound_raw_from_framed_progress iterator initial bound
  (BOUND_TYPE : signed_long_bound_type bound) protected (FRESH : ~ In iterator protected)
  body (F : framed_progress body (iterator::protected)) :
  framed_progress (long_raw_from_loop iterator initial bound body) protected.
Proof.
  apply sequence_framed_progress.
  - apply finite_framed_progress; cbn [frame_statement].
    destruct (in_dec peq iterator protected); [contradiction|reflexivity].
  - apply signed_bound_raw_loaded_framed_progress; assumption.
Defined.
Definition signed_bound_raw_from_region_progress iterator initial bound
  (BOUND_TYPE : signed_long_bound_type bound) protected (FRESH : ~ In iterator protected)
  body (F : framed_progress body (iterator::protected)) :
  region_progress (long_raw_from_loop iterator initial bound body).
Proof.
  apply sequence_region_progress with (protected:=protected).
  - apply finite_framed_progress; cbn [frame_statement].
    destruct (in_dec peq iterator protected); [contradiction|reflexivity].
  - apply signed_bound_raw_loaded_framed_progress; assumption.
Defined.
Print Assumptions signed_bound_from_framed_progress.
Print Assumptions signed_bound_from_region_progress.
Print Assumptions signed_bound_raw_from_framed_progress.
Print Assumptions signed_bound_raw_from_region_progress.
