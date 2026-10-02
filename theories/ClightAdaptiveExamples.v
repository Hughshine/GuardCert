From Stdlib Require Import List ZArith.
From compcert.common Require Import Errors Smallstep.
From compcert.cfrontend Require Import Clight Csyntax Csem.
From Guard Require Import ClightCountedLoop ClightRegionRule ClightZeroTrip
  ClightAdaptiveRegion ClightProgressClassifier ClightFrontendLoopProtocol ClightFrontendRegion
  AdaptiveRegionCompiler.
Import Clight.

(** This checks replacement of the entire loop node, rather than a finite
    store pair in its body. The generated guard never reads body memory. *)
Example generated_zero_trip_code iterator bound body :
  generated_region (zero_trip_rule iterator bound body) =
  Sifthenelse (counter_condition iterator bound) (counted_loop iterator bound body) Sskip.
Proof. reflexivity. Qed.

Example entire_loop_is_selected :
  AdaptiveRegion.transform_statement progress_supported select_zero_trip
    (counted_loop 1%positive 2%positive Sskip) =
  Sifthenelse (counter_condition 1%positive 2%positive)
    (counted_loop 1%positive 2%positive Sskip) Sskip.
Proof. vm_compute; reflexivity. Qed.

Example unsafe_counter_body_keeps_original :
  AdaptiveRegion.transform_statement progress_supported select_zero_trip
    (counted_loop 1%positive 2%positive (counter_increment 1%positive)) =
  counted_loop 1%positive 2%positive (counter_increment 1%positive).
Proof. vm_compute; reflexivity. Qed.

Theorem zero_trip_whole_program_compile_correct : forall p target,
  compile_progress_regions p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof. exact compile_progress_regions_correct. Qed.

Print Assumptions zero_trip_whole_program_compile_correct.

Example frontend_entire_loop_is_selected :
  AdaptiveRegion.transform_statement frontend_progress_supported select_loop_zero_trip
    (frontend_counted_loop 1%positive 2%positive Sskip) =
  Sifthenelse (counter_condition 1%positive 2%positive)
    (frontend_counted_loop 1%positive 2%positive Sskip) Sskip.
Proof. vm_compute; reflexivity. Qed.

Example frontend_counter_body_is_refused :
  frontend_progress_supported (frontend_counted_loop 1%positive 2%positive
    (counter_increment 1%positive)) = false.
Proof. vm_compute; reflexivity. Qed.
