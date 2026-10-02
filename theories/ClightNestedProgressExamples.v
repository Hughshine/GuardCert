From Stdlib Require Import List ZArith.
From compcert.lib Require Import Integers.
From compcert.common Require Import Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Cop Clight Csem.
From Guard Require Import ClightCountedLoop ClightFrontendLoopProtocol ClightFrontendRegion
  ClightRegionRule ClightRegionProgress ClightAdaptiveRegion ClightStructuredProgress AdaptiveRegionCompiler.
Import ListNotations.
Import Clight.

Definition reset_inner := Sset 3%positive (Econst_int Int.zero type_int32s).
Definition nested_source body := frontend_counted_loop 1%positive 2%positive
  (Ssequence reset_inner (frontend_counted_loop 3%positive 4%positive body)).

Example two_nested_frontend_loops_supported : structured_progress_supported (nested_source Sskip) = true.
Proof. vm_compute; reflexivity. Qed.
Example inner_loop_may_update_other_temporary :
  structured_progress_supported (nested_source (Sset 5%positive (Econst_int Int.one type_int32s))) = true.
Proof. vm_compute; reflexivity. Qed.
Example inner_body_cannot_update_outer_iterator :
  structured_progress_supported (nested_source (counter_increment 1%positive)) = false.
Proof. vm_compute; reflexivity. Qed.
Example inner_body_cannot_update_outer_bound :
  structured_progress_supported (nested_source (counter_increment 2%positive)) = false.
Proof. vm_compute; reflexivity. Qed.
Example inner_body_cannot_update_inner_iterator :
  structured_progress_supported (nested_source (counter_increment 3%positive)) = false.
Proof. vm_compute; reflexivity. Qed.
Example reused_nested_iterator_refused : structured_progress_supported
  (frontend_counted_loop 1%positive 2%positive
    (frontend_counted_loop 1%positive 4%positive Sskip)) = false.
Proof. vm_compute; reflexivity. Qed.
Example three_nested_loops_supported : structured_progress_supported
  (nested_source (Ssequence (Sset 5%positive (Econst_int Int.zero type_int32s))
    (frontend_counted_loop 5%positive 6%positive Sskip))) = true.
Proof. vm_compute; reflexivity. Qed.
Example mixed_loop_shapes_supported : structured_progress_supported
  (frontend_counted_loop 1%positive 2%positive
    (Ssequence reset_inner (counted_loop 3%positive 4%positive Sskip))) = true.
Proof. vm_compute; reflexivity. Qed.

Example complete_nested_loop_is_selected :
  AdaptiveRegion.transform_statement structured_progress_supported select_loop_zero_trip (nested_source Sskip) =
  Sifthenelse (counter_condition 1%positive 2%positive) (nested_source Sskip) Sskip.
Proof. vm_compute; reflexivity. Qed.

Theorem nested_source_has_actual_progress : exists MODEL : region_progress (nested_source Sskip), True.
Proof. apply structured_progress_supported_sound; exact two_nested_frontend_loops_supported. Qed.
Theorem nested_frontend_compiler_correct p target : compile_progress_regions p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof. exact (compile_progress_regions_correct p target). Qed.
Print Assumptions nested_source_has_actual_progress.
Print Assumptions nested_frontend_compiler_correct.
