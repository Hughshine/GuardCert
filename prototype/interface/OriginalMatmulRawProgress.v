From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Ctypes Clight.
From Guard Require Import ClightRegionProgress ClightFragmentProgress.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleMatmul
  GuardMemoryLongRawLoadedProgress.
From GuardInterface Require Import OriginalMatmulRawSource.
From GuardOriginalMatmul Require Import OriginalMatmul OriginalMatmulBody.
Import ListNotations.
Set Implicit Arguments.

(** These proofs concern the unchanged source's execution, including guard
    refusal. No loaded-header stability or accepted numeric range is needed. *)
Definition original_matmul_raw_assignment_framed :
  framed_progress (Ssequence Sskip (double_matmul_body original_matmul_site)) [_k__1;_j;_i].
Proof. apply finite_framed_progress; reflexivity. Defined.
Definition original_matmul_raw_inner_framed :
  framed_progress (raw_original_long_loop _k__1 _K (Ssequence Sskip (double_matmul_body original_matmul_site))) [_j;_i].
Proof.
  exact (@long_raw_initialized_framed_progress _k__1 (Evar _K memory_long_type) eq_refl [_j;_i]
    ltac:(vm_compute; intuition congruence) (Ssequence Sskip (double_matmul_body original_matmul_site)) original_matmul_raw_assignment_framed).
Defined.
Definition original_matmul_raw_middle_framed :
  framed_progress (raw_original_long_loop _j _N (raw_original_long_loop _k__1 _K
    (Ssequence Sskip (double_matmul_body original_matmul_site)))) [_i].
Proof.
  exact (@long_raw_initialized_framed_progress _j (Evar _N memory_long_type) eq_refl [_i]
    ltac:(vm_compute; intuition congruence) (raw_original_long_loop _k__1 _K (Ssequence Sskip (double_matmul_body original_matmul_site)))
    original_matmul_raw_inner_framed).
Defined.
Definition original_matmul_raw_source_progress : region_progress raw_original_matmul_region.
Proof.
  rewrite original_matmul_raw_frontend_shape.
  exact (@long_raw_initialized_region_progress _i (Evar _M memory_long_type) eq_refl []
    ltac:(cbn; tauto) (raw_original_long_loop _j _N (raw_original_long_loop _k__1 _K
      (Ssequence Sskip (double_matmul_body original_matmul_site)))) original_matmul_raw_middle_framed).
Defined.

Print Assumptions original_matmul_raw_assignment_framed.
Print Assumptions original_matmul_raw_inner_framed.
Print Assumptions original_matmul_raw_middle_framed.
Print Assumptions original_matmul_raw_source_progress.
