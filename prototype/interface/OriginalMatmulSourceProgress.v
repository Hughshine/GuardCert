From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Ctypes Clight.
From Guard Require Import ClightRegionProgress ClightFragmentProgress.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleMatmul
  GuardMemoryLongLoadedProgress.
From GuardOriginalMatmul Require Import OriginalMatmul OriginalMatmulBody.
Import ListNotations.
Set Implicit Arguments.

(** These proofs concern the unchanged source's execution, including guard
    refusal. No loaded-header stability or accepted numeric range is needed. *)
Definition original_matmul_assignment_framed :
  framed_progress (double_matmul_body original_matmul_site) [_k__1;_j;_i].
Proof. apply finite_framed_progress; reflexivity. Defined.
Definition original_matmul_inner_framed :
  framed_progress (original_long_loop _k__1 _K (double_matmul_body original_matmul_site)) [_j;_i].
Proof.
  exact (@long_initialized_framed_progress _k__1 (Evar _K memory_long_type) eq_refl [_j;_i]
    ltac:(vm_compute; intuition congruence) (double_matmul_body original_matmul_site) original_matmul_assignment_framed).
Defined.
Definition original_matmul_middle_framed :
  framed_progress (original_long_loop _j _N (original_long_loop _k__1 _K
    (double_matmul_body original_matmul_site))) [_i].
Proof.
  exact (@long_initialized_framed_progress _j (Evar _N memory_long_type) eq_refl [_i]
    ltac:(vm_compute; intuition congruence) (original_long_loop _k__1 _K (double_matmul_body original_matmul_site))
    original_matmul_inner_framed).
Defined.
Definition original_matmul_source_progress : region_progress original_matmul_region.
Proof.
  exact (@long_initialized_region_progress _i (Evar _M memory_long_type) eq_refl []
    ltac:(cbn; tauto) (original_long_loop _j _N (original_long_loop _k__1 _K
      (double_matmul_body original_matmul_site))) original_matmul_middle_framed).
Defined.

Print Assumptions original_matmul_assignment_framed.
Print Assumptions original_matmul_inner_framed.
Print Assumptions original_matmul_middle_framed.
Print Assumptions original_matmul_source_progress.
