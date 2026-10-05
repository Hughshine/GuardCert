From Stdlib Require Import List Bool.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Csyntax Csem Clight.
From compcert.x86 Require Import Asm.
From Guard Require Import ClightRegionProgress ClightStructuredProgress.
From GuardInterface Require Import ClightReadonlyCompiler ClightReadonlyProjectedCompiler ClightReadonlyRuleEmbedding
  ClightPreloadCompiler ClightReadonlyMatrix ClightReadonlyLoopUpdates ClightReadonlyCellSwap
  ClightStableLoadCompiler ClightLoadedBoundCompiler ClightRuntimeStrideCompiler ClightIndexedLoadCompiler ClightIndexedBoundCompiler ClightEqualityCompiler ClightReadonlyTestCompiler ClightEqualityHeadCompiler.
Set Implicit Arguments.

(** This is a user pass combining existing rules. Selection priority and
    traversal remain outside the generic guarded-rewrite framework. *)
Definition choose_common_exact source : option (readonly_clight_rule source) :=
  match choose_equality_loop source with
  | Some rule => Some rule
  | None => match choose_readonly_matrix source with
  | Some rule => Some rule
  | None => match choose_runtime_stride source with
    | Some rule => Some rule
    | None => match choose_readonly_rectangles source with
    | Some rule => Some rule
    | None => match choose_cell_pair source with
      | Some rule => Some rule
      | None => choose_preload_rewrite source end end end end end.
Definition choose_common_rewrite live pool source : option (readonly_projected_clight_rule live source) :=
  match choose_indexed_bound_default live pool source with
  | Some rule => Some rule
  | None => match choose_loaded_bound live pool source with
  | Some rule => Some rule
  | None => match choose_indexed_default live pool source with
    | Some rule => Some rule
    | None => match choose_stable_load live pool source with
    | Some rule => Some rule
    | None => match choose_common_exact source with
      | Some rule => embed_quiet_exact_rule live rule
      | None => None end end end end end.
Definition common_progress_supported source :=
  equality_loop_supported source || (indexed_bound_progress_supported source || structured_progress_supported source).
Theorem common_progress_supported_sound source : common_progress_supported source = true ->
  exists MODEL : region_progress source, True.
Proof.
  unfold common_progress_supported; rewrite orb_true_iff; intros [EQUALITY|REST].
  - apply equality_loop_supported_sound; exact EQUALITY.
  - apply orb_true_iff in REST as [LOADED|STRUCTURED].
    + apply indexed_bound_progress_supported_sound; exact LOADED.
    + apply structured_progress_supported_sound; exact STRUCTURED.
Qed.
Definition compile_common_rewrites := compile_readonly_tests_after choose_equality_head
  (transform_projected_readonly choose_common_rewrite common_progress_supported 1).
Theorem compile_common_rewrites_correct p target : compile_common_rewrites p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof.
  apply compile_readonly_tests_after_correct; intro program.
  apply transform_projected_readonly_correct, common_progress_supported_sound.
Qed.
Print Assumptions choose_common_rewrite.
Print Assumptions compile_common_rewrites_correct.
