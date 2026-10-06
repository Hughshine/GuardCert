From Stdlib Require Import List Bool.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Csyntax Csem Clight.
From compcert.x86 Require Import Asm.
From Guard Require Import ClightRegionProgress ClightStructuredProgress ClightPrivateRegion ClightPrivatePool ClightTempFootprint.
From GuardInterface Require Import ClightReadonlyCompiler ClightReadonlyProjectedCompiler ClightReadonlyRuleEmbedding
  ClightPreloadCompiler ClightReadonlyMatrix ClightReadonlyLoopUpdates ClightReadonlyCellSwap
  ClightStableLoadCompiler ClightLoadedBoundCompiler ClightRuntimeStrideCompiler ClightIndexedLoadCompiler ClightIndexedBoundCompiler ClightEqualityCompiler ClightReadonlyTestCompiler ClightEqualityHeadCompiler ClightLoadedMatrixCompiler ClightLoadedMatrixSyntax ClightLoadedRectangleCompiler ClightLoadedStrideCompiler ClightMixedLoadedProgress ClightDualLoadedUnitCompiler ClightDualLoadedMatrixCompiler ClightDualRepeatedCompiler
  ClightSharedProjectedCompiler ClightSimplifiedDualRectangleCompiler.
Set Implicit Arguments.

(** This is a user pass combining existing rules. Selection priority and
    traversal remain outside the generic guarded-rewrite framework. *)
Definition choose_common_exact source : option (readonly_clight_rule source) :=
  match choose_dual_repeat source with
  | Some rule => Some rule
  | None => match choose_dual_unit source with
  | Some rule => Some rule
  | None => match choose_equality_loop source with
  | Some rule => Some rule
  | None => match choose_readonly_matrix source with
  | Some rule => Some rule
  | None => match choose_runtime_stride source with
    | Some rule => Some rule
    | None => match choose_readonly_rectangles source with
    | Some rule => Some rule
    | None => match choose_cell_pair source with
      | Some rule => Some rule
      | None => choose_preload_rewrite source end end end end end end end.
Definition choose_common_rewrite live pool source : option (readonly_projected_clight_rule live source) :=
  match choose_dual_matrix live pool source with
  | Some rule => Some rule
  | None => match choose_loaded_matrix live pool source with
  | Some rule => Some rule
  | None => match choose_loaded_rectangle live pool source with
  | Some rule => Some rule
  | None => match choose_loaded_stride live pool source with
  | Some rule => Some rule
  | None => match choose_indexed_bound_default live pool source with
  | Some rule => Some rule
  | None => match choose_loaded_bound live pool source with
  | Some rule => Some rule
  | None => match choose_indexed_default live pool source with
    | Some rule => Some rule
    | None => match choose_stable_load live pool source with
    | Some rule => Some rule
    | None => match choose_common_exact source with
      | Some rule => embed_quiet_exact_rule live rule
      | None => None end end end end end end end end end.
Definition common_progress_supported source :=
  mixed_loaded_progress_supported source || (loaded_nested_supported source ||
    (equality_loop_supported source || (indexed_bound_progress_supported source || structured_progress_supported source))).
Theorem common_progress_supported_sound source : common_progress_supported source = true ->
  exists MODEL : region_progress source, True.
Proof.
  unfold common_progress_supported; rewrite orb_true_iff; intros [MIXED|REST].
  { apply mixed_loaded_progress_supported_sound; exact MIXED. }
  apply orb_true_iff in REST as [NESTED|OLD].
  - apply loaded_nested_supported_sound; exact NESTED.
  - apply orb_true_iff in OLD as [EQUALITY|REST].
    + apply equality_loop_supported_sound; exact EQUALITY.
    + apply orb_true_iff in REST as [LOADED|STRUCTURED].
      * apply indexed_bound_progress_supported_sound; exact LOADED.
      * apply structured_progress_supported_sound; exact STRUCTURED.
Qed.
(** Existing rules keep their priority and direct lowering. The two-cache
    rule uses a third slot for shared dispatch, with its original readonly
    certificate and local proof. This is a choice made by the user pass. *)
Definition common_region_selection live pool source : option statement :=
  match projected_readonly_selection choose_common_rewrite live pool source with
  | Some target => Some target
  | None => shared_projected_selection choose_simplified_dual_rectangle live pool source end.
Theorem common_region_selection_sound live pool source target :
  common_region_selection live pool source = Some target ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  unfold common_region_selection.
  destruct (projected_readonly_selection choose_common_rewrite live pool source) as [old|] eqn:OLD.
  - intro SAME; injection SAME as SAME; subst old.
    eapply projected_readonly_selection_sound; exact OLD.
  - apply shared_projected_selection_sound.
Qed.
Definition transform_common_regions (p : Clight.program) :=
  transform_private_program common_progress_supported common_region_selection
    (propose_private_names (program_temps p) 3) p.
Theorem transform_common_regions_correct p :
  forward_simulation (Clight.semantics2 p) (Clight.semantics2 (transform_common_regions p)).
Proof.
  apply transform_private_program_correct; [exact common_progress_supported_sound|exact common_region_selection_sound].
Qed.
Definition compile_common_rewrites := compile_readonly_tests_after choose_equality_head transform_common_regions.
Theorem compile_common_rewrites_correct p target : compile_common_rewrites p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof.
  apply compile_readonly_tests_after_correct, transform_common_regions_correct.
Qed.
Print Assumptions choose_common_rewrite.
Print Assumptions common_region_selection_sound.
Print Assumptions transform_common_regions_correct.
Print Assumptions compile_common_rewrites_correct.
