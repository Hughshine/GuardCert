From Stdlib Require Import List ZArith.
From compcert.common Require Import AST Smallstep.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightPrivateRegion ClightTempFootprint ClightSyntaxEquality.
From GuardMemory Require Import GuardMemoryTiledCompiler GuardMemoryAffineInnerPointerSyntax
  GuardMemoryParametricWidth.
From GuardInterface Require Import ClightAffineLoadedPointerRewrite ClightAffineLoadedPointerExample
  ClightAffinePointerGuardExamples ClightAffineInnerPointerCandidate
  ClightLoadedSequenceProgress ClightLoadedRegionHost ClightSourceObservation
  ClightAffineInnerPointerSourceGuard ClightAffinePointerGuard ClightObservedPointerSyntax.
From GuardInterface Require Import ClightLoadedBoundSyntax.
Import ListNotations.
Set Implicit Arguments.

(** These are normalized-AST and placement witnesses. They do not establish
    that a C frontend emits the fixture's fixed temporary identifiers. *)
Example alp_loaded_progress_accepts : loaded_sequence_progress_supported alp_source = true.
Proof. vm_compute; reflexivity. Qed.
Example alp_observed_progress_accepts : loaded_sequence_progress_supported alp_observed_source = true.
Proof. vm_compute; reflexivity. Qed.
Example alp_mutating_bound_progress_accepts :
  loaded_sequence_progress_supported (loaded_bound_loop ap_i ap_p
    (Ssequence ap_outer (Sassign (signed_load ap_p) (ap_constant 0%Z)))) = true.
Proof. vm_compute; reflexivity. Qed.
Example alp_loaded_iterator_write_rejected :
  loaded_sequence_progress_supported
    (ClightLoadedBoundSyntax.loaded_bound_loop ap_i ap_p
      (Ssequence (Sset ap_i ap_header) ap_outer)) = false.
Proof. vm_compute; reflexivity. Qed.

Definition alp_reassociated_source :=
  Ssequence (Sset ap_n (signed_load ap_p))
    (Ssequence (Sset 8%positive (signed_load ap_p))
      (Ssequence (Sset 9%positive (signed_load ap_q))
        (Ssequence alp_source (Sassign (signed_load ap_q) (ap_constant 17%Z))))).
Example alp_reassociated_profile_accepts :
  (match describe_observed_pointer_source alp_reassociated_source with
   | Some observed => if statement_eq
       (Ssequence (source_load_prefix (observed_source_loads observed)) (observed_source_loop observed))
       alp_observed_source then true else false
   | None => false end) = true.
Proof. vm_compute; reflexivity. Qed.
Example alp_reassociated_progress_accepts :
  loaded_sequence_progress_supported alp_reassociated_source = true.
Proof. vm_compute; reflexivity. Qed.

Definition alp_candidate_table live
  (candidate : affine_inner_pointer_candidate_package alp_cached_package live) width alias :=
  [(alp_observed_source,
    Ssequence (source_load_prefix alp_loads) (alp_guarded_candidate candidate width alias))].

Theorem alp_candidate_table_correct live
  (candidate : affine_inner_pointer_candidate_package alp_cached_package live) width alias :
  compile_memory_source_width (affine_inner_pointer_column_limit alp_cached_package)
    (affine_inner_pointer_row (affine_inner_pointer_shape alp_cached_package))
    (memory_affine_inner_pointer_header (affine_inner_pointer_shape alp_cached_package)
      (affine_inner_pointer_expression alp_cached_package))
    (affine_inner_pointer_header_bounds (affine_inner_pointer_row_limit alp_cached_package)
      (affine_inner_pointer_header_limits alp_cached_package))
    (affine_inner_pointer_expression alp_cached_package) = Some width ->
  compile_affine_inner_pointer_package_envelopes alp_cached_package = Some alias ->
  Forall (fun pair => PrivateRegion.projected_region_contract live (fst pair) (snd pair))
    (alp_candidate_table candidate width alias).
Proof.
  intros WIDTH ALIAS; apply Forall_cons; [|apply Forall_nil].
  cbn; apply alp_observed_candidate_contract; assumption.
Qed.

Theorem alp_installed_program_correct pool p
  (candidate : affine_inner_pointer_candidate_package alp_cached_package (program_temps p)) width alias :
  compile_memory_source_width (affine_inner_pointer_column_limit alp_cached_package)
    (affine_inner_pointer_row (affine_inner_pointer_shape alp_cached_package))
    (memory_affine_inner_pointer_header (affine_inner_pointer_shape alp_cached_package)
      (affine_inner_pointer_expression alp_cached_package))
    (affine_inner_pointer_header_bounds (affine_inner_pointer_row_limit alp_cached_package)
      (affine_inner_pointer_header_limits alp_cached_package))
    (affine_inner_pointer_expression alp_cached_package) = Some width ->
  compile_affine_inner_pointer_package_envelopes alp_cached_package = Some alias ->
  forward_simulation (Clight.semantics2 p)
    (Clight.semantics2 (apply_loaded_region_table pool (alp_candidate_table candidate width alias) p)).
Proof.
  intros WIDTH ALIAS; apply apply_loaded_region_table_correct,
    alp_candidate_table_correct; assumption.
Qed.

Print Assumptions alp_loaded_progress_accepts.
Print Assumptions alp_observed_progress_accepts.
Print Assumptions alp_mutating_bound_progress_accepts.
Print Assumptions alp_loaded_iterator_write_rejected.
Print Assumptions alp_reassociated_profile_accepts.
Print Assumptions alp_reassociated_progress_accepts.
Print Assumptions alp_candidate_table_correct.
Print Assumptions alp_installed_program_correct.
