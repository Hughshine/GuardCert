From Stdlib Require Import List PArith.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From GuardMemory Require Import GuardMemoryWindowBackend.
From GuardAffineNest Require Import AffineNestGuardPackage AffineNestMultiStaticPackage AffineNestPackageDecode AffineNestPackageRanges.
From GuardInterface Require Import ClightNestedConstantSite ClightNestedConstantSiteExample
  ClightNestedConstantNumericExample ClightNestedConstantMultiSite ClightNestedConstantMultiFactory
  ClightSignedExpressionProgress ClightNestedConstantMultiExecution ClightLoadedAffineNumericExamples.
Import ListNotations.

Definition ncs_multi_example_allocated :=
  [101%positive;104%positive;102%positive;105%positive;103%positive;106%positive;
   201%positive;204%positive;202%positive;205%positive;203%positive;206%positive;107%positive;
   4%positive;5%positive;51%positive;50%positive].

Definition ncs_multi_example_checked delta allocated := ncs_example_present(check_ncs_multi_site
  (ncs_original(ncs_example_shape delta))ncn_parameters ncs_example_live allocated
  (ncn_proposal 107%positive)(ncs_example_shape delta)).

Example original_nested_multi_site_is_accepted : ncs_multi_example_checked Int.one ncs_multi_example_allocated=true.
Proof. vm_compute; reflexivity. Qed.

Example original_nested_zero_offset_multi_site_is_accepted : ncs_multi_example_checked Int.zero ncs_multi_example_allocated=true.
Proof. vm_compute; reflexivity. Qed.

Example missing_second_scan_resources_refused : ncs_multi_example_checked Int.one
  [101%positive;104%positive;102%positive;105%positive;103%positive;106%positive;107%positive]=false.
Proof. vm_compute; reflexivity. Qed.

Example source_nested_progress_is_host_supported :
  signed_expression_region_progress_supported(ncs_original(ncs_example_shape Int.one))=true.
Proof. vm_compute; reflexivity. Qed.

Example captured_private_inputs_are_not_candidate_counters :
  ncs_candidate_pairs [4%positive;5%positive;50%positive;51%positive]
    [(4%positive,301%positive);(302%positive,5%positive);(303%positive,304%positive);
     (50%positive,51%positive)]=[(303%positive,304%positive)].
Proof. vm_compute; reflexivity. Qed.

Definition ncs_multi_zero_site : ncs_multi_site(ncs_original(ncs_example_shape Int.zero))ncn_parameters ncs_example_live
  ncs_multi_example_allocated(ncn_proposal 107%positive)(ncs_example_shape Int.zero).
Proof.
  pose proof original_nested_zero_offset_multi_site_is_accepted as CHECK; unfold ncs_multi_example_checked in CHECK.
  destruct(check_ncs_multi_site(ncs_original(ncs_example_shape Int.zero))ncn_parameters ncs_example_live
    ncs_multi_example_allocated(ncn_proposal 107%positive)(ncs_example_shape Int.zero)) as [site|];
    [exact site|discriminate].
Defined.

Theorem actual_original_empty_multi_guard_receipt fe ge locals : exists checked,
  ncs_multi_receipt ncs_multi_zero_site fe ge locals ncs_empty_temps lnf_zero_memory ncs_empty_temps lnf_zero_memory checked.
Proof. apply ncs_multi_guard_execution; apply checked_original_empty_source_executes. Qed.

Example checked_three_axis_source_candidate_has_actual_backend_code : exists code,
  compile_window_multi_pointer_buffer_loop(affine_proposed_pointers(ncn_proposal 107%positive))
    (affine_package_context ncn_parameters(ncn_proposal 107%positive))
    (affine_package_encoder_bounds(ncn_proposal 107%positive))
    (ncs_ports(ncs_original(ncs_example_shape Int.zero))ncn_parameters ncs_example_live(ncs_example_shape Int.zero))
    [(301%positive,302%positive);(303%positive,304%positive);(305%positive,306%positive);
     (307%positive,308%positive);(309%positive,310%positive);(311%positive,312%positive)]
    (affine_multi_source_loop(ncs_multi_package ncs_multi_zero_site))=Some code.
Proof. vm_compute; eexists; reflexivity. Qed.

Print Assumptions original_nested_multi_site_is_accepted.
Print Assumptions original_nested_zero_offset_multi_site_is_accepted.
Print Assumptions missing_second_scan_resources_refused.
Print Assumptions source_nested_progress_is_host_supported.
Print Assumptions captured_private_inputs_are_not_candidate_counters.
Print Assumptions actual_original_empty_multi_guard_receipt.
Print Assumptions checked_three_axis_source_candidate_has_actual_backend_code.
