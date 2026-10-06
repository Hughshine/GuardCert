From Stdlib Require Import List ZArith.
From compcert.cfrontend Require Import Ctypes Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax.
From GuardInterface Require Import ClightDependentBoundSyntax ClightDependentLoadedSource ClightDependentRegionHost
  ClightAffineDependentSyntax ClightAffineDependentCandidates ClightSourceObservation ClightSignedExpressionProgress
  ClightAffinePointerGuardExamples ClightAffineInnerPointerCandidateExamples ClightAffineInnerPointerCandidates.
Import ListNotations CoreAlarmed.

Definition dp_root := 20%positive.
Definition dp_source := Ssequence (source_load_prefix ap_loads) (dependent_bound_loop ap_i dp_root ap_outer).
Definition dp_profile : affine_inner_pointer_profiler := fun _ => Some ap_profile.
Definition dp_described pointer_cache cache := describe_affine_dependent_source [] pointer_cache cache dp_profile dp_source.
Example actual_compound_header_site_selected : ap_selected (describe_dependent_snapshot_site dp_source) = true.
Proof. vm_compute; reflexivity. Qed.
Example compound_source_without_public_bound_snapshot_selected : ap_selected (dp_described 100%positive 101%positive) = true.
Proof. vm_compute; reflexivity. Qed.
Example private_bound_is_checked_model_cache :
  match dp_described 100%positive 101%positive with
  | Some region => Pos.eqb (affine_inner_pointer_bound (affine_inner_pointer_shape (dependent_region_package region))) 101%positive
  | None => false end = true.
Proof. vm_compute; reflexivity. Qed.
Example original_compound_source_progress_selected : signed_expression_region_progress_supported dp_source = true.
Proof. vm_compute; reflexivity. Qed.
Example same_pointer_and_bound_cache_refused : ap_selected (dp_described 100%positive 100%positive) = false.
Proof. vm_compute; reflexivity. Qed.
Example original_root_cannot_be_private_pointer : ap_selected (dp_described dp_root 101%positive) = false.
Proof. vm_compute; reflexivity. Qed.
Example public_body_pointer_cannot_be_private_bound : ap_selected (dp_described 100%positive ap_p) = false.
Proof. vm_compute; reflexivity. Qed.
Example compound_source_missing_body_receipts_refused :
  ap_selected (describe_affine_dependent_source [] 100%positive 101%positive dp_profile
    (dependent_bound_loop ap_i dp_root ap_outer)) = false.
Proof. vm_compute; reflexivity. Qed.
Example generated_pointer_head_has_pointer_type :
  match propose_dependent_private_names [] 19 with
  | (_,ty)::rest => if type_eq ty signed_pointer_type then true else false
  | _ => false end = true.
Proof. vm_compute; reflexivity. Qed.
Example numeric_pointer_slot_refused :
  check_affine_dependent_source [] [(100%positive,type_int32s);(101%positive,type_int32s)]
    dp_profile (fun _ => None) dp_source = pure None.
Proof. vm_compute; reflexivity. Qed.
Example pointer_typed_bound_slot_refused :
  check_affine_dependent_source [] [(100%positive,signed_pointer_type);(101%positive,signed_pointer_type)]
    dp_profile (fun _ => None) dp_source = pure None.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions actual_compound_header_site_selected.
Print Assumptions compound_source_without_public_bound_snapshot_selected.
Print Assumptions private_bound_is_checked_model_cache.
Print Assumptions original_compound_source_progress_selected.
Print Assumptions same_pointer_and_bound_cache_refused.
Print Assumptions original_root_cannot_be_private_pointer.
Print Assumptions public_body_pointer_cannot_be_private_bound.
Print Assumptions compound_source_missing_body_receipts_refused.
Print Assumptions generated_pointer_head_has_pointer_type.
Print Assumptions numeric_pointer_slot_refused.
Print Assumptions pointer_typed_bound_slot_refused.
