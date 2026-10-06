From Stdlib Require Import List ZArith.
From compcert.cfrontend Require Import Ctypes Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax.
From GuardInterface Require Import ClightSourceObservation ClightPrivateLoadedSource
  ClightAffinePrivateLoadedCandidates ClightAffineDynamicLoadedSyntax
  ClightAffineDynamicLoadedExamples ClightAffinePointerGuardExamples
  ClightAffineInnerPointerCandidateExamples ClightAffineInnerPointerCandidates.
Import ListNotations CoreAlarmed.

(** The actual loaded source has body-pointer receipts but no bound snapshot.
    The inserted read is justified by the language theorem, not by these
    syntax fixtures; no candidate or native execution is claimed here. *)
Definition ps_source := Ssequence (source_load_prefix ap_loads) dl_loop.
Definition ps_profile : affine_inner_pointer_profiler := fun _ => Some ap_profile.
Definition ps_prepared cache := match describe_loaded_snapshot_site ps_source with
  | Some site => snapshot_site_prepared site cache
  | None => Sskip end.
Example private_snapshot_site_selected : ap_selected (describe_loaded_snapshot_site ps_source) = true.
Proof. vm_compute; reflexivity. Qed.
Example original_source_without_snapshot_refused_by_old_selector :
  ap_selected (describe_affine_dynamic_loaded_source ps_profile ps_source) = false.
Proof. vm_compute; reflexivity. Qed.
Example private_snapshot_intermediate_source_selected :
  ap_selected (describe_affine_dynamic_loaded_source ps_profile (ps_prepared 100%positive)) = true.
Proof. vm_compute; reflexivity. Qed.
Example inserted_private_bound_is_the_model_cache :
  match describe_affine_dynamic_loaded_source ps_profile (ps_prepared 100%positive) with
  | Some region => Pos.eqb (affine_inner_pointer_bound
      (affine_inner_pointer_shape (dynamic_loaded_body_cached_package (dynamic_loaded_region_body region)))) 100%positive
  | None => false end = true.
Proof. vm_compute; reflexivity. Qed.
Example iterator_cannot_be_private_snapshot :
  check_affine_private_loaded_source [] [(ap_i,type_int32s)] ps_profile (fun _ => None) ps_source = pure None.
Proof. vm_compute; reflexivity. Qed.
Example pointer_cannot_be_private_snapshot :
  check_affine_private_loaded_source [] [(dl_bound_pointer,type_int32s)] ps_profile (fun _ => None) ps_source = pure None.
Proof. vm_compute; reflexivity. Qed.
Example live_identifier_cannot_be_private_snapshot :
  check_affine_private_loaded_source [100%positive] [(100%positive,type_int32s)] ps_profile (fun _ => None) ps_source = pure None.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions private_snapshot_site_selected.
Print Assumptions original_source_without_snapshot_refused_by_old_selector.
Print Assumptions private_snapshot_intermediate_source_selected.
Print Assumptions inserted_private_bound_is_the_model_cache.
Print Assumptions iterator_cannot_be_private_snapshot.
Print Assumptions pointer_cannot_be_private_snapshot.
Print Assumptions live_identifier_cannot_be_private_snapshot.
