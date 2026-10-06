From Stdlib Require Import List ZArith.
From compcert.lib Require Import Integers.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightPrivatePool.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryArrayBackend GuardMemoryPointerBackend
  GuardMemoryMultiPointerBackend GuardMemoryScalarLoops GuardMemoryAffineInnerPointerSyntax
  GuardMemoryAffineInnerPointerRegionSource.
From GuardInterface Require Import ClightAffinePointerGuardExamples ClightSourceObservation
  ClightObservedPointerSyntax ClightSequenceProgressSelector ClightAffineInnerPointerCandidates.
Import ListNotations.
Local Open Scope Z_scope.

Definition ap_loads := [(8%positive,ap_p);(9%positive,ap_q)].
Definition ap_observed := Ssequence (source_load_prefix ap_loads) ap_source.
Definition ap_live := [ap_i;ap_n;ap_j;ap_k;ap_p;ap_q;ap_a;8%positive;9%positive].
Definition ap_profile := AffineInnerPointerSourceProfile 64 64 [] [] [] [ap_p;ap_q] 8192.
Definition ap_validator_bounds := [MemoryNested.A.Interval 1 65;
  MemoryNested.A.Interval Int.min_signed Int.max_signed].
Definition ap_encoder_bounds := [MemoryFramedNested.N.A.Interval 1 65;
  MemoryFramedNested.N.A.Interval Int.min_signed Int.max_signed].
Fixpoint ap_interchanged_instructions arity instructions :=
  match instructions with
  | [] => L.SNil
  | instruction::rest => L.SCons (L.Instr instruction (memory_variables_from 0 (2+arity)%nat))
      (ap_interchanged_instructions arity rest)
  end.
Definition ap_interchanged request :=
  L.Loop (L.Constant 0) (L.Var 0)
    (L.Loop (L.Var 0) (L.Var 1)
      (L.Seq (ap_interchanged_instructions (length (affine_request_context request))
        (affine_request_instructions request)))).
Definition ap_candidate_lowered := match describe_affine_inner_pointer_at ap_source ap_profile with
  | Some package => compile_memory_multi_pointer_buffer_loop (affine_inner_pointer_pointers package)
      (memory_affine_inner_pointer_region_context package) ap_encoder_bounds ap_live
      [(100%positive,101%positive);(102%positive,103%positive)]
      (ap_interchanged (affine_inner_pointer_request_of package))
  | None => None end.

Example affine_inner_pointer_observed_source_progress : sequence_progress_supported ap_observed = true.
Proof. vm_compute; reflexivity. Qed.
Example affine_inner_pointer_normalized_observation_selected :
  ap_selected (describe_observed_pointer_source ap_observed) = true.
Proof. vm_compute; reflexivity. Qed.
Example affine_inner_pointer_source_observation_coverage : source_observations_check [ap_p;ap_q] ap_loads = true.
Proof. vm_compute; reflexivity. Qed.
Example affine_inner_pointer_missing_receipt_refused : source_observations_check [ap_p;ap_q] [(8%positive,ap_p)] = false.
Proof. vm_compute; reflexivity. Qed.
Example affine_inner_pointer_generated_profile_checked :
  ap_selected (match propose_affine_inner_pointer_profile 64 64 16 8192 ap_source with
    | Some profile => describe_affine_inner_pointer_at ap_source profile | None => None end) = true.
Proof. vm_compute; reflexivity. Qed.
Example affine_inner_pointer_triangular_candidate_lowered : ap_selected ap_candidate_lowered = true.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions affine_inner_pointer_observed_source_progress.
Print Assumptions affine_inner_pointer_normalized_observation_selected.
Print Assumptions affine_inner_pointer_source_observation_coverage.
Print Assumptions affine_inner_pointer_missing_receipt_refused.
Print Assumptions affine_inner_pointer_generated_profile_checked.
Print Assumptions affine_inner_pointer_triangular_candidate_lowered.
