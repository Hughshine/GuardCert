From Stdlib Require Import List ZArith.
From compcert.lib Require Import Integers.
From compcert.cfrontend Require Import Ctypes.
From GuardAffineNest Require Import AffineNestGuardPackage AffineNestPackageExamples AffineNestStaticExamples
  AffineNestStaticPackage AffineNestRangeProposal.
Import ListNotations.
Local Open Scope Z_scope.
Definition affine_range_example_policy cap := AffineRangePolicy (-4) cap (-8) 9 (-32) 33.
Definition affine_range_example_accept policy :=
  let pool:=map(fun identifier=>(identifier,type_int32s)) affine_static_example_allocated in
  match affine_source_range_proposal policy affine_memory_example_live pool affine_memory_example_source with
  | Some(parameters,proposal)=>match check_affine_static_package affine_memory_example_source parameters affine_memory_example_live
      affine_static_example_allocated proposal with Some _=>true|None=>false end
  | None=>false end.
Example inferred_three_level_ranges_accepted : affine_range_example_accept(affine_range_example_policy 256)=true.
Proof. vm_compute; reflexivity. Qed.
Example overflowing_inferred_child_range_refused : affine_range_example_accept(affine_range_example_policy Int.max_signed)=false.
Proof. vm_compute; reflexivity. Qed.
Example invalid_configured_root_range_refused : affine_range_example_accept(affine_range_example_policy (-5))=false.
Proof. vm_compute; reflexivity. Qed.
Example actual_three_level_inferred_caps :
  let pool:=map(fun identifier=>(identifier,type_int32s)) affine_static_example_allocated in
  match affine_source_range_proposal(affine_range_example_policy 256) affine_memory_example_live pool affine_memory_example_source with
  | Some(_,proposal)=>affine_proposed_cap proposal=256 /\ affine_proposed_remaining proposal=[(0,263);(0,270)] /\
      affine_proposed_window_lower proposal=(-64) /\ affine_proposed_window_upper proposal=5398
  | None=>False end.
Proof. vm_compute; repeat split; reflexivity. Qed.
Print Assumptions inferred_three_level_ranges_accepted.
Print Assumptions overflowing_inferred_child_range_refused.
Print Assumptions invalid_configured_root_range_refused.
Print Assumptions actual_three_level_inferred_caps.
