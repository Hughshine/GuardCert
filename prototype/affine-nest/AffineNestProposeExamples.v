From Stdlib Require Import List ZArith.
From compcert.cfrontend Require Import Ctypes.
From GuardAffineNest Require Import AffineNestPackageExamples AffineNestStaticExamples AffineNestStaticPackage AffineNestPropose.
Import ListNotations.
Definition affine_default_example_accept :=
  let pool:=map(fun identifier=>(identifier,type_int32s)) affine_static_example_allocated in
  match affine_default_source_proposal affine_memory_example_live pool affine_memory_example_source with
  | Some(parameters,proposal)=>match check_affine_static_package affine_memory_example_source parameters affine_memory_example_live
      affine_static_example_allocated proposal with Some _=>true|None=>false end
  | None=>false end.
Example actual_source_default_proposal_accepted : affine_default_example_accept=true.
Proof. vm_compute; reflexivity. Qed.
Print Assumptions actual_source_default_proposal_accepted.
