From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From GuardAffineNest Require Import AffineNestPackageDecode.
From GuardInterface Require Import ClightNestedConstantPhysicalGuard ClightNestedConstantSiteExample
  ClightNestedConstantNumericExample ClightNestedConstantEntryGate ClightLoadedAffineNumericExamples.
Import ListNotations.

Example original_site_full_source_loop_lowering_available : exists source_loop,
  affine_package_source_loop ncn_parameters(ncn_proposal 107%positive)=Some source_loop.
Proof. vm_compute; eexists; reflexivity. Qed.

Theorem actual_empty_original_complete_physical_receipt fe ge locals : exists checked,
  ncs_physical_receipt ncs_zero_site fe ge locals ncs_empty_temps lnf_zero_memory ncs_empty_temps lnf_zero_memory checked.
Proof. apply ncs_original_physical_guard_execution; apply checked_original_empty_source_executes. Qed.

Theorem actual_full_physical_nonzero_row_refusal fe ge locals memory :
  exec_stmt fe ge locals ncs_nonzero_temps memory(ncs_physical_guard ncs_zero_site)
    E0(PTree.set 107%positive(Vint Int.zero)ncs_nonzero_temps) memory Out_normal.
Proof.
  unfold ncs_physical_guard; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)
    (le1:=PTree.set 107%positive(Vint Int.zero)ncs_nonzero_temps)(m1:=memory).
  - apply nonzero_row_actual_refusal_skips_all_headers.
  - eapply exec_Sifthenelse with(v1:=Vint Int.zero)(b:=false).
    + constructor; apply PTree.gss.
    + reflexivity.
    + constructor.
Qed.

Print Assumptions original_site_full_source_loop_lowering_available.
Print Assumptions actual_empty_original_complete_physical_receipt.
Print Assumptions actual_full_physical_nonzero_row_refusal.
