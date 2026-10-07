From Stdlib Require Import List Bool.
From compcert.lib Require Import Integers.
From compcert.common Require Import Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From GuardInterface Require Import ClightZeroIndexHeader ClightNestedFrontendRegion ClightNestedConstantSiteExample
  ClightSignedExpressionProgress ClightLoadedAffineNumericExamples.

Example array_zero_root_progress_is_host_supported :
  signed_expression_region_progress_supported(ncs_frontend_source true(ncs_example_shape Int.one))=true.
Proof. vm_compute; reflexivity. Qed.

Theorem actual_array_zero_root_empty_source_executes fe ge locals :
  exec_stmt fe ge locals ncs_empty_temps lnf_zero_memory(ncs_frontend_source true(ncs_example_shape Int.zero))
    E0 ncs_empty_temps lnf_zero_memory Out_normal.
Proof. apply(proj2(@ncs_frontend_execution_equivalent true _ _ _ _ _ _ _ _ _ _));
  apply checked_original_empty_source_executes. Qed.

Print Assumptions array_zero_root_progress_is_host_supported.
Print Assumptions actual_array_zero_root_empty_source_executes.
