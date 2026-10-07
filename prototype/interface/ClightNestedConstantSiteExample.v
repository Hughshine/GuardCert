From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightRectangularGuard.
From GuardAffineNest Require Import AffineNestPackageGuard.
From GuardInterface Require Import ClightNestedConstantSite ClightNestedConstantSiteNumeric ClightNestedConstantEntryGate
  ClightNestedConstantNumericExample ClightNestedConstantNumericGuard ClightNestedExpressionCapture
  ClightExpressionHeaderCapture ClightSignedExpressionProgress ClightLoadedOffsetHeader ClightLoadedAffineNumericExamples.
Import ListNotations.
Local Open Scope Z_scope.

Definition ncs_example_shape delta := NestedConstantShape 1%positive 2%positive 3%positive
  4%positive 5%positive 51%positive 50%positive 5 ncn_leaf 11%positive Int.one delta Int.one.
Definition ncs_example_live := [1%positive;2%positive;3%positive;7%positive;10%positive;11%positive].
Definition ncs_example_present {A}(result:option A) := match result with Some _=>true|None=>false end.
Definition ncs_example_accept delta := ncs_example_present(check_nested_constant_site
  (ncs_original(ncs_example_shape delta)) ncn_parameters ncs_example_live(ncn_proposal 107%positive)(ncs_example_shape delta)).
Example actual_loaded_indexed_original_site_checked : ncs_example_accept Int.one=true.
Proof. vm_compute; reflexivity. Qed.
Example cached_replacement_cannot_be_original_site : ncs_example_present(check_nested_constant_site
  ncn_source ncn_parameters ncs_example_live(ncn_proposal 107%positive)(ncs_example_shape Int.one))=false.
Proof. vm_compute; reflexivity. Qed.
Example probe_result_component_cursor_collision_refused : ncs_example_present(check_nested_constant_site
  (ncs_original(ncs_example_shape Int.one)) ncn_parameters ncs_example_live(ncn_proposal 103%positive)(ncs_example_shape Int.one))=false.
Proof. vm_compute; reflexivity. Qed.
Definition ncs_example_bad_cache := NestedConstantShape 1%positive 2%positive 3%positive
  11%positive 5%positive 51%positive 50%positive 5 ncn_leaf 11%positive Int.one Int.one Int.one.
Example header_pointer_as_capture_scratch_refused : ncs_example_present(check_nested_constant_site
  (ncs_original ncs_example_bad_cache) ncn_parameters ncs_example_live(ncn_proposal 107%positive) ncs_example_bad_cache)=false.
Proof. vm_compute; reflexivity. Qed.
Definition ncs_example_empty_literal := NestedConstantShape 1%positive 2%positive 3%positive
  4%positive 5%positive 51%positive 50%positive 0 ncn_leaf 11%positive Int.one Int.one Int.one.
Example empty_literal_site_refused : ncs_example_present(check_nested_constant_site
  (ncs_original ncs_example_empty_literal) ncn_parameters ncs_example_live(ncn_proposal 107%positive)
  ncs_example_empty_literal)=false.
Proof. vm_compute; reflexivity. Qed.
Example zero_offset_original_site_checked : ncs_example_accept Int.zero=true.
Proof. vm_compute; reflexivity. Qed.
Definition ncs_zero_site : nested_constant_site(ncs_original(ncs_example_shape Int.zero)) ncn_parameters ncs_example_live
  (ncn_proposal 107%positive)(ncs_example_shape Int.zero).
Proof.
  pose proof zero_offset_original_site_checked as CHECK; unfold ncs_example_accept in CHECK.
  destruct(check_nested_constant_site(ncs_original(ncs_example_shape Int.zero)) ncn_parameters ncs_example_live
    (ncn_proposal 107%positive)(ncs_example_shape Int.zero)) as [site|] eqn:SELECT;
    [exact site|discriminate].
Defined.

(** Only the row and a one-word header pointer are initialized. The child
    address is never loaded, and all leaf parameters/pointers are absent. *)
Definition ncs_empty_temps := PTree.set 1%positive(Vint Int.zero)
  (PTree.set 11%positive(Vptr 1%positive Ptrofs.zero)(PTree.empty val)).
Lemma checked_original_empty_source_executes fe ge locals :
  exec_stmt fe ge locals ncs_empty_temps lnf_zero_memory(ncs_original(ncs_example_shape Int.zero))
    E0 ncs_empty_temps lnf_zero_memory Out_normal.
Proof.
  unfold ncs_original; apply signed_expression_zero_trip_execution.
  change false with(Int.lt Int.zero(Int.add Int.zero Int.zero)).
  apply signed_expression_test_eval; [reflexivity|reflexivity|].
  eapply signed_load_offset_eval; [reflexivity|exact concrete_zero_bound_read].
Qed.
Theorem checked_original_empty_numeric_receipt fe ge locals : exists checked,
  ncs_numeric_receipt ncs_zero_site fe ge locals ncs_empty_temps lnf_zero_memory ncs_empty_temps lnf_zero_memory checked.
Proof.
  apply ncs_numeric_site_execution; [reflexivity|apply checked_original_empty_source_executes].
Qed.

Theorem checked_original_empty_entry_receipt fe ge locals : exists checked,
  ncs_entry_numeric_receipt ncs_zero_site fe ge locals ncs_empty_temps lnf_zero_memory ncs_empty_temps lnf_zero_memory checked.
Proof. apply ncs_entry_numeric_execution; apply checked_original_empty_source_executes. Qed.

Definition ncs_nonzero_temps := PTree.set 1%positive(Vint Int.one)(PTree.empty val).
Theorem nonzero_row_actual_refusal_skips_all_headers fe ge locals memory :
  exec_stmt fe ge locals ncs_nonzero_temps memory(ncs_entry_numeric_code ncs_zero_site)
    E0(PTree.set 107%positive(Vint Int.zero)ncs_nonzero_temps) memory Out_normal.
Proof.
  destruct(@ncs_zero_row_evaluation ge locals ncs_nonzero_temps memory 1%positive Int.one eq_refl)
    as [value [EVAL BOOL]].
  unfold ncs_entry_numeric_code; eapply exec_Sifthenelse with(b:=false);
    [exact EVAL|exact BOOL|constructor; constructor].
Qed.

Print Assumptions actual_loaded_indexed_original_site_checked.
Print Assumptions cached_replacement_cannot_be_original_site.
Print Assumptions probe_result_component_cursor_collision_refused.
Print Assumptions header_pointer_as_capture_scratch_refused.
Print Assumptions empty_literal_site_refused.
Print Assumptions zero_offset_original_site_checked.
Print Assumptions checked_original_empty_source_executes.
Print Assumptions checked_original_empty_numeric_receipt.
Print Assumptions checked_original_empty_entry_receipt.
Print Assumptions nonzero_row_actual_refusal_skips_all_headers.
