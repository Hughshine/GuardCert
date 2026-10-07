From Stdlib Require Import List PArith ZArith.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight Ctypes.
From GuardInterface Require Import ClightNestedConstantSite ClightNestedConstantPhysicalGuard
  ClightNestedConstantStability ClightNestedStabilityCertificate ClightNestedConstantWordExample
  ClightNestedConstantSiteExample ClightNestedConstantMultiExample.
Import ListNotations.

Example indexed_constant_body_produces_word :
  ncs_stability_word ncw_indexed_shape = Some Int.one.
Proof. vm_compute; reflexivity. Qed.

Definition mixed_word_shape := NestedConstantShape 1%positive 2%positive 3%positive
  4%positive 5%positive 51%positive 50%positive 5
  (Ssequence ncw_leaf (Sassign (Ederef (Etempvar 10%positive (Tpointer type_int32s noattr)) type_int32s)
    (Econst_int Int.zero type_int32s))) 11%positive Int.one Int.one Int.one.
Example first_word_proposal_cannot_hide_other_store_values :
  ncs_stability_word mixed_word_shape = None.
Proof. vm_compute; reflexivity. Qed.

Example indexed_constant_stability_site_checked :
  match check_ncs_stability_site (ncs_original ncw_indexed_shape) ncw_indexed_parameters
    ncw_indexed_live ncs_multi_example_allocated ncw_indexed_proposal ncw_indexed_shape
  with Some _ => true | None => false end = true.
Proof. vm_compute; reflexivity. Qed.

Theorem unsupported_word_classifier_preserves_scan source parameters live proposal shape
  (site : nested_constant_site source parameters live proposal shape) :
  ncs_stability_word shape = None -> ncs_stability_guard site = ncs_physical_guard site.
Proof.
  intro NONE; unfold ncs_stability_guard, ncs_physical_guard, ncs_stability_code;
    rewrite NONE; reflexivity.
Qed.

Print Assumptions indexed_constant_body_produces_word.
Print Assumptions first_word_proposal_cannot_hide_other_store_values.
Print Assumptions indexed_constant_stability_site_checked.
Print Assumptions unsupported_word_classifier_preserves_scan.
