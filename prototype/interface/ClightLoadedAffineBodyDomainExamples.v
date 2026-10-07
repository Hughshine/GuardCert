From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryAffineSourceValuation GuardMemoryFootprintCapabilities.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestGuardPackage AffineNestPackageExamples
  AffineNestScanPoints AffineNestValuation.
From GuardInterface Require Import ClightLoadedAffineNumericSite ClightLoadedAffineNumericExamples
  ClightLoadedAffineNumericGuard
  ClightLoadedBodyPrefix ClightLoadedBodyPrefixExamples ClightLoadedAffineBodyPrefix ClightLoadedAffineBodyDomain
  ClightCapableWordSeparation ClightWordAddressSeparation ClightReadonlyLoadedTreeSynthesis.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Example recursive_body_model_is_constructed :
  lnf_present(affine_loaded_body_model affine_memory_example_parameters lnf_proposal)=true.
Proof. vm_compute; reflexivity. Qed.

Example first_recursive_body_has_one_point :
  length(affine_scan_points (affine_proposed_child lnf_proposal)
    (memory_source_set_valuation(affine_word_valuation lnf_active_temps) 1%positive 0) 0)=1%nat.
Proof. vm_compute; reflexivity. Qed.

Example next_recursive_body_has_three_points :
  length(affine_scan_points (affine_proposed_child lnf_proposal)
    (memory_source_set_valuation(affine_word_valuation lnf_active_temps) 1%positive 1) 0)=3%nat.
Proof. vm_compute; reflexivity. Qed.

(** Exercise the stronger ready/prefix producer on the actual loaded source.
    This is a symbolic instantiation, not a new nonempty execution fixture or
    a claim that the numeric flag alone supplies physical permissions. *)
Theorem recursive_ready_prefix_from_original fe ge locals temps memory after final :
  affine_loaded_numeric_snapshot 11%positive lnf_proposal(Entry ge locals temps memory) ->
  affine_loaded_numeric_premise affine_memory_example_parameters lnf_proposal(Entry ge locals temps memory) ->
  temps!1%positive=Some(Vint Int.zero) ->
  0<=Int.signed(temp_word 4%positive temps) ->
  exec_stmt fe ge locals temps memory lnf_source E0 after final Out_normal ->
  loaded_body_prefix fe 1%positive 4%positive 11%positive (affine_proposed_body lnf_proposal)
    (affine_loaded_body_stable affine_memory_example_parameters lnf_proposal 11%positive)
    (affine_loaded_body_ready affine_memory_example_parameters lnf_proposal) 0(Entry ge locals temps memory).
Proof.
  eapply (@affine_loaded_ready_initial_prefix _ _ _ _ (loaded_numeric_package lnf_site) 11%positive
    fe ge locals temps memory after final).
Qed.

(** A concrete real store from the earlier alias source licenses equality.
    The new read-only domain asks only for a valid aligned address. It must
    reject self-alias even though the logical cell could be identical. *)
Theorem capable_self_alias_refuses
  (fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop) ge locals :
  capable_word_address_domain (Etempvar 3%positive(Tpointer type_int32s noattr)) 3%positive
    (Entry ge locals(lbp_temps 1%positive Ptrofs.zero) lbp_two_memory) /\
  decision_run (Entry ge locals(lbp_temps 1%positive Ptrofs.zero) lbp_two_memory)
    (word_address_separation (Etempvar 3%positive(Tpointer type_int32s noattr)) 3%positive) false.
Proof.
  pose proof (@lbp_initial_receipt fe ge locals lbp_two_memory lbp_one_memory 1%positive Ptrofs.zero
    lbp_concrete_read lbp_concrete_store) as PREFIX.
  assert (DOMAIN : word_address_domain (Etempvar 3%positive(Tpointer type_int32s noattr)) 3%positive
    (Entry ge locals(lbp_temps 1%positive Ptrofs.zero) lbp_two_memory)).
  { eapply lbp_probe_domain; [exact PREFIX|change (0<2); lia]. }
  destruct DOMAIN as [block [offset [other [base [loaded DOMAIN]]]]].
  destruct DOMAIN as [EVAL [POINTER [ACCESS READ]]].
  assert (VALID : Mem.valid_pointer lbp_two_memory block(Ptrofs.unsigned offset)=true)
    by(apply valid_word_address; exact ACCESS).
  assert (ALIGN : (4|Ptrofs.unsigned offset)) by exact(proj2 ACCESS).
  split.
  - exists block,offset,other,base,loaded; split; [exact EVAL|split; [exact POINTER|split; [exact VALID|split; assumption]]].
  - eapply lbp_probe_refuses; [exact PREFIX|change (0<2); lia].
Qed.

Print Assumptions recursive_body_model_is_constructed.
Print Assumptions first_recursive_body_has_one_point.
Print Assumptions next_recursive_body_has_three_points.
Print Assumptions recursive_ready_prefix_from_original.
Print Assumptions capable_self_alias_refuses.
