From Stdlib Require Import List ZArith.
From compcert.lib Require Import Integers.
From GuardInterface Require Import ClightNestedNumericWordFacts ClightNestedStabilityExample
  ClightNestedConstantWordExample ClightNestedStabilityCertificate ClightNestedConstantSite
  ClightNestedConstantMultiExample.
From GuardAffineNest Require Import AffineNestGuardPackage.
Import ListNotations.
Local Open Scope Z_scope.

(** Match the actual frontend's [1,17) cached-count profile. The older
    literal-15 fixture checks construction only and uses [0,16), which
    correctly refuses a count of 16 at runtime. *)
Definition numeric_fifteen_proposal := AffineGuardProposal 1%positive 4%positive fifteen_body fifteen_child
  [(0,16);(0,16);(0,5);(1,17);(1,17)] 0 1280 [10%positive] [fifteen_operation]
  [(1,17);(1,17)] 0 16 [(0,16);(0,5)]
  [101%positive;104%positive;102%positive;105%positive;103%positive;106%positive] 107%positive.

Example numeric_fifteen_site_checked :
  match check_ncs_stability_site(ncs_original fifteen_shape)ncw_indexed_parameters
    ncw_indexed_live ncs_multi_example_allocated numeric_fifteen_proposal fifteen_shape
  with Some _=>true | None=>false end=true.
Proof. vm_compute; reflexivity. Qed.

Example numeric_word_one_checked :
  ncs_numeric_word_check ncw_indexed_parameters ncw_indexed_proposal ncw_indexed_shape Int.one=true.
Proof. vm_compute; reflexivity. Qed.
Example numeric_word_fifteen_checked :
  ncs_numeric_word_check ncw_indexed_parameters numeric_fifteen_proposal fifteen_shape(Int.repr 15)=true.
Proof. vm_compute; reflexivity. Qed.
Example numeric_word_outside_profile_refused :
  ncs_numeric_word_check ncw_indexed_parameters numeric_fifteen_proposal fifteen_shape(Int.repr 16)=false.
Proof. vm_compute; reflexivity. Qed.
Example numeric_word_wrapped_count_refused :
  ncs_numeric_word_check ncw_indexed_parameters numeric_fifteen_proposal fifteen_shape(Int.repr Int.max_signed)=false.
Proof. vm_compute; reflexivity. Qed.
Example numeric_word_empty_count_refused :
  ncs_numeric_word_check ncw_indexed_parameters numeric_fifteen_proposal fifteen_shape Int.mone=false.
Proof. vm_compute; reflexivity. Qed.
Example numeric_word_unknown_parameter_refused :
  ncs_numeric_word_check(ncw_indexed_parameters++[200%positive]) numeric_fifteen_proposal fifteen_shape(Int.repr 15)=false.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions numeric_word_one_checked.
Print Assumptions numeric_fifteen_site_checked.
Print Assumptions numeric_word_fifteen_checked.
Print Assumptions numeric_word_outside_profile_refused.
Print Assumptions numeric_word_wrapped_count_refused.
Print Assumptions numeric_word_empty_count_refused.
Print Assumptions numeric_word_unknown_parameter_refused.
