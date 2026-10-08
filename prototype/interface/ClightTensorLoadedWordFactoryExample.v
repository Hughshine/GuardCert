From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight Ctypes Cop.
From Guard Require Import ClightPrivatePool.
From GuardInterface Require Import ClightTensorLoadedWordFactory ClightNestedConstantSite
  ClightTensorLoadedWordDriver ClightTensorRegionPackage ClightTensorRegionExample
  ClightTensorSourceExample ClightSignedExpressionProgress ClightDirectWordObservation.
Import ListNotations.
Local Open Scope Z_scope.

(** Independently loaded bounds and an actual dynamic-stride Horner RMW body:
      for i < *header: for j < header[1]: for k < 5:
        a[((i*ld)+j)*5+k] += increment
    Static recognition does not assert a safe or accepting runtime state. *)
Definition lwf_shape := NestedConstantShape 6%positive 7%positive 8%positive
  1%positive 3%positive 98%positive 4%positive 5 tensor_source_demo_code
  99%positive Int.one Int.zero Int.zero.
Definition lwf_description := LoadedWordDescription lwf_shape 9%positive
  tensor_source_demo_index tensor_source_demo_rhs
  100%positive 101%positive 102%positive 103%positive 104%positive 105%positive 106%positive 32 32.
Definition lwf_live := [6%positive;7%positive;8%positive;2%positive;5%positive;9%positive;99%positive].
Definition lwf_pool := map(fun id=>(id,type_int32s))[1%positive;3%positive;4%positive;
  100%positive;101%positive;102%positive;103%positive;104%positive;105%positive;106%positive;
  110%positive;111%positive;112%positive;113%positive;114%positive;115%positive].
Definition lwf_static_recognized live d := match check_loaded_word_static live d with Some _=>true|None=>false end.
Definition lwf_site_recognized source live pool d description :=
  match check_loaded_word_site source live pool d description with Some _=>true|None=>false end.

Example lwf_dynamic_horner_static : lwf_static_recognized lwf_live lwf_description=true.
Proof. vm_compute; reflexivity. Qed.
Example lwf_dynamic_horner_canonical :
  tensor_word_driver_canonical lwf_shape=tensor_region_demo_source.
Proof. vm_compute; reflexivity. Qed.
Example lwf_dynamic_horner_site :
  lwf_site_recognized(ncs_original lwf_shape)lwf_live lwf_pool lwf_description tensor_region_demo_description=true.
Proof. vm_compute; reflexivity. Qed.
Example lwf_dynamic_horner_progress : signed_expression_region_progress_supported(ncs_original lwf_shape)=true.
Proof. vm_compute; reflexivity. Qed.
Example lwf_typed_pool : private_pool_check lwf_live lwf_pool=true.
Proof. vm_compute; reflexivity. Qed.
Example lwf_wrong_original_refused :
  lwf_site_recognized Sskip lwf_live lwf_pool lwf_description tensor_region_demo_description=false.
Proof. vm_compute; reflexivity. Qed.
Example lwf_missing_private_refused :
  lwf_site_recognized(ncs_original lwf_shape)lwf_live(tl lwf_pool)lwf_description tensor_region_demo_description=false.
Proof. vm_compute; reflexivity. Qed.
Example lwf_wrong_private_type_refused :
  lwf_site_recognized(ncs_original lwf_shape)lwf_live
    ((1%positive,(Tfloat F64 noattr))::tl lwf_pool)lwf_description tensor_region_demo_description=false.
Proof. vm_compute; reflexivity. Qed.
Example lwf_visible_cache_refused :
  lwf_site_recognized(ncs_original lwf_shape)(1%positive::lwf_live)lwf_pool
    lwf_description tensor_region_demo_description=false.
Proof. vm_compute; reflexivity. Qed.
Example lwf_control_alias_refused :
  lwf_static_recognized lwf_live(LoadedWordDescription lwf_shape 9%positive tensor_source_demo_index tensor_source_demo_rhs
    100%positive 100%positive 102%positive 103%positive 104%positive 105%positive 106%positive 32 32)=false.
Proof. vm_compute; reflexivity. Qed.
Example lwf_changed_index_refused :
  lwf_static_recognized lwf_live(LoadedWordDescription lwf_shape 9%positive
    (Etempvar 2%positive (Tfloat F64 noattr))tensor_source_demo_rhs
    100%positive 101%positive 102%positive 103%positive 104%positive 105%positive 106%positive 32 32)=false.
Proof. vm_compute; reflexivity. Qed.
Definition lwf_nonword_index := Etempvar 2%positive(Tfloat F64 noattr).
Definition lwf_nonword_shape := NestedConstantShape 6%positive 7%positive 8%positive
  1%positive 3%positive 98%positive 4%positive 5
  (direct_word_store 9%positive lwf_nonword_index tensor_source_demo_rhs)
  99%positive Int.one Int.zero Int.zero.
Example lwf_nonword_grammar_refused :
  lwf_static_recognized lwf_live(LoadedWordDescription lwf_nonword_shape 9%positive
    lwf_nonword_index tensor_source_demo_rhs
    100%positive 101%positive 102%positive 103%positive 104%positive 105%positive 106%positive 32 32)=false.
Proof. vm_compute; reflexivity. Qed.
Example lwf_invalid_tensor_model_refused :
  lwf_site_recognized(ncs_original lwf_shape)lwf_live lwf_pool lwf_description tensor_region_demo_unlicensed_dimension=false.
Proof. vm_compute; reflexivity. Qed.
Example lwf_candidate_resources_separate :
  map fst(lwd_candidate_pool lwf_pool lwf_description)=
    [110%positive;111%positive;112%positive;113%positive;114%positive;115%positive].
Proof. vm_compute; reflexivity. Qed.

Print Assumptions lwf_dynamic_horner_static.
Print Assumptions lwf_dynamic_horner_canonical.
Print Assumptions lwf_dynamic_horner_site.
Print Assumptions lwf_dynamic_horner_progress.
Print Assumptions lwf_typed_pool.
Print Assumptions lwf_wrong_original_refused.
Print Assumptions lwf_missing_private_refused.
Print Assumptions lwf_wrong_private_type_refused.
Print Assumptions lwf_visible_cache_refused.
Print Assumptions lwf_control_alias_refused.
Print Assumptions lwf_changed_index_refused.
Print Assumptions lwf_nonword_grammar_refused.
Print Assumptions lwf_invalid_tensor_model_refused.
Print Assumptions lwf_candidate_resources_separate.
