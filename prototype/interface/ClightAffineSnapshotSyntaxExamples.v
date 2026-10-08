From Stdlib Require Import List ZArith.
From compcert.lib Require Import Integers.
From compcert.cfrontend Require Import Clight Ctypes Cop.
From Guard Require Import ClightCountedLoop ClightFrontendLoopProtocol.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightWordReadSnapshots
  ClightAffineHeaderSnapshots ClightAffineSnapshotSyntax ClightAffineInnerPointerCandidates.
Import ListNotations.
Local Open Scope Z_scope.

(** Independently written source expressions and bodies exercise selection.
    These are closed checker computations, not compiler/native evidence. *)
Definition ap_i := 1%positive.
Definition ap_n := 2%positive.
Definition ap_j := 3%positive.
Definition ap_k := 4%positive.
Definition ap_p := 5%positive.
Definition ap_q := 6%positive.
Definition ap_a := 7%positive.
Definition ap_constant value := Econst_int(Int.repr value)type_int32s.
Definition ap_sum first second := Ebinop Oadd first second type_int32s.
Definition ap_index bias := ap_sum(ap_sum(ap_constant bias)
  (Ebinop Omul(ap_constant 64)(Etempvar ap_i type_int32s)type_int32s))(Etempvar ap_j type_int32s).
Definition ap_pointer_cell pointer bias :=
  Ederef(Ebinop Oadd(Etempvar pointer(Tpointer type_int32s noattr))(ap_index bias)
    (Tpointer type_int32s noattr))type_int32s.
Definition ap_body := Sassign(ap_pointer_cell ap_p 32)
  (ap_sum(ap_pointer_cell ap_q 4096)(Etempvar ap_a type_int32s)).
Definition ap_selected {A:Type}(result:option A) := match result with Some _=>true|None=>false end.
Definition snapshot_example_N := 9%positive.
Definition snapshot_example_M := 10%positive.
Definition snapshot_example_cache := 11%positive.
Definition snapshot_example_header := Ebinop Oadd(Etempvar ap_i type_int32s)
  (signed_load snapshot_example_M)type_int32s.
Definition snapshot_example_source := loaded_bound_loop ap_i snapshot_example_N
  (affine_setup_child ap_j ap_k snapshot_example_header ap_body).
Definition snapshot_example_profile := propose_affine_inner_pointer_profile 64 64 16 8192.
Definition snapshot_example_describe source :=
  describe_affine_snapshot_source snapshot_example_profile ap_n snapshot_example_cache source.

Example original_loaded_affine_setup_selected : ap_selected(snapshot_example_describe snapshot_example_source)=true.
Proof. vm_compute; reflexivity. Qed.

Example original_double_M_read_selected : ap_selected(snapshot_example_describe
  (loaded_bound_loop ap_i snapshot_example_N(affine_setup_child ap_j ap_k
    (Ebinop Oadd(Etempvar ap_i type_int32s)
      (Ebinop Oadd(signed_load snapshot_example_M)(signed_load snapshot_example_M)type_int32s)type_int32s)ap_body)))=true.
Proof. vm_compute; reflexivity. Qed.

Example unencoded_second_loaded_pointer_refused : ap_selected(snapshot_example_describe
  (loaded_bound_loop ap_i snapshot_example_N(affine_setup_child ap_j ap_k
    (Ebinop Oadd(signed_load snapshot_example_M)(signed_load 12%positive)type_int32s)ap_body)))=false.
Proof. vm_compute; reflexivity. Qed.

Example nonaffine_product_of_loaded_parameter_refused : ap_selected(snapshot_example_describe
  (loaded_bound_loop ap_i snapshot_example_N(affine_setup_child ap_j ap_k
    (Ebinop Omul(Etempvar ap_i type_int32s)(signed_load snapshot_example_M)type_int32s)ap_body)))=false.
Proof. vm_compute; reflexivity. Qed.

Example division_header_refused : snapshot_word_expression_check
  (Ebinop Odiv(Etempvar ap_i type_int32s)(signed_load snapshot_example_M)type_int32s)=false.
Proof. vm_compute; reflexivity. Qed.

Example unsigned_header_refused : snapshot_word_expression_check
  (Ebinop Oadd(Etempvar ap_i type_int32s)(signed_load snapshot_example_M)(Tint I32 Unsigned noattr))=false.
Proof. vm_compute; reflexivity. Qed.

Example row_cache_collision_refused : ap_selected(describe_affine_snapshot_source
  snapshot_example_profile ap_i snapshot_example_cache snapshot_example_source)=false.
Proof. vm_compute; reflexivity. Qed.

Example column_cache_collision_refused : ap_selected(describe_affine_snapshot_source
  snapshot_example_profile ap_n ap_j snapshot_example_source)=false.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions original_loaded_affine_setup_selected.
Print Assumptions original_double_M_read_selected.
Print Assumptions unencoded_second_loaded_pointer_refused.
Print Assumptions nonaffine_product_of_loaded_parameter_refused.
Print Assumptions division_header_refused.
Print Assumptions unsigned_header_refused.
Print Assumptions row_cache_collision_refused.
Print Assumptions column_cache_collision_refused.
