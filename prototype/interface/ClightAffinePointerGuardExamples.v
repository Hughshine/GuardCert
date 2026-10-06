From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import Values.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightCondition ClightCountedLoop ClightFrontendLoopProtocol ClightNoWrap
  ClightMatrixGuard ClightRectangularGuard ClightRedundantSet.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineSourceExpressions
  GuardMemoryParametricWidth GuardMemoryLoops.
From GuardInterface Require Import ClightAffinePointerGuard.
Import ListNotations.
Local Open Scope Z_scope.

(** An explicit normalized Clight fixture for this C body, not a statement
    regenerated from a successful certificate:
    for (; i<n; ++i) { k=i+1; for (j=0;j<k;++j)
      p[32+64*i+j] = q[4096+64*i+j] + a; }
    These checks validate the new source describer and early runtime refusal.
    They are not frontend, program installation, or native execution evidence. *)
Definition ap_i := 1%positive.
Definition ap_n := 2%positive.
Definition ap_j := 3%positive.
Definition ap_k := 4%positive.
Definition ap_p := 5%positive.
Definition ap_q := 6%positive.
Definition ap_a := 7%positive.
Definition ap_constant value := Econst_int (Int.repr value) type_int32s.
Definition ap_sum first second := Ebinop Oadd first second type_int32s.
Definition ap_index bias := ap_sum (ap_sum (ap_constant bias)
  (Ebinop Omul (ap_constant 64) (Etempvar ap_i type_int32s) type_int32s)) (Etempvar ap_j type_int32s).
Definition ap_pointer_cell pointer bias :=
  Ederef (Ebinop Oadd (Etempvar pointer (Tpointer type_int32s noattr))
    (ap_index bias) (Tpointer type_int32s noattr)) type_int32s.
Definition ap_body := Sassign (ap_pointer_cell ap_p 32)
  (ap_sum (ap_pointer_cell ap_q 4096) (Etempvar ap_a type_int32s)).
Definition ap_header := ap_sum (Etempvar ap_i type_int32s) (ap_constant 1).
Definition ap_outer := Ssequence (Sset ap_k ap_header)
  (Ssequence (Sset ap_j (ap_constant 0)) (frontend_counted_loop ap_j ap_k ap_body)).
Definition ap_source := frontend_counted_loop ap_i ap_n ap_outer.
Definition ap_description source row_cap column_cap body_parameters body_caps pointers :=
  describe_memory_affine_pointer source row_cap column_cap [] body_parameters body_caps pointers 8192.
Definition ap_selected {A : Type} (result : option A) := match result with Some _ => true | None => false end.

Example affine_inner_pointer_triangle_source_selected :
  ap_selected (ap_description ap_source 64 64 [] [] [ap_p;ap_q]) = true.
Proof. vm_compute; reflexivity. Qed.
Example affine_inner_pointer_small_window_rejected :
  ap_selected (describe_memory_affine_pointer ap_source 64 64 [] [] [] [ap_p;ap_q] 4096) = false.
Proof. vm_compute; reflexivity. Qed.
Example affine_inner_pointer_missing_pointer_rejected :
  ap_selected (ap_description ap_source 64 64 [] [] [ap_p]) = false.
Proof. vm_compute; reflexivity. Qed.
Example affine_inner_pointer_unused_geometry_rejected :
  ap_selected (ap_description ap_source 64 64 [8%positive] [16] [ap_p;ap_q]) = false.
Proof. vm_compute; reflexivity. Qed.
Example affine_inner_pointer_modified_increment_rejected :
  ap_selected (ap_description (Sloop
    (Ssequence (Ssequence Sskip (Sifthenelse (counter_condition ap_i ap_n) Sskip Sbreak)) ap_outer)
    (Ssequence Sskip (Sset ap_i (ap_sum (Etempvar ap_i type_int32s) (ap_constant 2)))))
    64 64 [] [] [ap_p;ap_q]) = false.
Proof. vm_compute; reflexivity. Qed.

Definition ap_shape := MemoryAffineInnerPointerShape ap_i ap_n ap_j ap_k ap_body ap_outer.
Definition ap_affine := MemorySourceAdd (MemorySourceTemp ap_i) (MemorySourceConstant 1).
Definition ap_width := compile_memory_source_width 64 ap_i [ap_n]
  (affine_inner_pointer_header_bounds 64 []) ap_affine.
Definition ap_tree := match ap_width with
  | Some width => affine_inner_pointer_preparation_tree ap_shape ap_affine 64 [] [8%positive] [16] width
  | None => Decision false end.
Example affine_inner_pointer_width_compiles : match ap_width with Some _ => true | None => false end = true.
Proof. vm_compute; reflexivity. Qed.

(** n=0 refuses before reading the deliberately undefined body parameter or
    the public j/k. The ge/env/memory are arbitrary because this path only
    evaluates the two typed control words. *)
Example affine_inner_pointer_empty_refuses ge locals memory :
  decision_run (Entry ge locals
    (PTree.set ap_n (Vint Int.zero) (PTree.set ap_i (Vint Int.zero) (PTree.empty val))) memory) ap_tree false.
Proof.
  unfold ap_tree,ap_width; vm_compute.
  eapply run_test with (b := true).
  - apply register_expression_test; exists Int.zero; reflexivity.
  - eapply run_test with (b := false).
    + apply register_positive_test; exists Int.zero; reflexivity.
    + constructor.
Qed.

Print Assumptions affine_inner_pointer_triangle_source_selected.
Print Assumptions affine_inner_pointer_small_window_rejected.
Print Assumptions affine_inner_pointer_missing_pointer_rejected.
Print Assumptions affine_inner_pointer_unused_geometry_rejected.
Print Assumptions affine_inner_pointer_modified_increment_rejected.
Print Assumptions affine_inner_pointer_width_compiles.
Print Assumptions affine_inner_pointer_empty_refuses.
