From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import Values.
From Guard Require Import ClightCondition ClightPureExpr ClightNoWrap ClightMatrixGuard ClightRedundantSet ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryParametricWidth.
From GuardInterface Require Import AffineBoxEnvelope ClightAffinePointerEnvelope ClightAffineInnerPointerEnvelope
  ClightAffineInnerPointerSourceGuard ClightAffinePointerGuard ClightAffinePointerGuardExamples.
Import ListNotations.
Local Open Scope Z_scope.

Definition ap_complete_guard :=
  match ap_description ap_source 64 64 [] [] [ap_p;ap_q],ap_width with
  | Some package,Some width =>
    match compile_affine_inner_pointer_package_envelopes package with
    | Some alias => Some (affine_inner_pointer_source_guard_tree package width alias)
    | None => None end
  | _,_ => None end.

Example affine_inner_pointer_package_alias_compiles : ap_selected ap_complete_guard = true.
Proof. vm_compute; reflexivity. Qed.

(** The observation registers contain only N and source parameters. There is
    no temporary containing the constant column cap, even for a general box. *)
Example affine_inner_pointer_fixed_column_compiles : exists tree,
  compile_fixed_column_separation 64 [ap_n;ap_n] [65;65]
    ([64;1;0],32) ([64;1;0],4096) = Some tree.
Proof. vm_compute; eexists; reflexivity. Qed.

Example affine_inner_pointer_fixed_column_accepts :
  affine_box_separation 2 ([64;1;0],32) ([64;1;0],4096) [63;64;63] = true.
Proof. reflexivity. Qed.
Example affine_inner_pointer_fixed_column_refuses :
  affine_box_separation 2 ([64;1;0],32) ([64;1;0],4096) [64;64;64] = false.
Proof. reflexivity. Qed.
Example affine_inner_pointer_unsafe_endpoint_encoding_rejected :
  compile_fixed_column_separation 64 [ap_n;ap_n] [65;65]
    ([Int.max_signed;1;0],32) ([Int.max_signed;1;0],4096) = None.
Proof. vm_compute; reflexivity. Qed.

(** This is actual Clight decision execution with no pointer bindings and no
    j/k/body words. Its empty path refuses before the pointer comparison. *)
Example affine_inner_pointer_complete_guard_empty_refuses ge locals memory :
  exists tree, ap_complete_guard = Some tree /\
    decision_run (Entry ge locals
      (PTree.set ap_n (Vint Int.zero) (PTree.set ap_i (Vint Int.zero) (PTree.empty val))) memory) tree false.
Proof.
  unfold ap_complete_guard,ap_description; vm_compute; eexists; split; [reflexivity|].
  eapply run_test with (b := true).
  - apply register_expression_test; exists Int.zero; reflexivity.
  - eapply run_test with (b := false).
    + apply register_positive_test; exists Int.zero; reflexivity.
    + constructor.
Qed.

Print Assumptions affine_inner_pointer_package_alias_compiles.
Print Assumptions affine_inner_pointer_fixed_column_compiles.
Print Assumptions affine_inner_pointer_fixed_column_accepts.
Print Assumptions affine_inner_pointer_fixed_column_refuses.
Print Assumptions affine_inner_pointer_unsafe_endpoint_encoding_rejected.
Print Assumptions affine_inner_pointer_complete_guard_empty_refuses.
