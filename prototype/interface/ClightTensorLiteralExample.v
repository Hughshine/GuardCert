From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib Integers Maps.
From compcert.common Require Import AST Values.
From compcert.cfrontend Require Import Clight Ctypes.
From Guard Require Import ClightCountedLoop ClightRectangularLoops ClightStructuredProgress
  ClightFrontendLoopProtocol ClightLoopSyntax ClightCondition.
From GuardInterface Require Import ClightLiteralBoundPreparation ClightTensorRegionExample
  ClightTensorSourceExample ClightTensorRegionPackage ClightSignedExpressionProgress ClightSharedGuard
  ClightTensorLiteralPreservation ClightMaterializedCheck ClightStrictLoopProgress ClightStagedCheck.
Import ListNotations.

Definition tensor_literal_demo_source := frontend_counted_loop 6%positive 1%positive
  (Ssequence(rectangle_reset 7%positive)(frontend_counted_loop 7%positive 3%positive
    (Ssequence(rectangle_reset 8%positive)
      (strict_frontend_loop 8%positive(signed_expression_test 8%positive(Econst_int(Int.repr 5)type_int32s))tensor_source_demo_code)))).
Definition tensor_literal_demo_canonical:=literal_tests_prepare 4%positive(Int.repr 5)tensor_literal_demo_source.
Definition tensor_literal_demo_recognized source upper := tensor_region_demo_recognized
  (literal_tests_prepare 4%positive upper source)tensor_region_demo_description.
Example tensor_literal_demo_canonical_exact : tensor_literal_demo_canonical=tensor_region_demo_source.
Proof. vm_compute; reflexivity. Qed.
Example tensor_literal_demo_recognized_actual : tensor_literal_demo_recognized tensor_literal_demo_source(Int.repr 5)=true.
Proof. vm_compute; reflexivity. Qed.
Example tensor_literal_demo_wrong_literal_refused : tensor_literal_demo_recognized tensor_literal_demo_source(Int.repr 6)=false.
Proof. vm_compute; reflexivity. Qed.
Example tensor_literal_demo_expression_progress : signed_expression_region_progress_supported tensor_literal_demo_source=true.
Proof. vm_compute; reflexivity. Qed.
Example tensor_literal_demo_old_progress_refuses : structured_progress_supported tensor_literal_demo_source=false.
Proof. vm_compute; reflexivity. Qed.
Example tensor_literal_demo_original_helper_undefined : (PTree.empty val)!4%positive=None.
Proof. reflexivity. Qed.
Example tensor_literal_demo_prepared_helper_defined :
  (literal_bound_temps 4%positive(Int.repr 5)(PTree.empty val))!4%positive=Some(Vint(Int.repr 5)).
Proof. reflexivity. Qed.
Example tensor_literal_demo_addresses_unchanged :
  literal_tests_prepare 4%positive(Int.repr 5)tensor_source_demo_code=tensor_source_demo_code.
Proof. reflexivity. Qed.
Example tensor_literal_demo_materialized_described : match describe_materialized_check
  (tensor_literal_check_body 4%positive(Int.repr 5)(Decision false)99%positive)(shared_guard_choice 99%positive)
  with Some _=>true|None=>false end=true.
Proof. vm_compute; reflexivity. Qed.
Print Assumptions tensor_literal_demo_canonical_exact.
Print Assumptions tensor_literal_demo_recognized_actual.
Print Assumptions tensor_literal_demo_wrong_literal_refused.
Print Assumptions tensor_literal_demo_expression_progress.
Print Assumptions tensor_literal_demo_old_progress_refuses.
Print Assumptions tensor_literal_demo_original_helper_undefined.
Print Assumptions tensor_literal_demo_prepared_helper_defined.
Print Assumptions tensor_literal_demo_addresses_unchanged.
Print Assumptions tensor_literal_demo_materialized_described.
