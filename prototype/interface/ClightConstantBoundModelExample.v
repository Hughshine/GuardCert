From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightTempFrame ClightCountedProtocol ClightCountedLoop ClightFrontendLoopProtocol.
From GuardInterface Require Import ClightConstantBoundModel ClightStrictLoopProgress
  ClightSignedExpressionProgress ClightExpressionHeaderCapture ClightDualLoadedUnitSyntax
  ClightLoadedAffineScanAcceptExample.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition cbm_temps := PTree.set 50%positive(Vint(Int.repr 5))
  (PTree.set 2%positive(Vint(Int.repr 4)) lns_separate_temps).
Definition cbm_exit := PTree.set 2%positive(Vint(Int.repr 5)) cbm_temps.
Definition cbm_final_state : {memory | Mem.store Mint32 lns_first 1%positive 4(Vint(Int.repr 2))=Some memory}.
Proof. apply Mem.valid_access_store; eapply Mem.store_valid_access_1; [exact(proj2_sig lns_first_state)|].
  eapply Mem.store_valid_access_3; exact(proj2_sig lns_first_state). Defined.
Definition cbm_final := proj1_sig cbm_final_state.
Definition cbm_source := strict_frontend_loop 2%positive
  (signed_expression_test 2%positive(Econst_int(Int.repr 5)type_int32s))(dual_unit_store 3%positive).

(** A reached fifth component store changes the word used by a loaded child
    header. The literal-to-model bridge must not assume that word is stable. *)
Theorem constant_fifth_store_source fe ge locals :
  exec_stmt fe ge locals cbm_temps lns_first cbm_source E0 cbm_exit cbm_final Out_normal /\
  Mem.load Mint32 lns_first 1%positive 4=Some(Vint Int.one) /\
  Mem.load Mint32 cbm_final 1%positive 4=Some(Vint(Int.repr 2)).
Proof.
  split.
  - unfold cbm_source; eapply strict_iteration_encode with(body_temps:=cbm_temps)(body_memory:=cbm_final).
    + change true with(Int.lt(Int.repr 4)(Int.repr 5)); apply signed_expression_test_eval;
        [reflexivity|reflexivity|constructor].
    + exists(Int.repr 4); split; [reflexivity|change(4<2147483647); lia].
    + eapply dual_unit_store_encode; [reflexivity|exact(proj2_sig cbm_final_state)].
    + change (exec_stmt fe ge locals cbm_exit cbm_final cbm_source E0 cbm_exit cbm_final Out_normal).
      apply signed_expression_zero_trip_execution; change false with(Int.lt(Int.repr 5)(Int.repr 5)).
      apply signed_expression_test_eval; [reflexivity|reflexivity|constructor].
  - split.
    + rewrite (@Mem.load_store_same Mint32 lns_initial 1%positive 4(Vint Int.one) lns_first
        (proj2_sig lns_first_state)); reflexivity.
    + rewrite (@Mem.load_store_same Mint32 lns_first 1%positive 4(Vint(Int.repr 2)) cbm_final
        (proj2_sig cbm_final_state)); reflexivity.
Qed.

Theorem constant_fifth_store_model fe ge locals :
  exec_stmt fe ge locals cbm_temps lns_first
    (frontend_counted_loop 2%positive 50%positive(dual_unit_store 3%positive)) E0 cbm_exit cbm_final Out_normal /\
  cbm_exit!50%positive=Some(Vint(Int.repr 5)).
Proof.
  eapply constant_loop_preinitialized_model with(written:=[]);
    [discriminate|constructor|cbn; tauto|reflexivity|exact(proj1(constant_fifth_store_source fe ge locals))].
Qed.

Theorem constant_model_assignment_is_noop fe ge locals memory :
  exec_stmt fe ge locals cbm_temps memory(Sset 50%positive(Econst_int(Int.repr 5)type_int32s))
    E0 cbm_temps memory Out_normal.
Proof. apply initialized_bound_assignment with(upper:=Int.repr 5); [reflexivity|constructor]. Qed.

Print Assumptions constant_fifth_store_source.
Print Assumptions constant_fifth_store_model.
Print Assumptions constant_model_assignment_is_noop.
