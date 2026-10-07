From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightNoWrap
  ClightRectangularGuard ClightRedundantSet ClightProjectedExecution ClightRegionProgress.
From GuardMemory Require Import GuardMemoryBooleanScan.
From GuardInterface Require Import ClightTensorLoadedWordDriver ClightTensorWordOuterExample
  ClightTensorWordOuterHeaders ClightTensorWordColumnExample ClightWordComponentScanExample
  ClightTensorHeaderPointExample ClightTensorHeaderCapture ClightNestedConstantSite
  ClightNestedExpressionCapture ClightLoadedOffsetHeader ClightSignedIndexedOffsetHeader
  ClightExpressionHeaderCapture ClightLiteralBoundPreparation ClightCheckPlanFrame
  ClightQuietDeterminacy ClightDirectWordObservation ClightStrictLoopProgress ClightSignedExpressionProgress.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Remove both caches and the literal helper from the incoming source state.
    The driver must emit their initialization before the complete word scan. *)
Definition twd_temps base := PTree.remove 50%positive(PTree.remove 5%positive(PTree.remove 4%positive(two_temps base))).
Definition twd_live := [12%positive;2%positive;3%positive;1%positive;6%positive;7%positive;10%positive;11%positive].
Definition twd_stable := [4%positive;5%positive;50%positive;1%positive;6%positive;7%positive;10%positive;11%positive].
Definition twd_captured base := tensor_header_captured two_shape(twd_temps base)(Int.repr 2)(Some(Int.repr 2)).
Definition twd_code root_cap child_cap := tensor_word_driver_code two_shape 10%positive
  112%positive 114%positive 102%positive 105%positive 103%positive 104%positive 108%positive
  wcs_index two_rename root_cap child_cap.

Lemma twd_incoming_private_undefined base :
  (twd_temps base)!4%positive=None /\ (twd_temps base)!5%positive=None /\ (twd_temps base)!50%positive=None.
Proof. repeat split; reflexivity. Qed.
Lemma twd_initialization_restores base :
  literal_bound_temps 50%positive(Int.repr 5)(twd_captured base)=two_temps base.
Proof. vm_compute; reflexivity. Qed.

Lemma twd_actual_capture fe ge locals base :
  exec_stmt fe ge locals(twd_temps base)thp_memory(tensor_header_capture two_shape)
    E0(twd_captured base)thp_memory Out_normal.
Proof.
  unfold tensor_header_capture,nested_expression_capture,twd_captured,tensor_header_captured,nested_expression_captured.
  eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=PTree.set 4%positive(Vint(Int.repr 2))(twd_temps base))(m1:=thp_memory).
  - change(exec_stmt fe ge locals(twd_temps base)thp_memory(Sset 4%positive(signed_load_offset 11%positive(Int.repr 2)))
      E0(PTree.set 4%positive(Vint(Int.repr 2))(twd_temps base))thp_memory Out_normal).
    constructor; change(eval_expr ge locals(twd_temps base)thp_memory(signed_load_offset 11%positive(Int.repr 2))
      (Vint(Int.add Int.zero(Int.repr 2)))); eapply signed_load_offset_eval; [reflexivity|exact(proj1 thp_header_reads)].
  - assert(TEST:expression_test(signed_expression_test 12%positive(Etempvar 4%positive type_int32s))
      (Entry ge locals(PTree.set 4%positive(Vint(Int.repr 2))(twd_temps base))thp_memory)true).
    { change true with(Int.lt Int.zero(Int.repr 2)); apply signed_expression_test_eval; [reflexivity|reflexivity|constructor; reflexivity]. }
    destruct TEST as [value [EVAL BOOL]]; eapply exec_Sifthenelse; [exact EVAL|exact BOOL|].
    change(exec_stmt fe ge locals(PTree.set 4%positive(Vint(Int.repr 2))(twd_temps base))thp_memory
      (Sset 5%positive(signed_indexed_offset 11%positive Int.one(Int.repr 2)))E0
      (PTree.set 5%positive(Vint(Int.repr 2))(PTree.set 4%positive(Vint(Int.repr 2))(twd_temps base)))thp_memory Out_normal).
    constructor; change(eval_expr ge locals(PTree.set 4%positive(Vint(Int.repr 2))(twd_temps base))thp_memory
      (signed_indexed_offset 11%positive Int.one(Int.repr 2))(Vint(Int.add Int.zero(Int.repr 2)))).
    eapply signed_indexed_offset_eval; [reflexivity|exact(proj2 thp_header_reads)].
Qed.

Lemma twd_original_completion fe ge locals base :
  (base=Ptrofs.repr 16 \/ base=Ptrofs.repr(-20)) -> exists after final,
  exec_stmt fe ge locals(twd_temps base)thp_memory(ncs_original two_shape)E0 after final Out_normal.
Proof.
  intro BASE; destruct(@two_original_complete fe ge locals base BASE)as [after [final SOURCE]].
  destruct(@structured_execution_temp_transport fe ge locals(two_temps base)thp_memory two_source E0 after final Out_normal
    SOURCE(statement_temps two_source)(twd_temps base)(statement_temps two_source)
    (@check_plan_frameable_writes two_source eq_refl)ltac:(unfold statement_scope; apply incl_refl)
    ltac:(intros id MEMBER; vm_compute in MEMBER; repeat destruct MEMBER as [MEMBER|MEMBER]; try contradiction; subst id; reflexivity))
    as [exit [RUN PUBLIC]].
  exists exit,final; exact RUN.
Qed.

Lemma twd_driver_receipt fe ge locals base source_after final :
  exec_stmt fe ge locals(twd_temps base)thp_memory(ncs_original two_shape)E0 source_after final Out_normal ->
  exists accepted checked fallback_exit,
    exec_stmt fe ge locals(twd_temps base)thp_memory(twd_code 8 8)E0 checked thp_memory Out_normal /\
    temp_agree(tensor_word_driver_ports two_shape twd_live)(twd_temps base)checked /\
    checked!108%positive=Some(memory_boolean_word accepted) /\
    exec_stmt fe ge locals checked thp_memory(ncs_original two_shape)E0 fallback_exit final Out_normal /\
    temp_agree twd_live source_after fallback_exit /\
    (accepted=true -> exists exit,
      exec_stmt fe ge locals checked thp_memory(tensor_word_driver_canonical two_shape)E0 exit final Out_normal /\
      temp_agree twd_live source_after exit).
Proof.
  intro SOURCE; eapply tensor_word_driver_execution_with_fallback with
    (pointer:=10%positive)(row_cursor:=112%positive)(row_limit:=114%positive)
    (column_cursor:=102%positive)(column_limit:=105%positive)(component_cursor:=103%positive)
    (component_limit:=104%positive)(index:=wcs_index)(rhs:=wcs_rhs)(rename:=two_rename)(stable:=twd_stable).
  all: try solve[reflexivity|discriminate|exact wcs_word|exact SOURCE|lia].
  all: try solve[change(-2147483648<=5<=2147483647); lia].
  all: try solve[change(-2147483648<=8<=2147483647); lia].
  all: try solve[intros id MEMBER; vm_compute in MEMBER;
    repeat destruct MEMBER as [MEMBER|MEMBER]; try contradiction; subst id; reflexivity].
  all: try solve[vm_compute; intuition congruence].
Qed.

Theorem twd_actual_driver_scan fe ge locals base :
  (base=Ptrofs.repr 16 \/ base=Ptrofs.repr(-20)) -> exists checked,
  exec_stmt fe ge locals(twd_temps base)thp_memory(twd_code 8 8)E0 checked thp_memory Out_normal /\
  checked!108%positive=Some(memory_boolean_word(two_flag ge locals base)).
Proof.
  intro BASE; destruct(@two_actual_source_scan fe ge locals base BASE)
    as [source_after [final [checked [SOURCE [SCAN [PUBLIC [FLAG SOUND]]]]]]].
  exists checked; split; [|exact FLAG].
  unfold twd_code,tensor_word_driver_code; eapply decision_fragment_run with(b:=true).
  - change true with(register_flag 12%positive Int.zero(Entry ge locals(twd_temps base)thp_memory)).
    apply register_tree_run; exists Int.zero; reflexivity.
  - eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [apply twd_actual_capture|].
    eapply decision_fragment_run with(b:=true).
    + change true with(tensor_word_driver_profile_flag two_shape 8 8(Entry ge locals(twd_captured base)thp_memory)).
      apply tensor_word_driver_profile_run; [exists(Int.repr 2); reflexivity|intro; exists(Int.repr 2); reflexivity].
    + unfold tensor_word_driver_scan; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [apply literal_bound_set_execution|].
      change(exec_stmt fe ge locals(literal_bound_temps 50%positive(Int.repr 5)(twd_captured base))thp_memory
        (tensor_word_header_scan two_shape 10%positive 112%positive 114%positive 102%positive 105%positive
          103%positive 104%positive 108%positive wcs_index two_rename)E0 checked thp_memory Out_normal).
      rewrite twd_initialization_restores,<-two_scan_uses_templates; exact SCAN.
Qed.

Theorem twd_actual_initialized_acceptance fe ge locals : exists checked,
  exec_stmt fe ge locals(twd_temps(Ptrofs.repr 16))thp_memory(twd_code 8 8)E0 checked thp_memory Out_normal /\
  checked!108%positive=Some(memory_boolean_word true).
Proof.
  destruct(@twd_actual_driver_scan fe ge locals(Ptrofs.repr 16)ltac:(left; reflexivity))as [checked [RUN FLAG]].
  exists checked; split; [exact RUN|rewrite two_twenty_points_accept in FLAG; exact FLAG].
Qed.
Theorem twd_actual_initialized_alias_refusal fe ge locals : exists checked,
  exec_stmt fe ge locals(twd_temps(Ptrofs.repr(-20)))thp_memory(twd_code 8 8)E0 checked thp_memory Out_normal /\
  checked!108%positive=Some(memory_boolean_word false).
Proof.
  destruct(@twd_actual_driver_scan fe ge locals(Ptrofs.repr(-20))ltac:(right; reflexivity))as [checked [RUN FLAG]].
  exists checked; split; [exact RUN|rewrite two_first_row_refuses in FLAG; exact FLAG].
Qed.

Theorem twd_accepted_canonical_and_original_exit fe ge locals : exists source_after final checked exit fallback_exit,
  exec_stmt fe ge locals(twd_temps(Ptrofs.repr 16))thp_memory(ncs_original two_shape)E0 source_after final Out_normal /\
  exec_stmt fe ge locals(twd_temps(Ptrofs.repr 16))thp_memory(twd_code 8 8)E0 checked thp_memory Out_normal /\
  checked!108%positive=Some(memory_boolean_word true) /\
  exec_stmt fe ge locals checked thp_memory(tensor_word_driver_canonical two_shape)E0 exit final Out_normal /\
  temp_agree twd_live source_after exit /\
  exec_stmt fe ge locals checked thp_memory(ncs_original two_shape)E0 fallback_exit final Out_normal /\
  temp_agree twd_live source_after fallback_exit.
Proof.
  destruct(@twd_original_completion fe ge locals(Ptrofs.repr 16)ltac:(left; reflexivity))as [source_after [final SOURCE]].
  destruct(twd_driver_receipt SOURCE)as [accepted [checked [fallback_exit [RUN [FRAME [FLAG [FALLBACK [EXIT ACCEPT]]]]]]]].
  destruct(@twd_actual_initialized_acceptance fe ge locals)as [actual [ACTUAL TRUE]].
  destruct(@quiet_execution_determinate fe ge locals(twd_temps(Ptrofs.repr 16))thp_memory(twd_code 8 8)
    E0 checked thp_memory Out_normal RUN ltac:(vm_compute; reflexivity)E0 actual thp_memory Out_normal ACTUAL)
    as [_ [SAME _]]; subst actual.
  assert(ACCEPTED:accepted=true)by(destruct accepted; [reflexivity|rewrite TRUE in FLAG; discriminate]).
  subst accepted; destruct(ACCEPT eq_refl)as [exit [CANONICAL PUBLIC]].
  exists source_after,final,checked,exit,fallback_exit; repeat split; assumption.
Qed.

(** Oversized captured counts refuse before helper initialization or data
    scanning. The incoming data pointer can therefore be undefined. *)
Definition twd_no_data := PTree.remove 10%positive(twd_temps(Ptrofs.repr 16)).
Definition twd_no_data_captured := tensor_header_captured two_shape twd_no_data(Int.repr 2)(Some(Int.repr 2)).
Theorem twd_profile_refusal_without_data fe ge locals :
  exec_stmt fe ge locals twd_no_data thp_memory(twd_code 1 8)E0
    (PTree.set 108%positive(Vint Int.zero)twd_no_data_captured)thp_memory Out_normal /\
  twd_no_data!10%positive=None /\
  (PTree.set 108%positive(Vint Int.zero)twd_no_data_captured)!50%positive=None.
Proof.
  split; [|split; reflexivity].
  unfold twd_code,tensor_word_driver_code; eapply decision_fragment_run with(b:=true).
  - change true with(register_flag 12%positive Int.zero(Entry ge locals twd_no_data thp_memory));
      apply register_tree_run; exists Int.zero; reflexivity.
  - eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=twd_no_data_captured)(m1:=thp_memory).
    + unfold tensor_header_capture,nested_expression_capture,twd_no_data_captured,tensor_header_captured,nested_expression_captured.
      eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=PTree.set 4%positive(Vint(Int.repr 2))twd_no_data)(m1:=thp_memory).
      * constructor; change(eval_expr ge locals twd_no_data thp_memory(signed_load_offset 11%positive(Int.repr 2))
          (Vint(Int.add Int.zero(Int.repr 2)))); eapply signed_load_offset_eval; [reflexivity|exact(proj1 thp_header_reads)].
      * assert(TEST:expression_test(signed_expression_test 12%positive(Etempvar 4%positive type_int32s))
          (Entry ge locals(PTree.set 4%positive(Vint(Int.repr 2))twd_no_data)thp_memory)true).
        { change true with(Int.lt Int.zero(Int.repr 2)); apply signed_expression_test_eval; [reflexivity|reflexivity|constructor; reflexivity]. }
        destruct TEST as [value [EVAL BOOL]]; eapply exec_Sifthenelse; [exact EVAL|exact BOOL|].
        constructor; change(eval_expr ge locals(PTree.set 4%positive(Vint(Int.repr 2))twd_no_data)thp_memory
          (signed_indexed_offset 11%positive Int.one(Int.repr 2))(Vint(Int.add Int.zero(Int.repr 2))));
          eapply signed_indexed_offset_eval; [reflexivity|exact(proj2 thp_header_reads)].
    + apply tensor_word_driver_profile_root_refusal; [exists(Int.repr 2); reflexivity|reflexivity].
Qed.

Definition twd_empty_shape := NestedConstantShape 12%positive 2%positive 3%positive
  4%positive 5%positive 51%positive 50%positive 5 wcs_body 11%positive(Int.repr Int.max_signed)Int.zero(Int.repr 2).
Definition twd_empty_temps := PTree.set 12%positive(Vint Int.zero)
  (PTree.set 11%positive(Vptr 1%positive Ptrofs.zero)(PTree.empty val)).
Definition twd_empty_code := tensor_word_driver_code twd_empty_shape 10%positive
  112%positive 114%positive 102%positive 105%positive 103%positive 104%positive 108%positive
  wcs_index two_rename 8 8.
Definition twd_empty_checked := PTree.set 108%positive(Vint Int.zero)(PTree.set 4%positive(Vint Int.zero)twd_empty_temps).

(** The source and complete capture/profile/scan driver both skip an invalid
    indexed child load. No child cache, helper, data pointer or layout exists. *)
Theorem twd_empty_original_and_driver fe ge locals :
  exec_stmt fe ge locals twd_empty_temps thp_memory(ncs_original twd_empty_shape)
    E0 twd_empty_temps thp_memory Out_normal /\
  exec_stmt fe ge locals twd_empty_temps thp_memory twd_empty_code E0 twd_empty_checked thp_memory Out_normal /\
  twd_empty_checked!5%positive=None /\ twd_empty_checked!50%positive=None /\ twd_empty_checked!10%positive=None.
Proof.
  assert(ROOT:eval_expr ge locals twd_empty_temps thp_memory(signed_load_offset 11%positive Int.zero)(Vint Int.zero)).
  { change Int.zero with(Int.add Int.zero Int.zero); eapply signed_load_offset_eval; [reflexivity|exact(proj1 thp_header_reads)]. }
  split.
  - unfold ncs_original,nested_expression_source; apply signed_expression_zero_trip_execution.
    change false with(Int.lt Int.zero Int.zero); apply signed_expression_test_eval; [reflexivity|reflexivity|exact ROOT].
  - split; [|repeat split; reflexivity].
    unfold twd_empty_code,tensor_word_driver_code; eapply decision_fragment_run with(b:=true).
    + change true with(register_flag 12%positive Int.zero(Entry ge locals twd_empty_temps thp_memory));
        apply register_tree_run; exists Int.zero; reflexivity.
    + eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=PTree.set 4%positive(Vint Int.zero)twd_empty_temps)(m1:=thp_memory).
      * unfold tensor_header_capture,nested_expression_capture; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)
          (le1:=PTree.set 4%positive(Vint Int.zero)twd_empty_temps)(m1:=thp_memory).
        -- constructor; exact ROOT.
        -- assert(TEST:expression_test(signed_expression_test 12%positive(Etempvar 4%positive type_int32s))
            (Entry ge locals(PTree.set 4%positive(Vint Int.zero)twd_empty_temps)thp_memory)false).
           { change false with(Int.lt Int.zero Int.zero); apply signed_expression_test_eval;
               [reflexivity|reflexivity|constructor; reflexivity]. }
           destruct TEST as [value [EVAL BOOL]]; eapply exec_Sifthenelse; [exact EVAL|exact BOOL|constructor].
      * apply tensor_word_driver_profile_root_refusal; [exists Int.zero; reflexivity|reflexivity].
Qed.

Theorem twd_nonzero_start_skips_capture fe ge locals :
  exec_stmt fe ge locals(PTree.set 12%positive(Vint Int.one)(PTree.empty val))thp_memory(twd_code 8 8)
    E0(PTree.set 108%positive(Vint Int.zero)(PTree.set 12%positive(Vint Int.one)(PTree.empty val)))thp_memory Out_normal.
Proof. apply tensor_word_driver_start_refusal; [exists Int.one; reflexivity|reflexivity]. Qed.

Print Assumptions twd_incoming_private_undefined.
Print Assumptions twd_initialization_restores.
Print Assumptions twd_actual_capture.
Print Assumptions twd_original_completion.
Print Assumptions twd_driver_receipt.
Print Assumptions twd_actual_driver_scan.
Print Assumptions twd_actual_initialized_acceptance.
Print Assumptions twd_actual_initialized_alias_refusal.
Print Assumptions twd_accepted_canonical_and_original_exit.
Print Assumptions twd_profile_refusal_without_data.
Print Assumptions twd_empty_original_and_driver.
Print Assumptions twd_nonzero_start_skips_capture.
