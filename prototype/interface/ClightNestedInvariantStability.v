From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightNoWrap ClightTempFootprint
  ClightProjectedExecution.
From GuardMemory Require Import GuardMemoryBooleanScan.
From GuardAffineNest Require Import AffineNestGuardPackage.
From GuardInterface Require Import CompCertWordObservation ClightNestedConstantSite
  ClightNestedConstantHeaders ClightNestedConstantSitePrepare ClightNestedConstantSiteNumeric
  ClightNestedConstantOuterConsumer ClightNestedConstantWordModel ClightNestedConstantWordCheck
  ClightNestedConstantScanNames
  ClightCheckPlanFrame ClightNestedConstantPhysicalGuard ClightNestedConstantEntryGate
  ClightInitializedBooleanAnd ClightNestedConstantStability ClightNestedInvariantWordCheck
  ClightNestedInvariantWordModel ClightNestedConstantSiteFacts.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions.
Import ListNotations.
Set Implicit Arguments.

Definition ncs_invariant_or_scan shape proposal expression :=
  Sifthenelse (ncs_invariant_pair_expression shape expression)
    (Sset (affine_proposed_result proposal) (Econst_int Int.one type_int32s))
    (ncs_stability_code shape proposal).
Definition ncs_invariant_stability_code parameters shape proposal :=
  match ncs_invariant_expression parameters shape with
  | Some expression => ncs_invariant_or_scan shape proposal expression
  | None => ncs_stability_code shape proposal end.

Theorem ncs_invariant_or_scan_execution fe ge locals temps memory shape proposal expression word root child trace after final outcome :
  temps!(ncs_root_cache shape)=Some(Vint root) ->
  temps!(ncs_child_cache shape)=Some(Vint child) ->
  eval_expr ge locals temps memory(memory_source_affine_code expression)(Vint word) ->
  exec_stmt fe ge locals temps memory
    (if ncs_same_word_flag shape word(Entry ge locals temps memory)
     then Sset(affine_proposed_result proposal)(Econst_int Int.one type_int32s)
     else ncs_stability_code shape proposal) trace after final outcome ->
  exec_stmt fe ge locals temps memory(ncs_invariant_or_scan shape proposal expression) trace after final outcome.
Proof.
  intros ROOT CHILD VALUE RUN.
  destruct(@ncs_invariant_pair_expression_test ge locals temps memory shape expression word root child ROOT CHILD VALUE)
    as [value [EVAL BOOL]].
  unfold ncs_invariant_or_scan; eapply exec_Sifthenelse; [exact EVAL|exact BOOL|exact RUN].
Qed.

Section STABILITY.
Variables source : statement.
Variables parameters live : list ident.
Variable proposal : affine_guard_proposal.
Variable shape : nested_constant_shape.
Variable site : nested_constant_site source parameters live proposal shape.

Record ncs_invariant_stability_receipt fe ge locals checked memory checked_source_after final after : Prop := NCSInvariantStabilityReceipt {
  ncs_invariant_stability_run : exec_stmt fe ge locals (ncs_prepared_temps shape checked) memory
    (ncs_invariant_stability_code parameters shape proposal) E0 after memory Out_normal;
  ncs_invariant_stability_frame : temp_agree (ncs_ports source parameters live shape) (ncs_prepared_temps shape checked) after;
  ncs_invariant_stability_boolean : exists accepted, after!(affine_proposed_result proposal) = Some (memory_boolean_word accepted);
  ncs_invariant_stability_accept : after!(affine_proposed_result proposal) = Some (memory_boolean_word true) -> exists model_after,
    exec_stmt fe ge locals (ncs_prepared_temps shape checked) memory (ncs_model shape) E0 model_after final Out_normal /\
    temp_agree (ncs_scope source live) checked_source_after model_after
}.

Theorem ncs_invariant_stability_execution fe ge locals checked memory checked_source_after final
  (prepared : ncs_prepared_receipt source parameters live proposal shape fe ge locals checked memory checked_source_after final) :
  exists after, ncs_invariant_stability_receipt fe ge locals checked memory checked_source_after final after.
Proof.
  destruct(ncs_stability_execution site prepared) as [scan_after SCAN].
  destruct(ncs_invariant_expression parameters shape) as [expression|] eqn:EXPRESSION.
  - destruct(@ncs_invariant_expression_sound parameters shape expression EXPRESSION) as [BODY READS].
    pose proof(@ncs_prepared_invariant_value source parameters live proposal shape expression
      fe ge locals checked memory checked_source_after final prepared READS) as VALUE.
    set(word:=ncs_invariant_word expression(ncs_prepared_temps shape checked)) in *.
    destruct(ncs_prepare_observers prepared) as [block [offset [raw [child_raw HEADERS]]]].
    destruct(ncs_receipt_ready HEADERS) as [ROOT CHILD].
    destruct ROOT as [b [o [r [P [READ CACHE]]]]].
    destruct CHILD as [b' [o' [r' [P' [READ' CACHE']]]]].
    destruct(ncs_same_word_flag shape word(Entry ge locals(ncs_prepared_temps shape checked) memory)) eqn:FAST.
    + exists(PTree.set(affine_proposed_result proposal)(Vint Int.one)(ncs_prepared_temps shape checked)); constructor.
      * unfold ncs_invariant_stability_code; rewrite EXPRESSION.
        eapply ncs_invariant_or_scan_execution with(word:=word)(root:=Int.add r(ncs_delta shape))
          (child:=Int.add r'(ncs_child_delta shape)); [exact CACHE|exact CACHE'|exact VALUE|].
        rewrite FAST; constructor; constructor.
      * apply temp_agree_set; intro BAD; apply(ncs_scan_flag_private site).
        apply in_or_app; right; exact BAD.
      * exists true; apply PTree.gss.
      * intro SUCCESS; eapply ncs_invariant_word_accepted_model; [exact site| |exact BODY|exact prepared|exact VALUE|exact FAST].
        intros identifier MEMBER; apply(ncs_site_parameters_stable site),READS; exact MEMBER.
    + exists scan_after; constructor.
      * unfold ncs_invariant_stability_code; rewrite EXPRESSION.
        eapply ncs_invariant_or_scan_execution with(word:=word)(root:=Int.add r(ncs_delta shape))
          (child:=Int.add r'(ncs_child_delta shape)); [exact CACHE|exact CACHE'|exact VALUE|].
        rewrite FAST; exact(ncs_stability_run SCAN).
      * exact(ncs_stability_frame SCAN).
      * exact(ncs_stability_boolean SCAN).
      * exact(ncs_stability_accept SCAN).
  - exists scan_after; constructor.
    + unfold ncs_invariant_stability_code; rewrite EXPRESSION; exact(ncs_stability_run SCAN).
    + exact(ncs_stability_frame SCAN).
    + exact(ncs_stability_boolean SCAN).
    + exact(ncs_stability_accept SCAN).
Qed.
End STABILITY.

Definition ncs_invariant_stability_guard source parameters live proposal shape
  (site : nested_constant_site source parameters live proposal shape) :=
  Ssequence (ncs_entry_numeric_code site)
    (Sifthenelse (Etempvar (affine_proposed_result proposal) type_int32s)
      (Ssequence (ncs_prepare_code shape) (ncs_invariant_stability_code parameters shape proposal)) Sskip).

Section PHYSICAL.
Variables source : statement.
Variables parameters live : list ident.
Variable proposal : affine_guard_proposal.
Variable shape : nested_constant_shape.
Variable site : nested_constant_site source parameters live proposal shape.

Record ncs_invariant_stability_physical_receipt fe ge locals original memory original_after final after : Prop := NCSInvariantStabilityPhysicalReceipt {
  ncs_invariant_stability_physical_run : exec_stmt fe ge locals original memory (ncs_invariant_stability_guard site) E0 after memory Out_normal;
  ncs_invariant_stability_physical_public : temp_agree (ncs_scope source live) original after;
  ncs_invariant_stability_physical_boolean : exists accepted, after!(affine_proposed_result proposal) = Some (memory_boolean_word accepted);
  ncs_invariant_stability_physical_source : exists source_after,
    exec_stmt fe ge locals after memory source E0 source_after final Out_normal /\
    temp_agree (ncs_scope source live) original_after source_after;
  ncs_invariant_stability_physical_accept : after!(affine_proposed_result proposal) = Some (memory_boolean_word true) ->
    exists model_entry model_after,
    temp_agree (ncs_ports source parameters live shape) model_entry after /\
    ncs_numeric_flag parameters proposal shape (Entry ge locals model_entry memory) = true /\
    exec_stmt fe ge locals model_entry memory (ncs_model shape) E0 model_after final Out_normal /\
    temp_agree (ncs_scope source live) original_after model_after
}.

Theorem ncs_original_invariant_stability_guard_execution fe ge locals original memory original_after final :
  exec_stmt fe ge locals original memory source E0 original_after final Out_normal ->
  exists after, ncs_invariant_stability_physical_receipt fe ge locals original memory original_after final after.
Proof.
  intro SOURCE.
  destruct (ncs_entry_numeric_execution site SOURCE) as [checked ENTRY].
  pose proof (ncs_entry_result ENTRY) as FLAG.
  destruct (ncs_entry_numeric_flag parameters proposal shape (Entry ge locals checked memory)) eqn:NUMERIC.
  - pose proof (ncs_entry_accept ENTRY NUMERIC) as RECEIPT.
    assert (ACCEPT : ncs_numeric_flag parameters proposal shape (Entry ge locals checked memory) = true).
    { unfold ncs_entry_numeric_flag in NUMERIC; apply andb_true_iff in NUMERIC; exact (proj2 NUMERIC). }
    destruct (ncs_accepted_numeric_prepare RECEIPT ACCEPT) as [checked_source_after [CHECKED_PUBLIC PREPARED]].
    destruct (@ncs_invariant_stability_execution source parameters live proposal shape site fe ge locals checked memory
      checked_source_after final PREPARED) as [after STABILITY].
    assert (PUBLIC : temp_agree (ncs_scope source live) original after).
    { eapply temp_agree_trans; [exact (ncs_entry_public ENTRY)|].
      eapply temp_agree_trans; [exact (ncs_prepare_public PREPARED)|].
      eapply temp_agree_weaken; [apply ncs_scope_scan_ports|exact (ncs_invariant_stability_frame STABILITY)]. }
    exists after; constructor.
    + unfold ncs_invariant_stability_guard; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=checked) (m1:=memory).
      * exact (ncs_entry_run ENTRY).
      * eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
        -- constructor; exact FLAG.
        -- reflexivity.
        -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);
          [exact (ncs_prepare_run PREPARED)|exact (ncs_invariant_stability_run STABILITY)].
    + exact PUBLIC.
    + exact (ncs_invariant_stability_boolean STABILITY).
    + eapply structured_execution_temp_transport with (live:=ncs_scope source live) (allowed:=statement_temps source).
      * exact SOURCE.
      * apply check_plan_frameable_writes; exact (ncs_frameable site).
      * unfold statement_scope, ncs_scope; intros identifier MEMBER; apply in_or_app; left; exact MEMBER.
      * exact PUBLIC.
    + intro SUCCESS; destruct (ncs_invariant_stability_accept STABILITY SUCCESS) as [model_after [MODEL MODEL_PUBLIC]].
      exists (ncs_prepared_temps shape checked), model_after; split; [exact (ncs_invariant_stability_frame STABILITY)|split].
      * exact (ncs_prepare_accept PREPARED).
      * split; [exact MODEL|eapply temp_agree_trans; eassumption].
  - exists checked; constructor.
    + unfold ncs_invariant_stability_guard; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=checked) (m1:=memory).
      * exact (ncs_entry_run ENTRY).
      * eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);
        [constructor; exact FLAG|reflexivity|constructor].
    + exact (ncs_entry_public ENTRY).
    + exists false; exact FLAG.
    + exact (ncs_entry_source ENTRY).
    + intro SUCCESS; rewrite FLAG in SUCCESS; discriminate.
Qed.
End PHYSICAL.

Print Assumptions ncs_invariant_or_scan_execution.
Print Assumptions ncs_invariant_stability_execution.
Print Assumptions ncs_original_invariant_stability_guard_execution.
