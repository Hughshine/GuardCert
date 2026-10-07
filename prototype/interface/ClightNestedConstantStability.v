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
  ClightCheckPlanFrame ClightNestedConstantPhysicalGuard ClightNestedConstantEntryGate.
Import ListNotations.
Set Implicit Arguments.

(** A proposal only: the typed BODY checker below certifies the selected word. *)
Fixpoint first_store_word (body : statement) : option int :=
  match body with
  | Sassign _ (Econst_int word _) => Some word
  | Ssequence first second | Sifthenelse _ first second =>
      match first_store_word first with Some word => Some word | None => first_store_word second end
  | _ => None
  end.
Definition ncs_stability_word shape :=
  match first_store_word (ncs_leaf shape) with
  | Some word => if check_constant_word_statement word (ncs_leaf shape) then Some word else None
  | None => None
  end.
Theorem ncs_stability_word_sound shape word :
  ncs_stability_word shape = Some word -> check_constant_word_statement word (ncs_leaf shape) = true.
Proof.
  unfold ncs_stability_word; destruct (first_store_word (ncs_leaf shape)) as [proposed|]; [|discriminate].
  destruct (check_constant_word_statement proposed (ncs_leaf shape)) eqn:CHECK; [|discriminate].
  intro SAME; inversion SAME; subst; exact CHECK.
Qed.

Definition ncs_word_or_scan shape proposal word :=
  Sifthenelse (ncs_word_equal_expression (ncs_root_cache shape) (Int.add word (ncs_delta shape)))
    (Sifthenelse (ncs_word_equal_expression (ncs_child_cache shape) (Int.add word (ncs_child_delta shape)))
      (Sset (affine_proposed_result proposal) (Econst_int Int.one type_int32s))
      (ncs_outer_code shape proposal)) (ncs_outer_code shape proposal).
Definition ncs_stability_code shape proposal :=
  match ncs_stability_word shape with
  | Some word => ncs_word_or_scan shape proposal word
  | None => ncs_outer_code shape proposal
  end.

(** Pure comparison failures leave the scan's entry exactly unchanged. *)
Theorem ncs_word_or_scan_execution fe ge locals temps memory shape proposal word root child trace after final outcome :
  temps!(ncs_root_cache shape) = Some (Vint root) ->
  temps!(ncs_child_cache shape) = Some (Vint child) ->
  exec_stmt fe ge locals temps memory
    (if ncs_same_word_flag shape word (Entry ge locals temps memory)
     then Sset (affine_proposed_result proposal) (Econst_int Int.one type_int32s)
     else ncs_outer_code shape proposal) trace after final outcome ->
  exec_stmt fe ge locals temps memory (ncs_word_or_scan shape proposal word) trace after final outcome.
Proof.
  intros ROOT CHILD RUN.
  destruct (@ncs_word_equal_expression_test ge locals temps memory (ncs_root_cache shape)
    root (Int.add word (ncs_delta shape)) ROOT) as [rv [REVAL RBOOL]].
  destruct (@ncs_word_equal_expression_test ge locals temps memory (ncs_child_cache shape)
    child (Int.add word (ncs_child_delta shape)) CHILD) as [cv [CEVAL CBOOL]].
  unfold ncs_word_or_scan; unfold ncs_same_word_flag in RUN; cbn [entry_temps] in RUN.
  unfold temp_word in RUN; rewrite ROOT, CHILD in RUN.
  destruct (Int.eq root (Int.add word (ncs_delta shape))) eqn:R;
    destruct (Int.eq child (Int.add word (ncs_child_delta shape))) eqn:C; cbn in RUN.
  all: eapply exec_Sifthenelse; [exact REVAL|exact RBOOL|]; cbn.
  all: try (eapply exec_Sifthenelse; [exact CEVAL|exact CBOOL|]; cbn).
  all: exact RUN.
Qed.

Section STABILITY.
Variables source : statement.
Variables parameters live : list ident.
Variable proposal : affine_guard_proposal.
Variable shape : nested_constant_shape.
Variable site : nested_constant_site source parameters live proposal shape.

Record ncs_stability_receipt fe ge locals checked memory checked_source_after final after : Prop := NCSStabilityReceipt {
  ncs_stability_run : exec_stmt fe ge locals (ncs_prepared_temps shape checked) memory
    (ncs_stability_code shape proposal) E0 after memory Out_normal;
  ncs_stability_frame : temp_agree (ncs_ports source parameters live shape) (ncs_prepared_temps shape checked) after;
  ncs_stability_boolean : exists accepted, after!(affine_proposed_result proposal) = Some (memory_boolean_word accepted);
  ncs_stability_accept : after!(affine_proposed_result proposal) = Some (memory_boolean_word true) -> exists model_after,
    exec_stmt fe ge locals (ncs_prepared_temps shape checked) memory (ncs_model shape) E0 model_after final Out_normal /\
    temp_agree (ncs_scope source live) checked_source_after model_after
}.

Theorem ncs_stability_execution fe ge locals checked memory checked_source_after final
  (prepared : ncs_prepared_receipt source parameters live proposal shape fe ge locals checked memory checked_source_after final) :
  exists after, ncs_stability_receipt fe ge locals checked memory checked_source_after final after.
Proof.
  destruct (ncs_prepared_initial_prefix site prepared) as [block [offset [raw [child_raw [HEADERS PREFIX]]]]].
  destruct (@ncs_outer_scan_execution source parameters live proposal shape site fe ge locals checked memory
    checked_source_after final prepared _ HEADERS PREFIX) as [scan_after [SCAN [SCAN_FRAME SCAN_RESULT]]].
  assert (SCAN_ACCEPT : scan_after!(affine_proposed_result proposal) = Some (memory_boolean_word true) -> exists model_after,
    exec_stmt fe ge locals (ncs_prepared_temps shape checked) memory (ncs_model shape) E0 model_after final Out_normal /\
    temp_agree (ncs_scope source live) checked_source_after model_after).
  { intro ACCEPT.
    assert (FLAG : ncs_outer_result shape proposal (Entry ge locals (ncs_prepared_temps shape checked) memory)
      (ncs_observers shape block offset raw child_raw) = true).
    { rewrite SCAN_RESULT in ACCEPT; destruct (ncs_outer_result shape proposal
        (Entry ge locals (ncs_prepared_temps shape checked) memory) (ncs_observers shape block offset raw child_raw));
        [reflexivity|discriminate]. }
    eapply ncs_outer_accepted_model; eassumption. }
  destruct (ncs_stability_word shape) as [word|] eqn:WORD.
  - pose proof (@ncs_stability_word_sound shape word WORD) as BODY.
    destruct (ncs_receipt_ready HEADERS) as [ROOT CHILD].
    destruct ROOT as [b [o [r [P [READ CACHE]]]]].
    destruct CHILD as [b' [o' [r' [P' [READ' CACHE']]]]].
    destruct (ncs_same_word_flag shape word (Entry ge locals (ncs_prepared_temps shape checked) memory)) eqn:FAST.
    + exists (PTree.set (affine_proposed_result proposal) (Vint Int.one) (ncs_prepared_temps shape checked)); constructor.
      * unfold ncs_stability_code; rewrite WORD.
        eapply ncs_word_or_scan_execution with (root:=Int.add r (ncs_delta shape))
          (child:=Int.add r' (ncs_child_delta shape)); [exact CACHE|exact CACHE'|].
        rewrite FAST.
        constructor; constructor.
      * apply temp_agree_set; intro BAD; apply (ncs_scan_flag_private site).
        apply in_or_app; right; exact BAD.
      * exists true; apply PTree.gss.
      * intro SUCCESS; eapply ncs_same_word_accepted_model; eassumption.
    + exists scan_after; constructor.
      * unfold ncs_stability_code; rewrite WORD.
        eapply ncs_word_or_scan_execution with (root:=Int.add r (ncs_delta shape))
          (child:=Int.add r' (ncs_child_delta shape)); [exact CACHE|exact CACHE'|].
        rewrite FAST; exact SCAN.
      * exact SCAN_FRAME.
      * eexists; exact SCAN_RESULT.
      * exact SCAN_ACCEPT.
  - exists scan_after; constructor.
    + unfold ncs_stability_code; rewrite WORD; exact SCAN.
    + exact SCAN_FRAME.
    + eexists; exact SCAN_RESULT.
    + exact SCAN_ACCEPT.
Qed.
End STABILITY.

Definition ncs_stability_guard source parameters live proposal shape
  (site : nested_constant_site source parameters live proposal shape) :=
  Ssequence (ncs_entry_numeric_code site)
    (Sifthenelse (Etempvar (affine_proposed_result proposal) type_int32s)
      (Ssequence (ncs_prepare_code shape) (ncs_stability_code shape proposal)) Sskip).

Section PHYSICAL.
Variables source : statement.
Variables parameters live : list ident.
Variable proposal : affine_guard_proposal.
Variable shape : nested_constant_shape.
Variable site : nested_constant_site source parameters live proposal shape.

Record ncs_stability_physical_receipt fe ge locals original memory original_after final after : Prop := NCSStabilityPhysicalReceipt {
  ncs_stability_physical_run : exec_stmt fe ge locals original memory (ncs_stability_guard site) E0 after memory Out_normal;
  ncs_stability_physical_public : temp_agree (ncs_scope source live) original after;
  ncs_stability_physical_boolean : exists accepted, after!(affine_proposed_result proposal) = Some (memory_boolean_word accepted);
  ncs_stability_physical_source : exists source_after,
    exec_stmt fe ge locals after memory source E0 source_after final Out_normal /\
    temp_agree (ncs_scope source live) original_after source_after;
  ncs_stability_physical_accept : after!(affine_proposed_result proposal) = Some (memory_boolean_word true) ->
    exists model_entry model_after,
    temp_agree (ncs_ports source parameters live shape) model_entry after /\
    ncs_numeric_flag parameters proposal shape (Entry ge locals model_entry memory) = true /\
    exec_stmt fe ge locals model_entry memory (ncs_model shape) E0 model_after final Out_normal /\
    temp_agree (ncs_scope source live) original_after model_after
}.

Theorem ncs_original_stability_guard_execution fe ge locals original memory original_after final :
  exec_stmt fe ge locals original memory source E0 original_after final Out_normal ->
  exists after, ncs_stability_physical_receipt fe ge locals original memory original_after final after.
Proof.
  intro SOURCE.
  destruct (ncs_entry_numeric_execution site SOURCE) as [checked ENTRY].
  pose proof (ncs_entry_result ENTRY) as FLAG.
  destruct (ncs_entry_numeric_flag parameters proposal shape (Entry ge locals checked memory)) eqn:NUMERIC.
  - pose proof (ncs_entry_accept ENTRY NUMERIC) as RECEIPT.
    assert (ACCEPT : ncs_numeric_flag parameters proposal shape (Entry ge locals checked memory) = true).
    { unfold ncs_entry_numeric_flag in NUMERIC; apply andb_true_iff in NUMERIC; exact (proj2 NUMERIC). }
    destruct (ncs_accepted_numeric_prepare RECEIPT ACCEPT) as [checked_source_after [CHECKED_PUBLIC PREPARED]].
    destruct (@ncs_stability_execution source parameters live proposal shape site fe ge locals checked memory
      checked_source_after final PREPARED) as [after STABILITY].
    assert (PUBLIC : temp_agree (ncs_scope source live) original after).
    { eapply temp_agree_trans; [exact (ncs_entry_public ENTRY)|].
      eapply temp_agree_trans; [exact (ncs_prepare_public PREPARED)|].
      eapply temp_agree_weaken; [apply ncs_scope_scan_ports|exact (ncs_stability_frame STABILITY)]. }
    exists after; constructor.
    + unfold ncs_stability_guard; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=checked) (m1:=memory).
      * exact (ncs_entry_run ENTRY).
      * eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
        -- constructor; exact FLAG.
        -- reflexivity.
        -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);
          [exact (ncs_prepare_run PREPARED)|exact (ncs_stability_run STABILITY)].
    + exact PUBLIC.
    + exact (ncs_stability_boolean STABILITY).
    + eapply structured_execution_temp_transport with (live:=ncs_scope source live) (allowed:=statement_temps source).
      * exact SOURCE.
      * apply check_plan_frameable_writes; exact (ncs_frameable site).
      * unfold statement_scope, ncs_scope; intros identifier MEMBER; apply in_or_app; left; exact MEMBER.
      * exact PUBLIC.
    + intro SUCCESS; destruct (ncs_stability_accept STABILITY SUCCESS) as [model_after [MODEL MODEL_PUBLIC]].
      exists (ncs_prepared_temps shape checked), model_after; split; [exact (ncs_stability_frame STABILITY)|split].
      * exact (ncs_prepare_accept PREPARED).
      * split; [exact MODEL|eapply temp_agree_trans; eassumption].
  - exists checked; constructor.
    + unfold ncs_stability_guard; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=checked) (m1:=memory).
      * exact (ncs_entry_run ENTRY).
      * eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);
        [constructor; exact FLAG|reflexivity|constructor].
    + exact (ncs_entry_public ENTRY).
    + exists false; exact FLAG.
    + exact (ncs_entry_source ENTRY).
    + intro SUCCESS; rewrite FLAG in SUCCESS; discriminate.
Qed.
End PHYSICAL.

Print Assumptions ncs_stability_word_sound.
Print Assumptions ncs_word_or_scan_execution.
Print Assumptions ncs_stability_execution.
Print Assumptions ncs_original_stability_guard_execution.
