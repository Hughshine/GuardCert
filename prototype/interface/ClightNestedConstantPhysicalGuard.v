From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightNoWrap ClightProjectedExecution
  ClightRegionProgress ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryBooleanScan GuardMemoryRuntime GuardMemoryLoops GuardMemoryWindowCells.
From GuardAffineNest Require Import AffineNestGuardPackage AffineNestPackageGuard AffineNestPackageDecode AffineNestExit.
From GuardInterface Require Import ClightNestedConstantSite ClightNestedConstantSiteFacts
  ClightNestedConstantEntryGate ClightNestedConstantSiteNumeric ClightNestedConstantSitePrepare
  ClightNestedConstantOuterConsumer ClightNestedConstantScanNames ClightNestedConstantScanStatic
  ClightNestedConstantHeaders ClightConstantBoundModel ClightCheckPlanFrame ClightNestedConstantNumericGuard.
Import ListNotations.
Set Implicit Arguments.

Definition ncs_physical_guard source parameters live proposal shape
  (site:nested_constant_site source parameters live proposal shape) :=
  Ssequence(ncs_entry_numeric_code site)
    (Sifthenelse(Etempvar(affine_proposed_result proposal) type_int32s)
      (Ssequence(ncs_prepare_code shape)(ncs_outer_code shape proposal)) Sskip).

Lemma ncs_numeric_package_accept parameters proposal shape entry :
  ncs_numeric_flag parameters proposal shape entry=true -> affine_package_guard_flag parameters proposal entry=true.
Proof.
  intro ACCEPT; unfold ncs_numeric_flag,nested_constant_numeric_flag in ACCEPT.
  destruct(register_positive(ncs_root_cache shape) entry); [|discriminate].
  destruct(register_positive(ncs_child_cache shape) entry); [|discriminate]; exact ACCEPT.
Qed.

Section GUARD.
Variables source : statement.
Variables parameters live : list ident.
Variable proposal : affine_guard_proposal.
Variable shape : nested_constant_shape.
Variable site : nested_constant_site source parameters live proposal shape.

Lemma ncs_scope_scan_ports : incl(ncs_scope source live)(ncs_ports source parameters live shape).
Proof.
  intros identifier MEMBER; unfold ncs_ports,ncs_package_live; apply in_or_app; right; apply in_or_app; right;
    apply in_or_app; left; exact MEMBER.
Qed.

(** Acceptance carries a separate source/model entry plus its frame to the
    actual guard exit. The candidate adapter must consume this relation;
    private guard cursors are never confused with source coordinates. *)
Record ncs_physical_receipt fe ge locals original memory original_after final after : Prop := NCSPhysicalReceipt {
  ncs_physical_run : exec_stmt fe ge locals original memory(ncs_physical_guard site) E0 after memory Out_normal;
  ncs_physical_public : temp_agree(ncs_scope source live) original after;
  ncs_physical_boolean : exists accepted,after!(affine_proposed_result proposal)=Some(memory_boolean_word accepted);
  ncs_physical_source : exists source_after,exec_stmt fe ge locals after memory source E0 source_after final Out_normal /\
    temp_agree(ncs_scope source live) original_after source_after;
  ncs_physical_accept : after!(affine_proposed_result proposal)=Some(memory_boolean_word true) -> exists model_entry model_after,
    temp_agree(ncs_ports source parameters live shape) model_entry after /\
    ncs_numeric_flag parameters proposal shape(Entry ge locals model_entry memory)=true /\
    exec_stmt fe ge locals model_entry memory(ncs_model shape) E0 model_after final Out_normal /\
    temp_agree(ncs_scope source live) original_after model_after
}.

Theorem ncs_original_physical_guard_execution fe ge locals original memory original_after final :
  exec_stmt fe ge locals original memory source E0 original_after final Out_normal ->
  exists after,ncs_physical_receipt fe ge locals original memory original_after final after.
Proof.
  intro SOURCE.
  destruct(ncs_entry_numeric_execution site SOURCE) as [checked ENTRY].
  pose proof(ncs_entry_result ENTRY) as FLAG.
  destruct(ncs_entry_numeric_flag parameters proposal shape(Entry ge locals checked memory)) eqn:NUMERIC.
  - pose proof(ncs_entry_accept ENTRY NUMERIC) as RECEIPT.
    assert(ACCEPT : ncs_numeric_flag parameters proposal shape(Entry ge locals checked memory)=true).
    { unfold ncs_entry_numeric_flag in NUMERIC; apply andb_true_iff in NUMERIC; exact(proj2 NUMERIC). }
    destruct(ncs_accepted_numeric_prepare RECEIPT ACCEPT) as [checked_source_after [CHECKED_PUBLIC PREPARED]].
    destruct(ncs_prepared_initial_prefix site PREPARED) as [block [offset [raw [child_raw [HEADERS PREFIX]]]]].
    destruct(@ncs_outer_scan_execution source parameters live proposal shape site fe ge locals checked memory
      checked_source_after final PREPARED _ HEADERS PREFIX) as [after [RUN [KEEP RESULT]]].
    assert(PUBLIC : temp_agree(ncs_scope source live) original after).
    { eapply temp_agree_trans; [exact(ncs_entry_public ENTRY)|].
      eapply temp_agree_trans; [exact(ncs_prepare_public PREPARED)|].
      eapply temp_agree_weaken; [exact ncs_scope_scan_ports|exact KEEP]. }
    exists after; constructor.
    + unfold ncs_physical_guard; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=checked)(m1:=memory).
      * exact(ncs_entry_run ENTRY).
      * eapply exec_Sifthenelse with(v1:=Vint Int.one)(b:=true).
        -- constructor; exact FLAG.
        -- reflexivity.
        -- eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact(ncs_prepare_run PREPARED)|exact RUN].
    + exact PUBLIC.
    + eexists; exact RESULT.
    + eapply structured_execution_temp_transport with(live:=ncs_scope source live)(allowed:=statement_temps source).
      * exact SOURCE.
      * apply check_plan_frameable_writes; exact(ncs_frameable site).
      * unfold statement_scope,ncs_scope; intros identifier MEMBER; apply in_or_app; left; exact MEMBER.
      * exact PUBLIC.
    + intro SUCCESS.
      assert(PHYSICAL : ncs_outer_result shape proposal(Entry ge locals(ncs_prepared_temps shape checked) memory)
        (ncs_observers shape block offset raw child_raw)=true).
      { rewrite RESULT in SUCCESS.
        destruct(ncs_outer_result shape proposal(Entry ge locals(ncs_prepared_temps shape checked) memory)
          (ncs_observers shape block offset raw child_raw)); [reflexivity|discriminate]. }
      destruct(@ncs_outer_accepted_model source parameters live proposal shape site fe ge locals checked memory
        checked_source_after final PREPARED _ HEADERS PREFIX PHYSICAL) as [model_after [MODEL MODEL_PUBLIC]].
      exists(ncs_prepared_temps shape checked),model_after; split; [exact KEEP|split].
      * exact(ncs_prepare_accept PREPARED).
      * split; [exact MODEL|eapply temp_agree_trans; eassumption].
  - exists checked; constructor.
    + unfold ncs_physical_guard; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=checked)(m1:=memory).
      * exact(ncs_entry_run ENTRY).
      * eapply exec_Sifthenelse with(v1:=Vint Int.zero)(b:=false); [constructor; exact FLAG|reflexivity|constructor].
    + exact(ncs_entry_public ENTRY).
    + exists false; exact FLAG.
    + exact(ncs_entry_source ENTRY).
    + intro SUCCESS; rewrite FLAG in SUCCESS; discriminate.
Qed.

(** The existing verified decoder consumes the actual canonical Clight run
    produced above. Lowering is an option result from a data algorithm; it is
    not an additional source/model execution premise. The source-loop entry
    remains explicit and framed to the actual exit for a later candidate adapter. *)
Theorem ncs_physical_accepted_source_loop fe ge locals original memory original_after final after
  (receipt:ncs_physical_receipt fe ge locals original memory original_after final after) source_loop :
  affine_package_source_loop parameters proposal=Some source_loop ->
  after!(affine_proposed_result proposal)=Some(memory_boolean_word true) -> exists model_entry,
    temp_agree(ncs_ports source parameters live shape) model_entry after /\
    L.loop_semantics source_loop(map(affine_word_valuation model_entry)(affine_package_context parameters proposal))
      (RuntimeState(window_multi_pointer_locations model_entry(affine_proposed_window_lower proposal)
        (affine_proposed_window_upper proposal)) memory)
      (RuntimeState(window_multi_pointer_locations model_entry(affine_proposed_window_lower proposal)
        (affine_proposed_window_upper proposal)) final).
Proof.
  intros LOWER ACCEPT.
  destruct(ncs_physical_accept receipt ACCEPT) as [model_entry [model_after [FRAME [NUMERIC [MODEL PUBLIC]]]]].
  exists model_entry; split; [exact FRAME|].
  eapply affine_package_source_decode with(package:=ncs_package site)(after:=model_after).
  - intros identifier MEMBER; rewrite(ncs_model_exact site); apply(ncs_scan_model_pointer_private site); exact MEMBER.
  - exact LOWER.
  - eapply ncs_numeric_package_accept; exact NUMERIC.
  - exact MODEL.
Qed.
End GUARD.

Print Assumptions ncs_scope_scan_ports.
Print Assumptions ncs_numeric_package_accept.
Print Assumptions ncs_original_physical_guard_execution.
Print Assumptions ncs_physical_accepted_source_loop.
