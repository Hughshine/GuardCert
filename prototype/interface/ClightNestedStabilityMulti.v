From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightProjectedExecution ClightRegionProgress.
From GuardMemory Require Import GuardMemoryBooleanScan.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestGuardPackage AffineNestPackageGuard
  AffineNestMultiStaticPackage AffineNestMultiPresumption AffineNestAliasOnlyGuard AffineNestGuardFactTransport.
From GuardInterface Require Import ClightNestedConstantSite ClightNestedConstantSiteFacts ClightNestedConstantPhysicalGuard
  ClightNestedConstantSiteNumeric ClightNestedConstantMultiSite ClightAffineNestMaterialized ClightSharedGuard
  ClightNestedConstantScanStatic ClightNestedExpressionCapture ClightStrictLoopProgress ClightCheckPlanFrame
  ClightNestedConstantStability ClightNestedConstantMultiExecution ClightMaterializedCheck.
Import ListNotations.
Set Implicit Arguments.

Definition ncs_stability_multi_body source parameters live allocated proposal shape
  (site : ncs_multi_site source parameters live allocated proposal shape) :=
  Ssequence (ncs_stability_guard (ncs_multi_original site))
    (Sifthenelse (shared_guard_choice (affine_proposed_result proposal))
      (affine_multi_alias_only_code (ncs_multi_package site)) Sskip).

Section EXECUTION.
Variables source : statement.
Variables parameters live allocated : list ident.
Variable proposal : affine_guard_proposal.
Variable shape : nested_constant_shape.
Variable site : ncs_multi_site source parameters live allocated proposal shape.
Let original_site:=ncs_multi_original site.
Let package:=ncs_multi_package site.
Let ports:=ncs_ports source parameters live shape.
Let scope:=ncs_scope source live.

Theorem ncs_stability_canonical_at_guard_exit fe ge locals original memory original_after final checked
  (receipt:ncs_stability_physical_receipt original_site fe ge locals original memory original_after final checked) :
  checked!(affine_proposed_result proposal)=Some(memory_boolean_word true) -> exists model_after,
    exec_stmt fe ge locals checked memory(ncs_model shape) E0 model_after final Out_normal /\
    temp_agree scope original_after model_after /\
    affine_package_guard_flag parameters proposal(Entry ge locals checked memory)=true.
Proof.
  intro ACCEPT.
  destruct(ncs_stability_physical_accept receipt ACCEPT) as [anchor [after [FRAME [NUMERIC [MODEL PUBLIC]]]]].
  destruct(@structured_execution_temp_transport fe ge locals anchor memory(ncs_model shape) E0 after final Out_normal MODEL
    ports checked(affine_nest_controls(affine_proposal_nest proposal))
    (affine_materialized_source_writes(affine_multi_guard package))(ncs_multi_model_scope site) FRAME)
    as [checked_after [CURRENT EXIT]].
  exists checked_after; split; [exact CURRENT|split].
  - eapply temp_agree_trans; [exact PUBLIC|].
    eapply temp_agree_weaken; [apply ncs_scope_scan_ports|exact EXIT].
  - apply(@ncs_numeric_package_accept parameters proposal shape(Entry ge locals checked memory)).
    rewrite(@ncs_numeric_flag_frame _ _ _ _ _ original_site ge locals memory anchor checked).
    + exact NUMERIC.
    + eapply temp_agree_weaken; [apply ncs_multi_numeric_ports|exact FRAME].
Qed.

Record ncs_stability_multi_receipt fe ge locals original memory original_after final checked : Prop := NCSStabilityMultiReceipt {
  ncs_stability_multi_run : exec_stmt fe ge locals original memory(ncs_stability_multi_body site) E0 checked memory Out_normal;
  ncs_stability_multi_public : temp_agree scope original checked;
  ncs_stability_multi_answer : exists accepted,expression_test(shared_guard_choice(affine_proposed_result proposal))
    (Entry ge locals checked memory) accepted;
  ncs_stability_multi_boolean : exists accepted,checked!(affine_proposed_result proposal)=Some(memory_boolean_word accepted);
  ncs_stability_multi_source : exists after,exec_stmt fe ge locals checked memory source E0 after final Out_normal /\
    temp_agree scope original_after after;
  ncs_stability_multi_accept : checked!(affine_proposed_result proposal)=Some(memory_boolean_word true) -> exists reference after,
    temp_agree ports reference checked /\
    affine_multi_guard_flag parameters proposal(Entry ge locals reference memory)=true /\
    exec_stmt fe ge locals reference memory(ncs_model shape) E0 after final Out_normal /\
    temp_agree scope original_after after
}.

Theorem ncs_stability_multi_execution fe ge locals original memory original_after final :
  exec_stmt fe ge locals original memory source E0 original_after final Out_normal ->
  exists checked,ncs_stability_multi_receipt fe ge locals original memory original_after final checked.
Proof.
  intro SOURCE.
  destruct(ncs_original_stability_guard_execution original_site SOURCE) as [reference RECEIPT].
  destruct(ncs_stability_physical_boolean RECEIPT) as [active FLAG].
  destruct(@shared_guard_choice_test ge locals reference memory(affine_proposed_result proposal) active FLAG)
    as [value [EVAL BOOL]].
  destruct active.
  - destruct(ncs_stability_canonical_at_guard_exit RECEIPT FLAG) as [after [MODEL [PUBLIC NUMERIC]]].
    destruct(@affine_multi_alias_only_execution _ _ _ _ _ package fe ge locals reference memory after final
      MODEL NUMERIC FLAG) as [checked [ALIAS [KEEP RESULT]]].
    assert(PUBLIC_ENTRY : temp_agree scope original checked).
    { eapply temp_agree_trans; [exact(ncs_stability_physical_public RECEIPT)|].
      eapply temp_agree_weaken; [apply ncs_scope_scan_ports|exact KEEP]. }
    exists checked; constructor.
    + unfold ncs_stability_multi_body; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact(ncs_stability_physical_run RECEIPT)|].
      eapply exec_Sifthenelse with(v1:=value)(b:=true); eassumption.
    + exact PUBLIC_ENTRY.
    + eexists; apply shared_guard_choice_test; exact RESULT.
    + eexists; exact RESULT.
    + eapply structured_execution_temp_transport with(live:=scope)(allowed:=statement_temps source).
      * exact SOURCE.
      * apply check_plan_frameable_writes; exact(ncs_frameable original_site).
      * unfold statement_scope,scope,ncs_scope; intros identifier MEMBER; apply in_or_app; left; exact MEMBER.
      * exact PUBLIC_ENTRY.
    + intro SUCCESS.
      assert(ACCEPT : affine_multi_guard_flag parameters proposal(Entry ge locals reference memory)=true).
      { rewrite RESULT in SUCCESS; destruct(affine_multi_guard_flag parameters proposal(Entry ge locals reference memory));
          [reflexivity|discriminate]. }
      exists reference,after; repeat split; assumption.
  - exists reference; constructor.
    + unfold ncs_stability_multi_body; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact(ncs_stability_physical_run RECEIPT)|].
      eapply exec_Sifthenelse with(v1:=value)(b:=false); [exact EVAL|exact BOOL|constructor].
    + exact(ncs_stability_physical_public RECEIPT).
    + exists false; exists value; split; assumption.
    + exists false; exact FLAG.
    + exact(ncs_stability_physical_source RECEIPT).
    + intro SUCCESS; rewrite FLAG in SUCCESS; discriminate.
Qed.
End EXECUTION.

Print Assumptions ncs_stability_canonical_at_guard_exit.
Print Assumptions ncs_stability_multi_execution.
