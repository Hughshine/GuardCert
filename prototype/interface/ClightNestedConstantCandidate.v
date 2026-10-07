From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryBoundedSourceChecker GuardMemoryWindowBackend.
From GuardAffineNest Require Import AffineNestSyntax AffineNestGuardPackage AffineNestPackageDecode AffineNestPackageRanges
  AffineNestMultiStaticPackage AffineNestMultiPresumption AffineNestMultiCandidateLocal.
From GuardInterface Require Import ClightNestedConstantSite ClightNestedConstantMultiSite ClightNestedConstantMultiExecution
  ClightPrivateScanHost.
Import ListNotations.
Set Implicit Arguments.

Section CANDIDATE.
Variables source : statement.
Variables parameters live allocated : list ident.
Variable proposal : affine_guard_proposal.
Variable shape : nested_constant_shape.
Variable site : ncs_multi_site source parameters live allocated proposal shape.
Let package:=ncs_multi_package site.
Let ports:=ncs_ports source parameters live shape.
Let scope:=ncs_scope source live.
Variable candidate : L.stmt.
Variable pool : list(ident*ident).
Variable code : statement.
Hypothesis VALIDATOR : memory_bounded_source_certificate(affine_package_validator_bounds proposal)
  (affine_multi_source_loop package)(affine_package_context parameters proposal) candidate.
Hypothesis COMPILE : compile_window_multi_pointer_buffer_loop(affine_proposed_pointers proposal)
  (affine_package_context parameters proposal)(affine_package_encoder_bounds proposal) ports pool candidate=Some code.

Lemma ncs_candidate_frame_context reference current : temp_agree ports reference current ->
  temp_agree(affine_package_context parameters proposal++affine_proposed_pointers proposal++ports) reference current.
Proof.
  intros FRAME identifier MEMBER; apply FRAME.
  repeat rewrite in_app_iff in MEMBER; destruct MEMBER as [CONTEXT|[POINTER|PORT]].
  - unfold affine_package_context in CONTEXT; apply in_app_iff in CONTEXT as [PARAMETER|ROOT].
    + apply(affine_multi_parameters_public package); exact PARAMETER.
    + cbn [List.In] in ROOT; destruct ROOT as [SAME|[]]; subst identifier; exact(affine_multi_root_public package).
  - apply(affine_multi_pointer_public package); exact POINTER.
  - exact PORT.
Qed.

Theorem ncs_candidate_reference_local fe ge locals reference checked memory source_after final :
  temp_agree ports reference checked ->
  affine_multi_guard_flag parameters proposal(Entry ge locals reference memory)=true ->
  exec_stmt fe ge locals reference memory(ncs_model shape) E0 source_after final Out_normal -> exists after,
    exec_stmt fe ge locals checked memory(affine_multi_candidate_code proposal code) E0 after final Out_normal /\
    temp_agree ports source_after after.
Proof.
  intros FRAME ALIAS MODEL.
  destruct(@affine_multi_candidate_local(ncs_model shape) parameters ports proposal allocated package
    (affine_multi_source_loop package) candidate pool code(affine_multi_pointer_private package)
    (affine_multi_window_low package)(affine_multi_window_high package)
    (affine_multi_source_lower package)(affine_multi_shadow_scope package) VALIDATOR COMPILE
    fe ge locals reference checked memory source_after final(ncs_candidate_frame_context FRAME) ALIAS MODEL)
    as [after [RUN EXIT]].
  exists after; split; assumption.
Qed.

Theorem ncs_candidate_at_guard_exit fe ge locals original memory original_after final checked
  (receipt:ncs_multi_receipt site fe ge locals original memory original_after final checked) :
  checked!(affine_proposed_result proposal)=Some(GuardMemoryBooleanScan.memory_boolean_word true) -> exists after,
    exec_stmt fe ge locals checked memory(affine_multi_candidate_code proposal code) E0 after final Out_normal /\
    temp_agree scope original_after after.
Proof.
  intro ACCEPT.
  destruct(ncs_multi_accept receipt ACCEPT) as [reference [source_after [FRAME [ALIAS [MODEL PUBLIC]]]]].
  destruct(ncs_candidate_reference_local FRAME ALIAS MODEL) as [after [RUN EXIT]].
  exists after; split; [exact RUN|].
  eapply temp_agree_trans; [exact PUBLIC|].
  eapply temp_agree_weaken; [apply ClightNestedConstantPhysicalGuard.ncs_scope_scan_ports|exact EXIT].
Qed.
End CANDIDATE.

Print Assumptions ncs_candidate_frame_context.
Print Assumptions ncs_candidate_reference_local.
Print Assumptions ncs_candidate_at_guard_exit.
