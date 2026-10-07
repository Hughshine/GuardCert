From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryBoundedSourceChecker GuardMemoryWindowBackend.
From GuardAffineNest Require Import AffineNestSyntax AffineNestGuardPackage AffineNestPackageDecode AffineNestPackageRanges
  AffineNestMultiStaticPackage AffineNestMultiPresumption AffineNestMultiCandidateLocal AffineNestMultiCandidatePrefix AffineNestPackageGuard.
From GuardInterface Require Import ClightNestedConstantSite ClightNestedConstantMultiSite ClightNestedConstantMultiExecution
  ClightPrivateScanHost ClightNestedCompactExit.
Import ListNotations.
Set Implicit Arguments.

Definition ncs_compact_candidate_code shape code := Ssequence code(ncs_compact_exit_code shape).

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

Lemma ncs_compact_frame_context reference current : temp_agree ports reference current ->
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

Theorem ncs_compact_reference_local fe ge locals reference checked memory source_after final :
  temp_agree ports reference checked ->
  affine_multi_guard_flag parameters proposal(Entry ge locals reference memory)=true ->
  exec_stmt fe ge locals reference memory(ncs_model shape) E0 source_after final Out_normal -> exists after,
    exec_stmt fe ge locals checked memory(ncs_compact_candidate_code shape code) E0 after final Out_normal /\
    temp_agree ports source_after after.
Proof.
  intros FRAME ALIAS MODEL.
  destruct(@affine_multi_candidate_prefix(ncs_model shape) parameters ports proposal allocated package
    (affine_multi_source_loop package) candidate pool code(affine_multi_pointer_private package)
    (affine_multi_window_low package)(affine_multi_window_high package)
    (affine_multi_source_lower package) VALIDATOR COMPILE
    fe ge locals reference checked memory source_after final(ncs_compact_frame_context FRAME) ALIAS MODEL)
    as [private [PREFIX PUBLIC]].
  assert(NUMERIC:affine_package_guard_flag parameters proposal(Entry ge locals reference memory)=true).
  { unfold affine_multi_guard_flag in ALIAS; apply andb_true_iff in ALIAS; tauto. }
  destruct(@ncs_compact_accepted_inputs source parameters live proposal shape(ncs_multi_original site)
    fe ge locals reference memory source_after final NUMERIC MODEL)
    as [row [root [child [ROW [ROOT [CHILD [ACTIVE CHILD_ACTIVE]]]]]]].
  assert(CACHES:forall cache,In cache(ncs_caches shape) -> private!cache=reference!cache).
  { intros cache MEMBER; apply PUBLIC; unfold ports,ncs_ports; apply in_or_app; left;
      apply(ncs_cache_parameters(ncs_multi_original site)); exact MEMBER. }
  assert(RESTORE:exec_stmt fe ge locals private final(ncs_compact_exit_code shape)
    E0(ncs_compact_exit_temps shape private)final Out_normal).
  { apply ncs_compact_exit_execution with(site:=ncs_multi_original site)(root:=root)(child:=child).
    - rewrite CACHES by(left; reflexivity); exact ROOT.
    - rewrite CACHES by(right; left; reflexivity); exact CHILD. }
  exists(ncs_compact_exit_temps shape private); split.
  - unfold ncs_compact_candidate_code; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); eassumption.
  - rewrite <-(@ncs_compact_source_exit source parameters live proposal shape(ncs_multi_original site)
      fe ge locals reference memory source_after final row root child ROW ROOT CHILD ACTIVE CHILD_ACTIVE MODEL).
    apply ncs_compact_exit_frame with(site:=ncs_multi_original site); exact PUBLIC.
Qed.
End CANDIDATE.
Print Assumptions ncs_compact_reference_local.
