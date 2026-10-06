From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep Ctypes.
From Guard Require Import ClightGuard ClightCondition ClightPrivateRegion ClightTempFrame
  ClightTempFootprint ClightRegionProgress CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryBoundedSourceChecker
  GuardMemoryWindowBackend.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestSourceShape AffineNestSourceDecode
  AffineNestLeafModel AffineNestGuardPackage AffineNestPackageGuard
  AffineNestPackageDecode AffineNestPackageRanges AffineNestDomainGuard AffineNestShadowExit
  AffineNestStaticPackage AffineNestCandidateLocal AffineNestMultiStaticPackage
  AffineNestMultiPresumption AffineNestMultiGuardExecution AffineNestMultiCandidateLocal.
From GuardInterface Require Import GuardInterface ClightMaterializedCheck
  ClightMaterializedCertificate ClightMaterializedPreservation
  ClightPrivateScanHost ClightPrivateScanPreservation.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma affine_materialized_source_quiet source parameters live proposal
  (package : affine_guard_package source parameters live proposal) : quiet_statement source=true.
Proof.
  pose proof (affine_package_nest package) as NEST.
  pose proof (described_affine_source (affine_package_description package)) as EXACT; rewrite NEST in EXACT.
  pose proof (described_affine_shapes (affine_package_description package)) as SHAPES; rewrite NEST in SHAPES.
  rewrite EXACT; apply affine_nest_source_quiet; [exact SHAPES|exact (affine_leaf_quiet (affine_package_leaf package))].
Qed.

Lemma affine_materialized_source_writes source parameters live proposal
  (package : affine_guard_package source parameters live proposal) :
  writes_only (affine_nest_controls (affine_proposal_nest proposal)) source.
Proof.
  pose proof (affine_package_nest package) as NEST.
  pose proof (described_affine_source (affine_package_description package)) as EXACT; rewrite NEST in EXACT.
  pose proof (described_affine_shapes (affine_package_description package)) as SHAPES; rewrite NEST in SHAPES.
  rewrite EXACT; apply affine_nest_source_writes; [exact SHAPES|exact (affine_leaf_writes (affine_package_leaf package))].
Qed.

Definition affine_single_materialized_ports parameters proposal live :=
  parameters++[affine_proposed_iterator proposal; affine_proposed_bound proposal]++live.

Definition affine_single_materialized_certificate source parameters live proposal
  (package : affine_guard_package source parameters live proposal) test
  (BODY : materialized_body test=affine_package_guard_code package)
  (COND : materialized_condition test=Etempvar (affine_proposed_result proposal) type_int32s) temps :
  guard_certificate (materialized_host (adapter_entry temps) (scan_public_observe live))
    (materialized_source_completion source) (fun entry => affine_package_guard_flag parameters proposal entry=true)
    (private_scan_entry_frame (affine_single_materialized_ports parameters proposal live))
    (private_scan_entry_frame (affine_single_materialized_ports parameters proposal live)) test.
Proof.
  apply materialized_execution_certificate; intros [ge locals le memory] DOMAIN.
  destruct (@materialized_source_receipt (adapter_entry temps) source _
    (affine_materialized_source_quiet package) DOMAIN) as [after [final SOURCE]].
  destruct (@affine_package_guard_execution source parameters live proposal package (adapter_entry temps)
    ge locals le memory after final SOURCE) as [checked [RUN [FRAME [RESULT _]]]].
  destruct (@affine_probe_result_test (affine_proposed_result proposal)
    (affine_package_guard_flag parameters proposal (Entry ge locals le memory)) ge locals checked memory RESULT)
    as [value [EVAL BOOL]].
  exists (affine_package_guard_flag parameters proposal (Entry ge locals le memory)),checked.
  rewrite BODY,COND; cbn [entry_ge entry_env entry_temps entry_memory].
  split; [exact RUN|split; [exists value; auto|split; [exact FRAME|auto]]].
Defined.

Definition affine_multi_materialized_certificate source parameters live allocated proposal
  (package : affine_multi_static_package source parameters live allocated proposal) test
  (BODY : materialized_body test=affine_multi_guard_code package)
  (COND : materialized_condition test=Etempvar (affine_proposed_result proposal) type_int32s) temps :
  guard_certificate (materialized_host (adapter_entry temps) (scan_public_observe live))
    (materialized_source_completion source) (fun entry => affine_multi_guard_flag parameters proposal entry=true)
    (private_scan_entry_frame live) (private_scan_entry_frame live) test.
Proof.
  apply materialized_execution_certificate; intros [ge locals le memory] DOMAIN.
  destruct (@materialized_source_receipt (adapter_entry temps) source _
    (affine_materialized_source_quiet (affine_multi_guard package)) DOMAIN) as [after [final SOURCE]].
  destruct (@affine_multi_guard_execution source parameters live allocated proposal package (adapter_entry temps)
    ge locals le memory after final SOURCE) as [checked [RUN [FRAME RESULT]]].
  destruct (@affine_probe_result_test (affine_proposed_result proposal)
    (affine_multi_guard_flag parameters proposal (Entry ge locals le memory)) ge locals checked memory RESULT)
    as [value [EVAL BOOL]].
  exists (affine_multi_guard_flag parameters proposal (Entry ge locals le memory)),checked.
  rewrite BODY,COND; cbn [entry_ge entry_env entry_temps entry_memory].
  split; [exact RUN|split; [exists value; auto|split; [exact FRAME|auto]]].
Defined.

Section SINGLE.
Variables source : statement.
Variables parameters live allocated : list ident.
Variable proposal : affine_guard_proposal.
Variable package : affine_static_package source parameters live allocated proposal.
Variables source_loop candidate : L.stmt.
Variable pool : list (ident*ident).
Variable code : statement.
Variable test : materialized_check.
Hypothesis DESCRIBE : describe_materialized_check (affine_package_guard_code (affine_static_guard package))
  (Etempvar (affine_proposed_result proposal) type_int32s)=Some test.
Hypothesis VALIDATOR : memory_bounded_source_certificate (affine_package_validator_bounds proposal)
  source_loop (affine_package_context parameters proposal) candidate.
Hypothesis LOWER : affine_static_source_loop package=source_loop.
Hypothesis COMPILE : compile_window_multi_pointer_buffer_loop (affine_proposed_pointers proposal)
  (affine_package_context parameters proposal) (affine_package_encoder_bounds proposal) live pool candidate=Some code.

Definition affine_single_materialized_rule : materialized_preserving_rule live source.
Proof.
  refine {| materialized_candidate:=affine_single_candidate_code proposal code;
    materialized_test:=test; materialized_domain:=materialized_source_completion source;
    materialized_premise:=fun entry=>affine_package_guard_flag parameters proposal entry=true;
    materialized_ports:=affine_single_materialized_ports parameters proposal live;
    materialized_writes:=affine_nest_controls (affine_proposal_nest proposal) |}.
  - intros identifier MEMBER; unfold affine_single_materialized_ports; repeat rewrite in_app_iff; auto.
  - exact (affine_materialized_source_writes (affine_static_guard package)).
  - intro temps; destruct (@describe_materialized_check_exact _ _ _ DESCRIBE) as [BODY COND].
    exact (@affine_single_materialized_certificate source parameters live proposal (affine_static_guard package) test BODY COND temps).
  - intros temps p locals le memory current after final SCOPE SOURCE ACCEPT AGREE.
    assert (POINTER_NAMES : forall identifier, In identifier (affine_proposed_pointers proposal) ->
      ~In identifier (affine_nest_mutated (affine_proposal_nest proposal))).
    { intros identifier MEMBER; rewrite (affine_static_single package) in MEMBER; cbn in MEMBER.
      destruct MEMBER as [SAME|BAD]; [subst; exact (affine_static_pointer_private package)|contradiction]. }
    assert (ENTRY : temp_agree (affine_package_context parameters proposal++affine_proposed_pointers proposal++live) le current).
    { intros identifier MEMBER; apply AGREE; unfold affine_single_materialized_ports.
      unfold affine_package_context in MEMBER; repeat rewrite in_app_iff in MEMBER; cbn [List.In] in MEMBER.
      repeat rewrite in_app_iff; cbn [List.In].
      destruct MEMBER as [[PARAMETER|[ITERATOR|BAD]]|[POINTER|PUBLIC_ID]].
      - tauto.
      - tauto.
      - contradiction.
      - right; right; rewrite (affine_static_single package) in POINTER; cbn in POINTER.
        destruct POINTER as [SAME|BAD]; [subst; exact (affine_static_pointer_public package)|contradiction].
      - tauto. }
    destruct (@affine_single_candidate_local source parameters live proposal (affine_static_guard package)
      (affine_static_pointer package) source_loop candidate pool code (affine_static_single package) POINTER_NAMES
      (affine_static_window_low package) (affine_static_window_high package) (affine_static_window_span package)
      (ltac:(rewrite <-LOWER; exact (affine_static_source_lower package))) (affine_static_shadow_scope package)
      VALIDATOR COMPILE (adapter_entry temps) (globalenv p) locals le current memory after final ENTRY ACCEPT SOURCE)
      as [exit [RUN FRAME]].
    exists exit,final; auto using memory_equivalent_refl.
  - intros temps p locals le memory after final SOURCE; exists (adapter_entry temps),after,final; exact SOURCE.
Defined.

Theorem affine_single_materialized_region_sound : PrivateRegion.projected_region_contract live source
  (materialized_select test (affine_single_candidate_code proposal code) source).
Proof. exact (materialized_preserving_region_contract affine_single_materialized_rule). Qed.
End SINGLE.

Section MULTI.
Variables source : statement.
Variables parameters live allocated : list ident.
Variable proposal : affine_guard_proposal.
Variable package : affine_multi_static_package source parameters live allocated proposal.
Variables source_loop candidate : L.stmt.
Variable pool : list (ident*ident).
Variable code : statement.
Variable test : materialized_check.
Hypothesis DESCRIBE : describe_materialized_check (affine_multi_guard_code package)
  (Etempvar (affine_proposed_result proposal) type_int32s)=Some test.
Hypothesis VALIDATOR : memory_bounded_source_certificate (affine_package_validator_bounds proposal)
  source_loop (affine_package_context parameters proposal) candidate.
Hypothesis LOWER : affine_multi_source_loop package=source_loop.
Hypothesis COMPILE : compile_window_multi_pointer_buffer_loop (affine_proposed_pointers proposal)
  (affine_package_context parameters proposal) (affine_package_encoder_bounds proposal) live pool candidate=Some code.

Definition affine_multi_materialized_rule : materialized_preserving_rule live source.
Proof.
  refine {| materialized_candidate:=affine_multi_candidate_code proposal code;
    materialized_test:=test; materialized_domain:=materialized_source_completion source;
    materialized_premise:=fun entry=>affine_multi_guard_flag parameters proposal entry=true;
    materialized_ports:=live; materialized_writes:=affine_nest_controls (affine_proposal_nest proposal) |}.
  - intros identifier MEMBER; exact MEMBER.
  - exact (affine_materialized_source_writes (affine_multi_guard package)).
  - intro temps; destruct (@describe_materialized_check_exact _ _ _ DESCRIBE) as [BODY COND].
    exact (@affine_multi_materialized_certificate source parameters live allocated proposal package test BODY COND temps).
  - intros temps p locals le memory current after final SCOPE SOURCE ACCEPT AGREE.
    assert (ENTRY : temp_agree (affine_package_context parameters proposal++affine_proposed_pointers proposal++live) le current).
    { intros identifier MEMBER; apply AGREE.
      unfold affine_package_context in MEMBER; repeat rewrite in_app_iff in MEMBER; cbn [List.In] in MEMBER.
      destruct MEMBER as [[PARAMETER|[ITERATOR|BAD]]|[POINTER|PUBLIC_ID]].
      - apply (affine_multi_parameters_public package); exact PARAMETER.
      - subst identifier; exact (affine_multi_root_public package).
      - contradiction.
      - apply (affine_multi_pointer_public package); exact POINTER.
      - exact PUBLIC_ID. }
    destruct (@affine_multi_candidate_local source parameters live proposal allocated package source_loop candidate pool code
      (affine_multi_pointer_private package) (affine_multi_window_low package) (affine_multi_window_high package)
      (ltac:(rewrite <-LOWER; exact (affine_multi_source_lower package))) (affine_multi_shadow_scope package)
      VALIDATOR COMPILE (adapter_entry temps) (globalenv p) locals le current memory after final ENTRY ACCEPT SOURCE)
      as [exit [RUN FRAME]].
    exists exit,final; auto using memory_equivalent_refl.
  - intros temps p locals le memory after final SOURCE; exists (adapter_entry temps),after,final; exact SOURCE.
Defined.

Theorem affine_multi_materialized_region_sound : PrivateRegion.projected_region_contract live source
  (materialized_select test (affine_multi_candidate_code proposal code) source).
Proof. exact (materialized_preserving_region_contract affine_multi_materialized_rule). Qed.
End MULTI.

Print Assumptions affine_materialized_source_quiet.
Print Assumptions affine_materialized_source_writes.
Print Assumptions affine_single_materialized_certificate.
Print Assumptions affine_multi_materialized_certificate.
Print Assumptions affine_single_materialized_rule.
Print Assumptions affine_single_materialized_region_sound.
Print Assumptions affine_multi_materialized_rule.
Print Assumptions affine_multi_materialized_region_sound.
