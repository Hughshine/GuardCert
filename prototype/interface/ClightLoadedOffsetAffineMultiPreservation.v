From Stdlib Require Import List.
From compcert.common Require Import AST Values Memory Events Smallstep.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightPrivateRegion ClightTempFrame
  ClightTempFootprint ClightProjectedExecution CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryBoundedSourceChecker GuardMemoryWindowBackend.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestGuardPackage AffineNestPackageRanges AffineNestPackageDecode
  AffineNestMultiStaticPackage AffineNestMultiCandidateLocal.
From GuardInterface Require Import GuardInterface ClightReadonlyRewrite ClightMaterializedCheck ClightMaterializedCertificate
  ClightPrivateScanHost ClightPrivateScanPreservation ClightCheckPlanFrame ClightLoadedAffineNumericSite
  ClightLoadedAffineScanSite ClightLoadedAffineScanExecution ClightLoadedAffineScanTransfer
  ClightLoadedAffineCandidate ClightLoadedAffineMultiGuard ClightExpressionAffineNumericSite
  ClightLoadedOffsetAffineScanSite ClightLoadedOffsetAffineScanExecution ClightLoadedOffsetAffineScanTransfer
  ClightLoadedOffsetAffineCandidate ClightLoadedOffsetAffineMultiGuard.
Set Implicit Arguments.

Lemma offset_affine_scan_entry_public source parameters live proposal pointer delta
  (site : offset_affine_transfer_site source parameters live proposal pointer delta) original checked :
  offset_affine_scan_entry_relation parameters live proposal pointer delta original checked ->
  private_scan_entry_frame live original checked.
Proof.
  intros [upper [_ [GE [ENV [MEMORY FRAME]]]]].
  repeat split; try assumption.
  eapply temp_agree_trans.
  - apply temp_agree_set; intros MEMBER.
    apply(expression_numeric_private(offset_scan_numeric(offset_transfer_scan site))),in_or_app; right; exact MEMBER.
  - eapply temp_agree_weaken; [|exact FRAME].
    intros identifier MEMBER; apply(proj2(loaded_affine_scan_ports_inclusions parameters proposal live));
      right; right; exact MEMBER.
Qed.

Section PRESERVATION.
Variable source : statement.
Variables parameters live allocated : list ident.
Variable proposal : affine_guard_proposal.
Variable pointer : ident.
Variable delta : Integers.Int.int.
Variable site : offset_affine_multi_site source parameters live allocated proposal pointer delta.
Variable candidate : L.stmt.
Variable pool : list(ident*ident).
Variable code : statement.
Hypothesis VALIDATOR : memory_bounded_source_certificate(affine_package_validator_bounds proposal)
  (affine_multi_source_loop(offset_multi_package site))(affine_package_context parameters proposal) candidate.
Hypothesis COMPILE : compile_window_multi_pointer_buffer_loop(affine_proposed_pointers proposal)
  (affine_package_context parameters proposal)(affine_package_encoder_bounds proposal)
  (loaded_affine_scan_ports parameters proposal live) pool candidate=Some code.
Hypothesis SCOPE : statement_scope live source.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Let host := materialized_host fe (scan_public_observe live).

Definition offset_affine_multi_local_certificate :
  preservation_certificate host (materialized_source_completion source)
    (offset_affine_candidate_presumption fe parameters live proposal pointer delta)
    (offset_affine_scan_entry_relation parameters live proposal pointer delta)
    (offset_affine_scan_entry_relation parameters live proposal pointer delta)
    eq source (affine_multi_candidate_code proposal code) source.
Proof.
  constructor.
  - intros entry checked original DOMAIN PREMISE ENTRY [raw [RUN [TRACE [OUTCOME [PUBLIC MEMORY]]]]].
    pose proof(offset_affine_scan_entry_public(offset_multi_transfer site) ENTRY) as [GE [ENV [MEM FRAME]]].
    destruct entry as [ge locals le memory],checked as [current_ge current_locals current current_memory].
    cbn [entry_ge entry_env entry_memory entry_temps] in *; subst current_ge current_locals current_memory.
    unfold clight_fragment_run in RUN; cbn [entry_ge entry_env entry_memory entry_temps] in RUN.
    rewrite TRACE,OUTCOME in RUN.
    destruct(@offset_affine_candidate_local source parameters live allocated proposal pointer delta
      (offset_transfer_scan(offset_multi_transfer site))(offset_multi_package site)(offset_multi_cached_scope site)
      candidate pool code VALIDATOR COMPILE fe ge locals le memory current (fragment_temps raw)(fragment_memory raw)
      PREMISE ENTRY RUN) as [after [EXEC EXIT]].
    exists original; split; [|reflexivity].
    exists(FragmentObservation E0 after (fragment_memory raw) Out_normal); split; [exact EXEC|].
    split; [reflexivity|split; [reflexivity|split; [eapply temp_agree_trans; eassumption|exact MEMORY]]].
  - intros entry checked original DOMAIN ENTRY [raw [RUN [TRACE [OUTCOME [PUBLIC MEMORY]]]]].
    pose proof(offset_affine_scan_entry_public(offset_multi_transfer site) ENTRY) as [GE [ENV [MEM FRAME]]].
    destruct entry as [ge locals le memory],checked as [current_ge current_locals current current_memory].
    cbn [entry_ge entry_env entry_memory entry_temps] in *; subst current_ge current_locals current_memory.
    unfold clight_fragment_run in RUN; cbn [entry_ge entry_env entry_memory entry_temps] in RUN.
    rewrite TRACE,OUTCOME in RUN.
    destruct(@structured_execution_temp_transport fe ge locals le memory source E0 (fragment_temps raw)
      (fragment_memory raw) Out_normal RUN live current (statement_temps source)
      (@check_plan_frameable_writes source
        (expression_numeric_frameable(offset_scan_numeric(offset_transfer_scan(offset_multi_transfer site))))) SCOPE FRAME)
      as [after [EXEC EXIT]].
    exists original; split; [|reflexivity].
    exists(FragmentObservation E0 after (fragment_memory raw) Out_normal); split; [exact EXEC|].
    split; [reflexivity|split; [reflexivity|split; [eapply temp_agree_trans; eassumption|exact MEMORY]]].
Defined.

Theorem offset_affine_multi_guarded_preservation entry original :
  materialized_source_completion source entry -> runs host source entry original ->
  runs host (materialized_select(offset_multi_test site)(affine_multi_candidate_code proposal code) source) entry original.
Proof.
  intros DOMAIN SOURCE.
  destruct(@guardify_preservation _ host (materialized_source_completion source)
    (offset_affine_candidate_presumption fe parameters live proposal pointer delta)
    (offset_affine_scan_entry_relation parameters live proposal pointer delta)
    (offset_affine_scan_entry_relation parameters live proposal pointer delta)
    eq source (affine_multi_candidate_code proposal code) source (offset_multi_test site)
    (offset_affine_multi_guard_certificate site fe (scan_public_observe live))
    offset_affine_multi_local_certificate entry original DOMAIN SOURCE) as [target [RUN SAME]].
  subst target; exact RUN.
Qed.
End PRESERVATION.

Theorem offset_affine_multi_region_contract source parameters live allocated proposal pointer delta
  (site : offset_affine_multi_site source parameters live allocated proposal pointer delta) candidate pool code
  (VALIDATOR : memory_bounded_source_certificate(affine_package_validator_bounds proposal)
    (affine_multi_source_loop(offset_multi_package site))(affine_package_context parameters proposal) candidate)
  (COMPILE : compile_window_multi_pointer_buffer_loop(affine_proposed_pointers proposal)
    (affine_package_context parameters proposal)(affine_package_encoder_bounds proposal)
    (loaded_affine_scan_ports parameters proposal live) pool candidate=Some code) :
  PrivateRegion.projected_region_contract live source
    (materialized_select(offset_multi_test site)(affine_multi_candidate_code proposal code) source).
Proof.
  intros temps p locals le current memory after final SCOPE AGREE SOURCE fn continuation.
  destruct(@structured_execution_temp_transport (adapter_entry temps)(globalenv p) locals le memory source
    E0 after final Out_normal SOURCE live current (statement_temps source)
    (@check_plan_frameable_writes source
      (expression_numeric_frameable(offset_scan_numeric(offset_transfer_scan(offset_multi_transfer site))))) SCOPE AGREE)
    as [middle [EXEC FRAME]].
  assert(DOMAIN:materialized_source_completion source(Entry(globalenv p)locals current memory)).
  { exists(adapter_entry temps),middle,final; exact EXEC. }
  assert(ORIGINAL:runs(materialized_host(adapter_entry temps)(scan_public_observe live)) source
    (Entry(globalenv p)locals current memory)(after,final)).
  { exists(FragmentObservation E0 middle final Out_normal); split; [exact EXEC|].
    split; [reflexivity|split; [reflexivity|split; [exact FRAME|apply memory_equivalent_refl]]]. }
  destruct(@offset_affine_multi_guarded_preservation source parameters live allocated proposal pointer delta site
    candidate pool code VALIDATOR COMPILE SCOPE (adapter_entry temps) _ _ DOMAIN ORIGINAL)
    as [raw [RUN [TRACE [OUTCOME [PUBLIC MEMORY]]]]].
  unfold clight_fragment_run in RUN; cbn [entry_ge entry_env entry_temps entry_memory] in RUN.
  rewrite TRACE,OUTCOME in RUN.
  destruct(exec_stmt_steps(adapter_entry temps) p _ _ _ _ _ _ _ _ RUN fn continuation) as [finish [STEPS EXIT]].
  inversion EXIT; subst finish; exists(fragment_temps raw),(fragment_memory raw); auto.
Qed.

Print Assumptions offset_affine_scan_entry_public.
Print Assumptions offset_affine_multi_local_certificate.
Print Assumptions offset_affine_multi_guarded_preservation.
Print Assumptions offset_affine_multi_region_contract.
