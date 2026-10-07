From Stdlib Require Import List Bool.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightPrivateRegion ClightTempFrame ClightTempFootprint
  ClightProjectedExecution CompCertMemoryEquivalence ClightRectangularLoops.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryBoundedSourceChecker GuardMemoryWindowBackend.
From GuardAffineNest Require Import AffineNestGuardPackage AffineNestPackageDecode AffineNestPackageRanges
  AffineNestMultiStaticPackage AffineNestMultiCandidateLocal.
From GuardInterface Require Import GuardInterface ClightReadonlyRewrite ClightMaterializedCheck ClightMaterializedCertificate
  ClightPrivateScanPreservation ClightCheckPlanFrame ClightNestedConstantSite ClightNestedConstantMultiSite
  ClightNestedConstantMultiPreservation ClightZeroIndexHeader ClightExecutionCongruence ClightStrictLoopProgress
  ClightSignedExpressionProgress ClightSignedIndexedOffsetHeader ClightLoadedOffsetHeader
  ClightConstantBoundModel ClightNestedExpressionCapture ClightNestedFrontendRegion
  ClightNestedInvariantCertificate ClightNestedConstantMultiCertificate ClightPrivateScanHost ClightNestedCompactCandidate ClightNestedCompactCertificate.
Set Implicit Arguments.

Section PRESERVATION.
Variable source : statement.
Variables parameters live allocated : list ident.
Variable proposal : affine_guard_proposal.
Variable shape : nested_constant_shape.
Variable site : ncs_invariant_stability_site source parameters live allocated proposal shape.
Variable candidate : L.stmt.
Variable pool : list(ident*ident).
Variable code : statement.
Hypothesis VALIDATOR : memory_bounded_source_certificate(affine_package_validator_bounds proposal)
  (affine_multi_source_loop(ncs_multi_package(ncs_invariant_stability_core site)))(affine_package_context parameters proposal) candidate.
Hypothesis COMPILE : compile_window_multi_pointer_buffer_loop(affine_proposed_pointers proposal)
  (affine_package_context parameters proposal)(affine_package_encoder_bounds proposal)
  (ncs_ports source parameters live shape) pool candidate=Some code.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Let host:=materialized_host fe(scan_public_observe live).
Let scope:=ncs_scope source live.

(** The new guard discharges the same candidate presumption and entry
    relation. The compact candidate and language installation host are reused. *)
Theorem ncs_invariant_guarded_preservation entry original :
  materialized_source_completion source entry -> runs host source entry original ->
  runs host(materialized_select(ncs_invariant_stability_test site)(ncs_compact_candidate_code shape code)source) entry original.
Proof.
  intros DOMAIN SOURCE.
  destruct(@guardify_preservation _ host(materialized_source_completion source)
    (ncs_candidate_presumption source parameters live proposal shape fe)
    (ncs_accepted_entry source parameters live proposal shape fe)(private_scan_entry_frame scope)
    eq source(ncs_compact_candidate_code shape code)source(ncs_invariant_stability_test site)
    (ncs_invariant_stability_guard_certificate site fe(scan_public_observe live))
    (@ncs_compact_local_certificate source parameters live allocated proposal shape(ncs_invariant_stability_core site)
      candidate pool code VALIDATOR COMPILE fe)
    entry original DOMAIN SOURCE) as [target [RUN SAME]].
  subst target; exact RUN.
Qed.
End PRESERVATION.

Theorem ncs_invariant_frontend_region_contract indexed parameters live allocated proposal shape
  (site:ncs_invariant_stability_site(ncs_original shape)parameters live allocated proposal shape) candidate pool code
  (VALIDATOR:memory_bounded_source_certificate(affine_package_validator_bounds proposal)
    (affine_multi_source_loop(ncs_multi_package(ncs_invariant_stability_core site)))(affine_package_context parameters proposal)candidate)
  (COMPILE:compile_window_multi_pointer_buffer_loop(affine_proposed_pointers proposal)
    (affine_package_context parameters proposal)(affine_package_encoder_bounds proposal)
    (ncs_ports(ncs_original shape)parameters live shape)pool candidate=Some code) :
  PrivateRegion.projected_region_contract live(ncs_frontend_source indexed shape)
    (materialized_select(ncs_invariant_stability_test site)(ncs_compact_candidate_code shape code)(ncs_frontend_source indexed shape)).
Proof.
  intros temps p locals le current memory after final SCOPE AGREE SOURCE fn continuation.
  assert(NORMAL_SCOPE:statement_scope live(ncs_original shape)).
  { unfold statement_scope in *; rewrite ncs_frontend_temps in SCOPE; exact SCOPE. }
  apply(proj1(@ncs_frontend_execution_equivalent indexed(adapter_entry temps)(globalenv p)locals le memory shape
    E0 after final Out_normal)) in SOURCE.
  destruct(@structured_execution_temp_transport(adapter_entry temps)(globalenv p)locals le memory(ncs_original shape)
    E0 after final Out_normal SOURCE live current(statement_temps(ncs_original shape))
    (@check_plan_frameable_writes _(ncs_frameable(ncs_multi_original(ncs_invariant_stability_core site)))) NORMAL_SCOPE AGREE)
    as [middle [EXEC FRAME]].
  assert(DOMAIN:materialized_source_completion(ncs_original shape)(Entry(globalenv p)locals current memory)).
  { exists(adapter_entry temps),middle,final; exact EXEC. }
  assert(ORIGINAL:runs(materialized_host(adapter_entry temps)(scan_public_observe live))(ncs_original shape)
    (Entry(globalenv p)locals current memory)(after,final)).
  { exists(FragmentObservation E0 middle final Out_normal); split; [exact EXEC|].
    split; [reflexivity|split; [reflexivity|split; [exact FRAME|apply memory_equivalent_refl]]]. }
  destruct(@ncs_invariant_guarded_preservation(ncs_original shape)parameters live allocated proposal shape site candidate pool code
    VALIDATOR COMPILE(adapter_entry temps) _ _ DOMAIN ORIGINAL) as [raw [RUN [TRACE [OUTCOME [PUBLIC MEMORY]]]]].
  unfold clight_fragment_run in RUN; cbn [entry_ge entry_env entry_temps entry_memory] in RUN.
  rewrite TRACE,OUTCOME in RUN.
  apply(proj1(@materialized_select_execution_exact _ _ _ _ _ _ _ _ _ _ _ _)) in RUN.
  destruct RUN as [accepted [checked [CHECK [TEST BRANCH]]]].
  assert(TARGET:exec_stmt(adapter_entry temps)(globalenv p)locals current memory
    (materialized_select(ncs_invariant_stability_test site)(ncs_compact_candidate_code shape code)(ncs_frontend_source indexed shape))
    E0(fragment_temps raw)(fragment_memory raw)Out_normal).
  { apply(proj2(@materialized_select_execution_exact _ _ _ _ _ _ _ _ _ _ _ _));
      exists accepted,checked; split; [exact CHECK|split; [exact TEST|]].
    destruct accepted; [exact BRANCH|].
    apply(proj2(@ncs_frontend_execution_equivalent indexed _ _ _ _ _ _ _ _ _ _)); exact BRANCH. }
  destruct(exec_stmt_steps(adapter_entry temps)p _ _ _ _ _ _ _ _ TARGET fn continuation) as [finish [STEPS EXIT]].
  inversion EXIT; subst finish; exists(fragment_temps raw),(fragment_memory raw); auto.
Qed.

Print Assumptions ncs_invariant_guarded_preservation.
Print Assumptions ncs_invariant_frontend_region_contract.
