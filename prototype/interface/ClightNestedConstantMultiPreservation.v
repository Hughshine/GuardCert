From Stdlib Require Import List.
From compcert.common Require Import AST Values Memory Events Smallstep.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightPrivateRegion ClightTempFrame ClightTempFootprint
  ClightProjectedExecution CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryBoundedSourceChecker GuardMemoryWindowBackend.
From GuardAffineNest Require Import AffineNestSyntax AffineNestGuardPackage AffineNestPackageDecode AffineNestPackageRanges
  AffineNestMultiStaticPackage AffineNestMultiCandidateLocal.
From GuardInterface Require Import GuardInterface ClightReadonlyRewrite ClightMaterializedCheck
  ClightMaterializedCertificate ClightPrivateScanHost ClightPrivateScanPreservation ClightCheckPlanFrame
  ClightNestedConstantSite ClightNestedConstantMultiSite ClightNestedConstantCandidate
  ClightNestedConstantMultiCertificate.
Import ListNotations.
Set Implicit Arguments.

Lemma ncs_scope_live source live : incl live(ncs_scope source live).
Proof. intros identifier MEMBER; unfold ncs_scope; apply in_or_app; right; exact MEMBER. Qed.

Section PRESERVATION.
Variable source : statement.
Variables parameters live allocated : list ident.
Variable proposal : affine_guard_proposal.
Variable shape : nested_constant_shape.
Variable site : ncs_multi_site source parameters live allocated proposal shape.
Variable candidate : L.stmt.
Variable pool : list(ident*ident).
Variable code : statement.
Hypothesis VALIDATOR : memory_bounded_source_certificate(affine_package_validator_bounds proposal)
  (affine_multi_source_loop(ncs_multi_package site))(affine_package_context parameters proposal) candidate.
Hypothesis COMPILE : compile_window_multi_pointer_buffer_loop(affine_proposed_pointers proposal)
  (affine_package_context parameters proposal)(affine_package_encoder_bounds proposal)
  (ncs_ports source parameters live shape) pool candidate=Some code.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Let host:=materialized_host fe(scan_public_observe live).
Let scope:=ncs_scope source live.

Definition ncs_multi_local_certificate :
  preservation_certificate host(materialized_source_completion source)
    (ncs_candidate_presumption source parameters live proposal shape fe)
    (ncs_accepted_entry source parameters live proposal shape fe)(private_scan_entry_frame scope)
    eq source(affine_multi_candidate_code proposal code) source.
Proof.
  constructor.
  - intros entry checked original DOMAIN PREMISE [ENTRY [reference [ANCHOR CHECKED]]]
      [raw [RUN [TRACE [OUTCOME [PUBLIC MEMORY]]]]].
    destruct ENTRY as [GE [ENV [MEM FRAME]]].
    destruct ANCHOR as [REF_GE [REF_ENV [REF_MEM [ALIAS MODEL]]]].
    destruct CHECKED as [_ [_ [_ PORTS]]].
    destruct entry as [ge locals temps memory],checked as [current_ge current_locals current current_memory],
      reference as [ref_ge ref_locals ref_temps ref_memory].
    cbn [entry_ge entry_env entry_memory entry_temps] in *.
    subst current_ge current_locals current_memory ref_ge ref_locals ref_memory.
    unfold clight_fragment_run in RUN; cbn [entry_ge entry_env entry_memory entry_temps] in RUN.
    rewrite TRACE,OUTCOME in RUN.
    destruct(MODEL _ _ RUN) as [model_after [MODEL_RUN MODEL_PUBLIC]].
    destruct(@ncs_candidate_reference_local source parameters live allocated proposal shape site candidate pool code
      VALIDATOR COMPILE fe ge locals ref_temps current memory model_after(fragment_memory raw)
      PORTS ALIAS MODEL_RUN) as [after [EXEC EXIT]].
    exists original; split; [|reflexivity].
    exists(FragmentObservation E0 after(fragment_memory raw) Out_normal); split; [exact EXEC|].
    split; [reflexivity|split; [reflexivity|split; [|exact MEMORY]]].
    eapply temp_agree_trans; [exact PUBLIC|].
    eapply temp_agree_trans.
    + eapply temp_agree_weaken; [apply ncs_scope_live|exact MODEL_PUBLIC].
    + eapply temp_agree_weaken; [|exact EXIT].
      intros identifier MEMBER; apply ClightNestedConstantPhysicalGuard.ncs_scope_scan_ports,ncs_scope_live; exact MEMBER.
  - intros entry checked original DOMAIN ENTRY [raw [RUN [TRACE [OUTCOME [PUBLIC MEMORY]]]]].
    destruct ENTRY as [GE [ENV [MEM FRAME]]].
    destruct entry as [ge locals temps memory],checked as [current_ge current_locals current current_memory].
    cbn [entry_ge entry_env entry_memory entry_temps] in *; subst current_ge current_locals current_memory.
    unfold clight_fragment_run in RUN; cbn [entry_ge entry_env entry_memory entry_temps] in RUN.
    rewrite TRACE,OUTCOME in RUN.
    destruct(@structured_execution_temp_transport fe ge locals temps memory source E0(fragment_temps raw)
      (fragment_memory raw) Out_normal RUN scope current(statement_temps source)
      (@check_plan_frameable_writes source(ncs_frameable(ncs_multi_original site)))
      ltac:(unfold statement_scope,scope,ncs_scope; intros identifier MEMBER; apply in_or_app; left; exact MEMBER) FRAME)
      as [after [EXEC EXIT]].
    exists original; split; [|reflexivity].
    exists(FragmentObservation E0 after(fragment_memory raw) Out_normal); split; [exact EXEC|].
    split; [reflexivity|split; [reflexivity|split; [|exact MEMORY]]].
    eapply temp_agree_trans; [exact PUBLIC|].
    eapply temp_agree_weaken; [apply ncs_scope_live|exact EXIT].
Defined.

Theorem ncs_multi_guarded_preservation entry original :
  materialized_source_completion source entry -> runs host source entry original ->
  runs host(materialized_select(ncs_multi_test site)(affine_multi_candidate_code proposal code)source) entry original.
Proof.
  intros DOMAIN SOURCE.
  destruct(@guardify_preservation _ host(materialized_source_completion source)
    (ncs_candidate_presumption source parameters live proposal shape fe)
    (ncs_accepted_entry source parameters live proposal shape fe)(private_scan_entry_frame scope)
    eq source(affine_multi_candidate_code proposal code)source(ncs_multi_test site)
    (ncs_multi_guard_certificate site fe(scan_public_observe live))ncs_multi_local_certificate
    entry original DOMAIN SOURCE) as [target [RUN SAME]].
  subst target; exact RUN.
Qed.
End PRESERVATION.

Theorem ncs_multi_region_contract source parameters live allocated proposal shape
  (site:ncs_multi_site source parameters live allocated proposal shape) candidate pool code
  (VALIDATOR:memory_bounded_source_certificate(affine_package_validator_bounds proposal)
    (affine_multi_source_loop(ncs_multi_package site))(affine_package_context parameters proposal) candidate)
  (COMPILE:compile_window_multi_pointer_buffer_loop(affine_proposed_pointers proposal)
    (affine_package_context parameters proposal)(affine_package_encoder_bounds proposal)
    (ncs_ports source parameters live shape)pool candidate=Some code) :
  PrivateRegion.projected_region_contract live source
    (materialized_select(ncs_multi_test site)(affine_multi_candidate_code proposal code)source).
Proof.
  intros temps p locals le current memory after final SCOPE AGREE SOURCE fn continuation.
  destruct(@structured_execution_temp_transport(adapter_entry temps)(globalenv p)locals le memory source
    E0 after final Out_normal SOURCE live current(statement_temps source)
    (@check_plan_frameable_writes source(ncs_frameable(ncs_multi_original site))) SCOPE AGREE)
    as [middle [EXEC FRAME]].
  assert(DOMAIN:materialized_source_completion source(Entry(globalenv p)locals current memory)).
  { exists(adapter_entry temps),middle,final; exact EXEC. }
  assert(ORIGINAL:runs(materialized_host(adapter_entry temps)(scan_public_observe live))source
    (Entry(globalenv p)locals current memory)(after,final)).
  { exists(FragmentObservation E0 middle final Out_normal); split; [exact EXEC|].
    split; [reflexivity|split; [reflexivity|split; [exact FRAME|apply memory_equivalent_refl]]]. }
  destruct(@ncs_multi_guarded_preservation source parameters live allocated proposal shape site candidate pool code
    VALIDATOR COMPILE(adapter_entry temps) _ _ DOMAIN ORIGINAL) as [raw [RUN [TRACE [OUTCOME [PUBLIC MEMORY]]]]].
  unfold clight_fragment_run in RUN; cbn [entry_ge entry_env entry_temps entry_memory] in RUN.
  rewrite TRACE,OUTCOME in RUN.
  destruct(exec_stmt_steps(adapter_entry temps)p _ _ _ _ _ _ _ _ RUN fn continuation) as [finish [STEPS EXIT]].
  inversion EXIT; subst finish; exists(fragment_temps raw),(fragment_memory raw); auto.
Qed.

Print Assumptions ncs_scope_live.
Print Assumptions ncs_multi_local_certificate.
Print Assumptions ncs_multi_guarded_preservation.
Print Assumptions ncs_multi_region_contract.
