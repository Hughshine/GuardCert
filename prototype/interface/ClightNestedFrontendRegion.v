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
  ClightConstantBoundModel ClightNestedExpressionCapture.
Set Implicit Arguments.

Definition ncs_frontend_literal shape := Ssequence(Ssequence Sskip(rectangle_reset(ncs_iterator shape)))
  (strict_frontend_loop(ncs_iterator shape)(signed_expression_test(ncs_iterator shape)
    (Econst_int(Integers.Int.repr(ncs_upper shape))Ctypes.type_int32s))(ncs_leaf shape)).
Definition ncs_frontend_child shape := Ssequence(Ssequence Sskip(rectangle_reset(ncs_column shape)))
  (strict_frontend_loop(ncs_column shape)(signed_expression_test(ncs_column shape)
    (signed_indexed_offset(ncs_pointer shape)(ncs_index shape)(ncs_child_delta shape)))(ncs_frontend_literal shape)).
Definition ncs_frontend_source(indexed:bool)shape := strict_frontend_loop(ncs_row shape)
  (signed_expression_test(ncs_row shape)(if indexed then signed_indexed_offset(ncs_pointer shape)Integers.Int.zero(ncs_delta shape)
    else signed_load_offset(ncs_pointer shape)(ncs_delta shape)))(ncs_frontend_child shape).

Lemma ncs_frontend_literal_equivalent shape : statement_execution_equivalent(ncs_frontend_literal shape)
  (constant_body_source(ncs_iterator shape)(Integers.Int.repr(ncs_upper shape))(ncs_leaf shape)).
Proof. unfold ncs_frontend_literal,constant_body_source; apply statement_sequence_equivalent;
  [apply statement_skip_prefix_equivalent|unfold statement_execution_equivalent; intros; reflexivity]. Qed.

Lemma ncs_frontend_child_equivalent shape : statement_execution_equivalent(ncs_frontend_child shape)
  (nested_expression_body(ncs_column shape)(signed_indexed_offset(ncs_pointer shape)(ncs_index shape)(ncs_child_delta shape))
    (constant_body_source(ncs_iterator shape)(Integers.Int.repr(ncs_upper shape))(ncs_leaf shape))).
Proof. unfold ncs_frontend_child,nested_expression_body; apply statement_sequence_equivalent;
  [apply statement_skip_prefix_equivalent|apply statement_strict_body_equivalent,ncs_frontend_literal_equivalent]. Qed.

Lemma ncs_frontend_execution_equivalent indexed fe ge locals temps memory shape trace after final outcome :
  exec_stmt fe ge locals temps memory(ncs_frontend_source indexed shape)trace after final outcome <->
  exec_stmt fe ge locals temps memory(ncs_original shape)trace after final outcome.
Proof.
  assert(BODY:=statement_strict_body_equivalent(ncs_row shape)
    (signed_expression_test(ncs_row shape)(if indexed then signed_indexed_offset(ncs_pointer shape)Integers.Int.zero(ncs_delta shape)
      else signed_load_offset(ncs_pointer shape)(ncs_delta shape)))(ncs_frontend_child_equivalent shape)).
  unfold ncs_frontend_source; rewrite(BODY fe ge locals temps memory trace after final outcome);
    destruct indexed; [apply ncs_zero_index_execution_equivalent|reflexivity].
Qed.

Lemma ncs_frontend_temps indexed shape : statement_temps(ncs_frontend_source indexed shape)=statement_temps(ncs_original shape).
Proof.
  unfold ncs_frontend_source,ncs_frontend_child,ncs_frontend_literal,ncs_original,nested_expression_source,
    nested_expression_body,constant_body_source,strict_frontend_loop,signed_expression_test;
    destruct indexed; cbn [statement_temps expression_temps]; repeat rewrite List.app_nil_r;
    [pose proof(ncs_zero_index_temps shape) as SAME; exact SAME|reflexivity].
Qed.

Theorem ncs_frontend_region_contract indexed parameters live allocated proposal shape
  (site:ncs_multi_site(ncs_original shape)parameters live allocated proposal shape) candidate pool code
  (VALIDATOR:memory_bounded_source_certificate(affine_package_validator_bounds proposal)
    (affine_multi_source_loop(ncs_multi_package site))(affine_package_context parameters proposal)candidate)
  (COMPILE:compile_window_multi_pointer_buffer_loop(affine_proposed_pointers proposal)
    (affine_package_context parameters proposal)(affine_package_encoder_bounds proposal)
    (ncs_ports(ncs_original shape)parameters live shape)pool candidate=Some code) :
  PrivateRegion.projected_region_contract live(ncs_frontend_source indexed shape)
    (materialized_select(ncs_multi_test site)(affine_multi_candidate_code proposal code)(ncs_frontend_source indexed shape)).
Proof.
  intros temps p locals le current memory after final SCOPE AGREE SOURCE fn continuation.
  assert(NORMAL_SCOPE:statement_scope live(ncs_original shape)).
  { unfold statement_scope in *; rewrite ncs_frontend_temps in SCOPE; exact SCOPE. }
  apply(proj1(@ncs_frontend_execution_equivalent indexed(adapter_entry temps)(globalenv p)locals le memory shape
    E0 after final Out_normal)) in SOURCE.
  destruct(@structured_execution_temp_transport(adapter_entry temps)(globalenv p)locals le memory(ncs_original shape)
    E0 after final Out_normal SOURCE live current(statement_temps(ncs_original shape))
    (@check_plan_frameable_writes _(ncs_frameable(ncs_multi_original site))) NORMAL_SCOPE AGREE)
    as [middle [EXEC FRAME]].
  assert(DOMAIN:materialized_source_completion(ncs_original shape)(Entry(globalenv p)locals current memory)).
  { exists(adapter_entry temps),middle,final; exact EXEC. }
  assert(ORIGINAL:runs(materialized_host(adapter_entry temps)(scan_public_observe live))(ncs_original shape)
    (Entry(globalenv p)locals current memory)(after,final)).
  { exists(FragmentObservation E0 middle final Out_normal); split; [exact EXEC|].
    split; [reflexivity|split; [reflexivity|split; [exact FRAME|apply memory_equivalent_refl]]]. }
  destruct(@ncs_multi_guarded_preservation(ncs_original shape)parameters live allocated proposal shape site candidate pool code
    VALIDATOR COMPILE(adapter_entry temps) _ _ DOMAIN ORIGINAL) as [raw [RUN [TRACE [OUTCOME [PUBLIC MEMORY]]]]].
  unfold clight_fragment_run in RUN; cbn [entry_ge entry_env entry_temps entry_memory] in RUN.
  rewrite TRACE,OUTCOME in RUN.
  apply(proj1(@materialized_select_execution_exact _ _ _ _ _ _ _ _ _ _ _ _)) in RUN.
  destruct RUN as [accepted [checked [CHECK [TEST BRANCH]]]].
  assert(TARGET:exec_stmt(adapter_entry temps)(globalenv p)locals current memory
    (materialized_select(ncs_multi_test site)(affine_multi_candidate_code proposal code)(ncs_frontend_source indexed shape))
    E0(fragment_temps raw)(fragment_memory raw)Out_normal).
  { apply(proj2(@materialized_select_execution_exact _ _ _ _ _ _ _ _ _ _ _ _));
      exists accepted,checked; split; [exact CHECK|split; [exact TEST|]].
    destruct accepted; [exact BRANCH|].
    apply(proj2(@ncs_frontend_execution_equivalent indexed _ _ _ _ _ _ _ _ _ _)); exact BRANCH. }
  destruct(exec_stmt_steps(adapter_entry temps)p _ _ _ _ _ _ _ _ TARGET fn continuation) as [finish [STEPS EXIT]].
  inversion EXIT; subst finish; exists(fragment_temps raw),(fragment_memory raw); auto.
Qed.

Print Assumptions ncs_frontend_execution_equivalent.
Print Assumptions ncs_frontend_literal_equivalent.
Print Assumptions ncs_frontend_child_equivalent.
Print Assumptions ncs_frontend_temps.
Print Assumptions ncs_frontend_region_contract.
