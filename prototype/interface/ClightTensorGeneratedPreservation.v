From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Guard Require Import ClightGuard ClightCondition ClightTempFrame ClightTempFootprint
  ClightPrivateRegion ClightRegionProgress CompCertMemoryEquivalence.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite
  ClightPrivateScanHost ClightPrivateScanPreservation ClightLiteralBoundPreparation ClightTensorRegionPackage
  ClightTensorRegionPreservation ClightMaterializedCheck ClightMaterializedCertificate
  ClightMaterializedPreservation ClightSharedGuard ClightStagedCheck ClightCheckPlan ClightCheckPlanFrame.
Import ListNotations.
Set Implicit Arguments.

From GuardInterface Require Import ClightTensorLiteralPreservation ClightTensorGeneratedCandidates.
From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryTensorSource.

(** Reuse the same guard encoding and language host with an actual generated
    candidate and data-only affine/point-space witnesses. *)
Section GENERATED.
Variable live : list ident.
Variable source : statement.
Variable helper : ident.
Variable upper : int.
Variable package : tensor_region_package(literal_tests_prepare helper upper source).
Let tree := tensor_region_guard package.
Let ports := tensor_literal_ports live source helper tree.
Hypothesis FRAMEABLE : check_plan_frameable source=true.
Hypothesis QUIET : quiet_statement source=true.
Hypothesis HELPER_PRIVATE : ~In helper(statement_temps source++live).
Variable result : ident.
Hypothesis RESULT_PRIVATE : ~In result(helper::ports).
Variable test : materialized_check.
Hypothesis TEST_BODY : materialized_body test=tensor_literal_check_body helper upper tree result.
Hypothesis TEST_CONDITION : materialized_condition test=shared_guard_choice result.
Variable pool : list(ident*ident).
Variable proposal : tensor_generated_candidate.
Variable code : statement.
Hypothesis CHECK : CoreAlarmed.Base.mayReturn
  (check_tensor_generated_region package live pool proposal) (Some code).

Theorem tensor_literal_generated_execution fe ge locals le memory after final current :
  exec_stmt fe ge locals le memory source E0 after final Out_normal ->
  tensor_literal_premise source helper upper package(Entry ge locals le memory) -> temp_agree ports le current ->
  exists exit, exec_stmt fe ge locals current memory
    (tensor_literal_candidate helper upper(tensor_region_branch package code)) E0 exit final Out_normal /\
    temp_agree live after exit.
Proof.
  intros SOURCE PREMISE FRAME.
  destruct(@tensor_literal_canonical_source live source helper upper package FRAMEABLE HELPER_PRIVATE
    fe ge locals le memory after final current SOURCE FRAME) as [canonical [CANONICAL PUBLIC]].
  assert(GUARD:decision_run(Entry ge locals(literal_bound_temps helper upper current)memory)tree true).
  { exact(@decision_tree_read_frame tree(tensor_literal_prepared_entry helper upper(Entry ge locals le memory))
      (literal_bound_temps helper upper current)true
      (@tensor_literal_prepared_frame live source helper upper package le current FRAME)PREMISE). }
  destruct(@tensor_region_generated_execution _ package fe ge locals(literal_bound_temps helper upper current)memory
    canonical final live pool proposal code CHECK CANONICAL GUARD) as [exit [CANDIDATE EXIT]].
  exists exit; split.
  - unfold tensor_literal_candidate; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0);
      [apply literal_bound_set_execution|exact CANDIDATE].
  - eapply temp_agree_trans; eassumption.
Qed.

Definition tensor_literal_generated_rule : materialized_preserving_rule live source.
Proof.
  refine {|materialized_candidate:=tensor_literal_candidate helper upper(tensor_region_branch package code);
    materialized_test:=test;materialized_domain:=tensor_literal_domain source;
    materialized_premise:=tensor_literal_premise source helper upper package;
    materialized_ports:=ports;materialized_ports_live:=@tensor_literal_ports_live live source helper upper package;
    materialized_writes:=statement_temps source;materialized_source_writes:=check_plan_frameable_writes source FRAMEABLE;
    materialized_certificate:=@tensor_literal_certificate live source helper upper package FRAMEABLE QUIET HELPER_PRIVATE
      result RESULT_PRIVATE test TEST_BODY TEST_CONDITION|}.
  - intros temps p locals le memory current after final SCOPE SOURCE PREMISE FRAME.
    destruct(tensor_literal_generated_execution SOURCE PREMISE FRAME) as [exit [RUN PUBLIC]].
    exists exit,final; split; [exact RUN|split; [exact PUBLIC|apply memory_equivalent_refl]].
  - intros temps p locals le memory after final SOURCE; exists(adapter_entry temps),after,final; exact SOURCE.
Defined.
Theorem tensor_literal_generated_contract : PrivateRegion.projected_region_contract live source
  (materialized_select test(tensor_literal_candidate helper upper(tensor_region_branch package code))source).
Proof. exact(materialized_preserving_region_contract tensor_literal_generated_rule). Qed.
End GENERATED.
Print Assumptions tensor_literal_generated_execution.
Print Assumptions tensor_literal_generated_rule.
Print Assumptions tensor_literal_generated_contract.
