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

Definition tensor_literal_ports live source helper tree :=
  statement_temps source++live++remove peq helper(check_plan_reads(tree_check_plan tree)).
Definition tensor_literal_prepared_entry helper upper entry :=
  Entry(entry_ge entry)(entry_env entry)(literal_bound_temps helper upper(entry_temps entry))(entry_memory entry).
Definition tensor_literal_check_body helper upper tree result :=
  Ssequence(literal_bound_set helper upper)(shared_guard_code tree result).
Definition tensor_literal_candidate helper upper branch:=Ssequence(literal_bound_set helper upper)branch.

Section PRESERVATION.
Variables live : list ident.
Variable source : statement.
Variable helper : ident.
Variable upper : int.
Variable package : tensor_region_package(literal_tests_prepare helper upper source).
Let tree:=tensor_region_guard package.
Let ports:=tensor_literal_ports live source helper tree.
Hypothesis FRAMEABLE : check_plan_frameable source=true.
Hypothesis QUIET : quiet_statement source=true.
Hypothesis HELPER_PRIVATE : ~In helper(statement_temps source++live).
Variable result : ident.
Hypothesis RESULT_PRIVATE : ~In result(helper::ports).
Variable test : materialized_check.
Hypothesis TEST_BODY : materialized_body test=tensor_literal_check_body helper upper tree result.
Hypothesis TEST_CONDITION : materialized_condition test=shared_guard_choice result.

Lemma tensor_literal_ports_live : incl live ports.
Proof. intros id MEMBER; unfold ports,tensor_literal_ports; repeat rewrite in_app_iff; tauto. Qed.
Lemma tensor_literal_ports_source : incl(statement_temps source++live)ports.
Proof. intros id MEMBER; unfold ports,tensor_literal_ports; repeat rewrite in_app_iff in *; tauto. Qed.
Lemma tensor_literal_helper_private : ~In helper ports.
Proof.
  unfold ports,tensor_literal_ports; repeat rewrite in_app_iff; intros [SOURCE|[LIVE|READ]].
  - apply HELPER_PRIVATE,in_or_app; left; exact SOURCE.
  - apply HELPER_PRIVATE,in_or_app; right; exact LIVE.
  - exact(remove_In peq _ _ READ).
Qed.
Lemma tensor_literal_helper_scope_private : ~In helper(statement_temps source++ports).
Proof.
  rewrite in_app_iff; intros [SOURCE|PORT].
  - apply HELPER_PRIVATE,in_or_app; left; exact SOURCE.
  - exact(tensor_literal_helper_private PORT).
Qed.
Lemma tensor_literal_prepared_frame before current : temp_agree ports before current ->
  temp_agree(check_plan_reads(tree_check_plan tree))
    (literal_bound_temps helper upper before)(literal_bound_temps helper upper current).
Proof.
  intros FRAME id READ; unfold literal_bound_temps; rewrite !PTree.gsspec; destruct(peq id helper); [reflexivity|].
  apply FRAME; unfold ports,tensor_literal_ports; apply in_or_app; right; apply in_or_app; right.
  apply in_in_remove; assumption.
Qed.

Definition tensor_literal_domain:=materialized_source_completion source.
Definition tensor_literal_premise entry:=decision_run(tensor_literal_prepared_entry helper upper entry)tree true.

Lemma tensor_literal_canonical_source fe ge locals le memory after final current :
  exec_stmt fe ge locals le memory source E0 after final Out_normal -> temp_agree ports le current ->
  exists exit,
    exec_stmt fe ge locals(literal_bound_temps helper upper current)memory
      (literal_tests_prepare helper upper source)E0 exit final Out_normal /\ temp_agree live after exit.
Proof.
  intros SOURCE FRAME; eapply literal_prepared_source_execution; [exact FRAMEABLE|exact HELPER_PRIVATE|exact SOURCE|].
  eapply temp_agree_weaken; [exact tensor_literal_ports_source|exact FRAME].
Qed.

Theorem tensor_literal_check_encoding fe entry : tensor_literal_domain entry ->
  exists accepted after,
    exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
      (materialized_body test)E0 after(entry_memory entry)Out_normal /\
    expression_test(materialized_condition test)(Entry(entry_ge entry)(entry_env entry)after(entry_memory entry))accepted /\
    temp_agree ports(entry_temps entry)after /\ (accepted=true -> tensor_literal_premise entry).
Proof.
  intro DOMAIN; destruct(@materialized_source_receipt fe source entry QUIET DOMAIN)as [after [final SOURCE]].
  destruct(tensor_literal_canonical_source SOURCE(temp_agree_refl _ _))as [canonical [CANONICAL _]].
  assert(DEFINED:tensor_region_domain package(tensor_literal_prepared_entry helper upper entry)).
  { exists canonical,final; apply(tensor_region_source_execution package).
    eapply quiet_execution_preserved; [split; reflexivity|exact CANONICAL|apply tensor_region_source_quiet; exact package]. }
  destruct(@readonly_available _ _ _ _ _ (tensor_region_condition package false live) _ DEFINED)
    as [accepted [checked [GUARD SAME]]]; subst checked.
  exists accepted,(PTree.set result(Vint(shared_guard_word accepted))(literal_bound_temps helper upper(entry_temps entry))).
  split.
  - rewrite TEST_BODY; unfold tensor_literal_check_body; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0).
    + apply literal_bound_set_execution.
    + apply shared_guard_execution; exact GUARD.
  - split.
    + rewrite TEST_CONDITION; apply shared_guard_choice_test; apply PTree.gss.
    + split.
      * eapply temp_agree_trans; [apply literal_bound_temps_frame; exact tensor_literal_helper_private|apply temp_agree_set].
        intro MEMBER; apply RESULT_PRIVATE; right; exact MEMBER.
      * intro ACCEPT; subst accepted; exact GUARD.
Qed.

Definition tensor_literal_certificate temps : guard_certificate
  (materialized_host(adapter_entry temps)(scan_public_observe live))tensor_literal_domain tensor_literal_premise
  (private_scan_entry_frame ports)(private_scan_entry_frame ports)test :=
  @materialized_execution_certificate(adapter_entry temps)_(scan_public_observe live)ports
    tensor_literal_domain tensor_literal_premise test(tensor_literal_check_encoding(adapter_entry temps)).

Variable pool : list(ident*ident).
Variable proposal : tensor_region_candidate.
Variable code : statement.
Hypothesis CHECK : CoreAlarmed.Base.mayReturn(check_tensor_region_candidate package live pool proposal)(Some code).

Theorem tensor_literal_candidate_execution fe ge locals le memory after final current :
  exec_stmt fe ge locals le memory source E0 after final Out_normal ->
  tensor_literal_premise(Entry ge locals le memory) -> temp_agree ports le current ->
  exists exit,exec_stmt fe ge locals current memory
    (tensor_literal_candidate helper upper(tensor_region_branch package code))E0 exit final Out_normal /\
    temp_agree live after exit.
Proof.
  intros SOURCE PREMISE FRAME.
  destruct(tensor_literal_canonical_source SOURCE FRAME)as [canonical [CANONICAL PUBLIC]].
  assert(GUARD:decision_run(Entry ge locals(literal_bound_temps helper upper current)memory)tree true).
  { exact(@decision_tree_read_frame tree(tensor_literal_prepared_entry helper upper(Entry ge locals le memory))
      (literal_bound_temps helper upper current)true(tensor_literal_prepared_frame FRAME)PREMISE). }
  destruct(@tensor_region_candidate_execution _ package fe ge locals(literal_bound_temps helper upper current)memory
    canonical final live pool proposal code CHECK CANONICAL GUARD)as [exit [CANDIDATE EXIT]].
  exists exit; split.
  - unfold tensor_literal_candidate; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [apply literal_bound_set_execution|exact CANDIDATE].
  - eapply temp_agree_trans; eassumption.
Qed.

Definition tensor_literal_preserving_rule : materialized_preserving_rule live source.
Proof.
  refine {|materialized_candidate:=tensor_literal_candidate helper upper(tensor_region_branch package code);
    materialized_test:=test;materialized_domain:=tensor_literal_domain;materialized_premise:=tensor_literal_premise;
    materialized_ports:=ports;materialized_ports_live:=tensor_literal_ports_live;
    materialized_writes:=statement_temps source;materialized_source_writes:=check_plan_frameable_writes source FRAMEABLE;
    materialized_certificate:=tensor_literal_certificate|}.
  - intros temps p locals le memory current after final SCOPE SOURCE PREMISE FRAME.
    destruct(tensor_literal_candidate_execution SOURCE PREMISE FRAME)as [exit [RUN PUBLIC]].
    exists exit,final; split; [exact RUN|split; [exact PUBLIC|apply memory_equivalent_refl]].
  - intros temps p locals le memory after final SOURCE; exists(adapter_entry temps),after,final; exact SOURCE.
Defined.
Theorem tensor_literal_region_contract : PrivateRegion.projected_region_contract live source
  (materialized_select test(tensor_literal_candidate helper upper(tensor_region_branch package code))source).
Proof. exact(materialized_preserving_region_contract tensor_literal_preserving_rule). Qed.
End PRESERVATION.
Print Assumptions tensor_literal_ports_live.
Print Assumptions tensor_literal_helper_private.
Print Assumptions tensor_literal_prepared_frame.
Print Assumptions tensor_literal_canonical_source.
Print Assumptions tensor_literal_check_encoding.
Print Assumptions tensor_literal_certificate.
Print Assumptions tensor_literal_candidate_execution.
Print Assumptions tensor_literal_preserving_rule.
Print Assumptions tensor_literal_region_contract.
