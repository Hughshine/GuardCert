From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightPrivateRegion
  ClightRegionProgress ClightProjectedExecution CompCertMemoryEquivalence ClightGuard.
From GuardMemory Require Import GuardMemoryBooleanScan.
From GuardInterface Require Import ClightTensorRegionPackage ClightTensorRegionPreservation
  ClightTensorGeneratedCandidates ClightCheckPlanFrame ClightCheckPlan ClightStagedCheck
  ClightSharedGuard ClightQuietDeterminacy ClightReadonlyRewrite ClightReadonlyTreeFacts GuardedRewrite.
Import ListNotations.
Set Implicit Arguments.

(** A language-level preparation receipt. Supported source factories produce
    its fields; an optimizer supplies data, not this semantic callback record. *)
Record tensor_preparation_certificate live source canonical driver flag := TensorPreparationCertificate {
  tpc_source_frame : check_plan_frameable source=true;
  tpc_canonical_frame : check_plan_frameable canonical=true;
  tpc_flag_private : ~In flag(statement_temps source++live);
  tpc_run : forall fe ge locals temps memory after final,
    exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
    exists accepted checked,
      exec_stmt fe ge locals temps memory driver E0 checked memory Out_normal /\
      temp_agree(statement_temps source++live)temps checked /\
      checked!flag=Some(memory_boolean_word accepted) /\
      (accepted=true -> exists exit,
        exec_stmt fe ge locals checked memory canonical E0 exit final Out_normal /\ temp_agree live after exit)
}.

Definition prepared_tensor_complete_check canonical(package:tensor_region_package canonical)driver flag :=
  Ssequence driver(Sifthenelse(shared_guard_choice flag)(shared_guard_code(tensor_region_guard package)flag)Sskip).
Definition prepared_tensor_generated_target source canonical(package:tensor_region_package canonical)driver flag code :=
  Ssequence(prepared_tensor_complete_check package driver flag)
    (Sifthenelse(shared_guard_choice flag)(tensor_region_branch package code)source).

Section GENERATED.
Variables live : list ident.
Variables source canonical driver : statement.
Variable flag : ident.
Variable preparation : tensor_preparation_certificate live source canonical driver flag.
Variable package : tensor_region_package canonical.
Let ports:=statement_temps source++live.
Let canonical_ports:=statement_temps canonical++live++check_plan_reads(tree_check_plan(tensor_region_guard package)).
Hypothesis FLAG : ~In flag canonical_ports.

Theorem prepared_tensor_complete_execution fe ge locals temps memory after final :
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists accepted checked,
    exec_stmt fe ge locals temps memory(prepared_tensor_complete_check package driver flag)E0 checked memory Out_normal /\
    temp_agree ports temps checked /\ checked!flag=Some(memory_boolean_word accepted) /\
    (accepted=true -> exists exit,
      exec_stmt fe ge locals checked memory canonical E0 exit final Out_normal /\
      temp_agree live after exit /\ decision_run(Entry ge locals checked memory)(tensor_region_guard package)true).
Proof.
  intro SOURCE; destruct(tpc_run preparation SOURCE)as [ready [first [RUN [FRAME [WORD CANONICAL]]]]].
  destruct(@shared_guard_choice_test ge locals first memory flag ready WORD)as [value [CHOICE BOOL]].
  unfold prepared_tensor_complete_check; destruct ready.
  - destruct(CANONICAL eq_refl)as [canonical_exit [CANONICAL_RUN PUBLIC]].
    assert(DEFINED:tensor_region_domain package(Entry ge locals first memory)).
    { exists canonical_exit,final; apply(tensor_region_source_execution package).
      eapply quiet_execution_preserved; [split; reflexivity|exact CANONICAL_RUN|apply tensor_region_source_quiet; exact package]. }
    destruct(@readonly_available _ _ _ _ _ (tensor_region_condition package false live) _ DEFINED)
      as [accepted [observed [GUARD SAME]]]; subst observed.
    pose(checked:=PTree.set flag(Vint(shared_guard_word accepted))first).
    assert(CHECK_FRAME:temp_agree canonical_ports first checked)by(apply temp_agree_set; exact FLAG).
    exists accepted,checked; split.
    + eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact RUN|].
      eapply exec_Sifthenelse; [exact CHOICE|exact BOOL|apply shared_guard_execution; exact GUARD].
    + split; [eapply temp_agree_trans; [exact FRAME|apply temp_agree_set; exact(tpc_flag_private preparation)]|].
      split; [apply PTree.gss|intro ACCEPT; subst accepted].
      destruct(@structured_execution_temp_transport fe ge locals first memory canonical E0 canonical_exit final Out_normal
        CANONICAL_RUN canonical_ports checked(statement_temps canonical)(@check_plan_frameable_writes _ (tpc_canonical_frame preparation))
        ltac:(unfold statement_scope,canonical_ports; intros id MEMBER; apply in_or_app; left; exact MEMBER)CHECK_FRAME)
        as [exit [CANONICAL_CHECKED EXIT]].
      exists exit; split; [exact CANONICAL_CHECKED|split].
      * eapply temp_agree_trans; [exact PUBLIC|eapply temp_agree_weaken; [|exact EXIT]].
        unfold canonical_ports; intros id MEMBER; apply in_or_app; right; apply in_or_app; left; exact MEMBER.
      * eapply(@decision_tree_read_frame(tensor_region_guard package)(Entry ge locals first memory)checked true); [|exact GUARD].
        eapply temp_agree_weaken; [|exact CHECK_FRAME].
        unfold canonical_ports; intros id MEMBER; apply in_or_app; right; apply in_or_app; right; exact MEMBER.
  - exists false,first; split.
    + eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact RUN|].
      eapply exec_Sifthenelse; [exact CHOICE|exact BOOL|constructor].
    + split; [exact FRAME|split; [exact WORD|discriminate]].
Qed.

Variables pairs : list(ident*ident).
Variable proposal : tensor_generated_candidate.
Variable code : statement.
Hypothesis CHECK : CoreAlarmed.Base.mayReturn(check_tensor_generated_region package live pairs proposal)(Some code).

Theorem prepared_tensor_generated_execution fe ge locals temps memory after final :
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists exit,exec_stmt fe ge locals temps memory(prepared_tensor_generated_target source package driver flag code)
    E0 exit final Out_normal /\ temp_agree live after exit.
Proof.
  intro SOURCE; destruct(prepared_tensor_complete_execution SOURCE)as [accepted [checked [RUN [FRAME [WORD ACCEPTED]]]]].
  destruct(@shared_guard_choice_test ge locals checked memory flag accepted WORD)as [value [CHOICE BOOL]].
  assert(SELECTED:exists exit,exec_stmt fe ge locals checked memory
    (if accepted then tensor_region_branch package code else source)E0 exit final Out_normal /\ temp_agree live after exit).
  { destruct accepted.
    - destruct(ACCEPTED eq_refl)as [canonical_exit [CANONICAL [PUBLIC GUARD]]].
      destruct(@tensor_region_generated_execution _ package fe ge locals checked memory canonical_exit final
        live pairs proposal code CHECK CANONICAL GUARD)as [exit [CANDIDATE EXIT]].
      exists exit; split; [exact CANDIDATE|eapply temp_agree_trans; eassumption].
    - destruct(@structured_execution_temp_transport fe ge locals temps memory source E0 after final Out_normal SOURCE
        ports checked(statement_temps source)(@check_plan_frameable_writes _ (tpc_source_frame preparation))
        ltac:(unfold statement_scope,ports; intros id MEMBER; apply in_or_app; left; exact MEMBER)FRAME)
        as [exit [FALLBACK PUBLIC]].
      exists exit; split; [exact FALLBACK|eapply temp_agree_weaken; [|exact PUBLIC]].
      unfold ports; intros id MEMBER; apply in_or_app; right; exact MEMBER. }
  destruct SELECTED as [exit [SELECTED PUBLIC]]; exists exit; split; [|exact PUBLIC].
  unfold prepared_tensor_generated_target; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact RUN|].
  eapply exec_Sifthenelse; [exact CHOICE|exact BOOL|exact SELECTED].
Qed.

Theorem prepared_tensor_generated_contract : PrivateRegion.projected_region_contract live source
  (prepared_tensor_generated_target source package driver flag code).
Proof.
  intros temps p locals le current memory after final SCOPE AGREE SOURCE fn continuation.
  destruct(@structured_execution_temp_transport(adapter_entry temps)(globalenv p)locals le memory source E0 after final
    Out_normal SOURCE live current(statement_temps source)(@check_plan_frameable_writes _ (tpc_source_frame preparation))
    SCOPE AGREE)as [middle [ORIGINAL PUBLIC]].
  destruct(prepared_tensor_generated_execution ORIGINAL)as [exit [RUN EXIT_PUBLIC]].
  destruct(exec_stmt_steps(adapter_entry temps)p _ _ _ _ _ _ _ _ RUN fn continuation)as [finish [STEPS EXIT]].
  inversion EXIT; subst finish; exists exit,final; split; [exact STEPS|split].
  - eapply temp_agree_trans; eassumption.
  - apply memory_equivalent_refl.
Qed.
End GENERATED.

Print Assumptions prepared_tensor_complete_execution.
Print Assumptions prepared_tensor_generated_execution.
Print Assumptions prepared_tensor_generated_contract.
