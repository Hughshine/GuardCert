From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib Maps.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightGuard ClightPrivateRegion ClightRegionProgress
  ClightTempFrame ClightTempFootprint ClightProjectedExecution.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryPointerSequence.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyRuleEmbedding
  ClightAffineSnapshotSyntax ClightAffineSnapshotRows ClightAffineSnapshotCaptureCandidate ClightAffineSnapshotSourceInputs
  ClightAffineEmptySnapshotCondition ClightAffineEmptySnapshotRewrite ClightAffineEmptyConditionClient
  ClightAffineEmptyConditionCapture ClightAffineZeroSnapshotPreparation ClightNestedExpressionCapture
  ClightSourceObservation ClightSourcePrefixRegion ClightLoadedBoundSyntax
  ClightCheckPlan ClightCheckPlanFrame ClightSharedGuard ClightReadonlyAlternativePlan
  ClightProjectedRuntimeDispatch.
Import ListNotations.
Set Implicit Arguments.

Lemma affine_empty_runtime_frameable_quiet code : quiet_statement code=check_plan_frameable code.
Proof. induction code; cbn [quiet_statement check_plan_frameable];
  try rewrite IHcode1,IHcode2; reflexivity. Qed.
Lemma affine_empty_runtime_prefix_quiet loads : quiet_statement (source_load_prefix loads)=true.
Proof. induction loads as [|[out pointer] rest IH]; cbn [source_load_prefix quiet_statement]; auto. Qed.

Definition affine_empty_runtime_source loads original suffix :=
  Ssequence (Ssequence (source_load_prefix loads) original) suffix.
Definition affine_empty_runtime_setup original (site:affine_snapshot_source_package original)
    loads condition result :=
  Ssequence (source_load_prefix loads)
    (Ssequence (affine_snapshot_capture_statement site)
      (check_plan_code (affine_empty_client_plan site condition) result)).
Definition affine_empty_runtime_fast original (site:affine_snapshot_source_package original) suffix :=
  Ssequence (affine_empty_client_yes site) suffix.
Definition affine_empty_runtime_target original (site:affine_snapshot_source_package original)
    loads condition result suffix previous :=
  projected_runtime_dispatch (affine_empty_runtime_setup site loads condition result)
    (shared_guard_choice result) (affine_empty_runtime_fast site suffix) previous.

Section PRELUDE.
Variable original:statement.
Variable site:affine_snapshot_source_package original.
Variable live:list ident.
Variable capture:affine_snapshot_capture_package site live.
Let package:=snapshot_cached_package site.
Variable condition:decision_tree.
Hypothesis CONDITION:forall fe,readonly_condition (readonly_clight_host fe (@eq fragment_observation))
  (affine_snapshot_original_domain package (snapshot_root site) (snapshot_child site)
    (snapshot_child_cache site) (snapshot_original_header site) fe)
  (affine_empty_snapshot_facts site) condition.
Variable result:ident.
Hypothesis RESOURCES:check_plan_resources (affine_empty_client_plan site condition) result live
  (affine_empty_client_yes site) original=true.
Variable loads:list (ident*ident).
Hypothesis PREFIX_FRESH:forall id,In id (source_load_targets loads)->~In id (source_load_pointers loads).
Variable suffix:statement.
Hypothesis SUFFIX_QUIET:quiet_statement suffix=true.

(** The empty condition's domain and the old target's refused entry are both
    produced from the original source execution. The fast branch keeps the real
    source suffix, including its memory effects. No body-only observation is
    added to the empty condition's invocation domain. *)
Theorem affine_empty_runtime_prelude (SUFFIX_SCOPE:statement_scope live suffix) :
  projected_dispatch_prelude live (affine_empty_runtime_source loads original suffix)
    (affine_empty_runtime_setup site loads condition result) (shared_guard_choice result)
    (affine_empty_runtime_fast site suffix).
Proof.
  intros temps p locals entry memory after final SOURCE.
  destruct (@source_prefix_region_execution loads original suffix (adapter_entry temps)
    (globalenv p) locals entry memory after final SOURCE)
    as [middle [body_after [body_memory [PREFIX [BODY SUFFIX]]]]].
  assert (FRAMEABLE:check_plan_frameable (affine_snapshot_source package (snapshot_root site)
    (snapshot_original_header site))=true).
  { rewrite <-snapshot_source_exact; exact (snapshot_capture_frameable capture). }
  assert (ROOT_PRIVATE:~In (affine_inner_pointer_bound (affine_inner_pointer_shape package))
    (statement_temps (affine_snapshot_source package (snapshot_root site) (snapshot_original_header site))++
      (live++affine_inner_pointer_pointers package))).
  { rewrite <-snapshot_source_exact; exact (snapshot_capture_root_private capture). }
  assert (CHILD_PRIVATE:~In (snapshot_child_cache site)
    (statement_temps (affine_snapshot_source package (snapshot_root site) (snapshot_original_header site))++
      (live++affine_inner_pointer_pointers package))).
  { rewrite <-snapshot_source_exact; exact (snapshot_capture_child_private capture). }
  rewrite (snapshot_source_exact site) in BODY.
  destruct (@affine_snapshot_capture_source_inputs (snapshot_cached_source site) package (snapshot_root site)
    (snapshot_child site) (snapshot_child_cache site) (snapshot_original_header site)
    (live++affine_inner_pointer_pointers package) (adapter_entry temps) (globalenv p) locals middle memory
    body_after body_memory (snapshot_header_word site) (snapshot_child_read site)
    (@memory_pointer_sequence_quiet _ _ (affine_inner_pointer_body_exact (affine_inner_pointer_syntax package)))
    FRAMEABLE ROOT_PRIVATE CHILD_PRIVATE (snapshot_capture_caches_distinct capture) BODY)
    as [upper [child [checked [source_after [CAPTURE [CHECKED [PREPARED [PUBLIC DOMAIN]]]]]]]].
  rewrite <-snapshot_source_exact in BODY,PREPARED.
  pose proof (@affine_empty_client_guarded_execution original site condition CONDITION (adapter_entry temps)
    (globalenv p) locals checked memory source_after body_memory DOMAIN PREPARED) as SELECT.
  unfold affine_empty_client_guarded in SELECT.
  destruct (@readonly_alternative_selected_execution (adapter_entry temps) (globalenv p) locals checked memory
    (affine_empty_client_outer site) condition (affine_empty_snapshot_restore site) original source_after
    body_memory SELECT) as [answer [CHECK BRANCH]].
  destruct (check_plan_resources_sound _ _ _ _ _ RESOURCES) as [YES [NO PRIVATE]].
  assert (PLAN_PRIVATE:~In result (check_plan_reads (affine_empty_client_plan site condition))).
  { intro MEMBER; apply PRIVATE,in_or_app; left; exact MEMBER. }
  assert (FLAG_PRIVATE:~In result live).
  { intro MEMBER; apply PRIVATE; repeat rewrite in_app_iff; tauto. }
  assert (CHECK_CODE:exec_stmt (adapter_entry temps) (globalenv p) locals checked memory
    (check_plan_code (affine_empty_client_plan site condition) result) E0
    (PTree.set result (Vint (shared_guard_word answer)) checked) memory Out_normal).
  { eapply (@check_plan_code_execution (adapter_entry temps) (Entry (globalenv p) locals checked memory)
      (affine_empty_client_plan site condition) answer);
      [apply check_plan_tree_run; exact CHECK|exact PLAN_PRIVATE|apply temp_agree_refl]. }
  exists (PTree.set result (Vint (shared_guard_word answer)) checked),answer; split.
  - unfold affine_empty_runtime_setup; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [exact PREFIX|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [exact CAPTURE|exact CHECK_CODE].
  - split; [apply shared_guard_choice_test,PTree.gss|].
    destruct answer.
    + assert (YES_PRIVATE:~In result (statement_temps (affine_empty_client_yes site)++live)).
      { intro MEMBER; apply PRIVATE; repeat rewrite in_app_iff in *; tauto. }
      destruct (@structured_execution_temp_transport (adapter_entry temps) (globalenv p) locals checked memory
        (affine_empty_client_yes site) E0 source_after body_memory Out_normal BRANCH
        (statement_temps (affine_empty_client_yes site)++live)
        (PTree.set result (Vint (shared_guard_word true)) checked)
        (statement_temps (affine_empty_client_yes site))
        (@check_plan_frameable_writes (affine_empty_client_yes site) YES)
        ltac:(unfold statement_scope; intros id MEMBER; apply in_or_app; left; exact MEMBER)
        (@temp_agree_set _ _ _ _ YES_PRIVATE)) as [fast_exit [FAST FAST_FRAME]].
      assert (BODY_PUBLIC:temp_agree live body_after fast_exit).
      { eapply temp_agree_trans.
        - eapply temp_agree_weaken; [|exact PUBLIC].
          intros id MEMBER; apply in_or_app; right; apply in_or_app; left; exact MEMBER.
        - eapply temp_agree_weaken; [|exact FAST_FRAME].
          intros id MEMBER; apply in_or_app; right; exact MEMBER. }
      destruct (@structured_execution_temp_transport (adapter_entry temps) (globalenv p) locals body_after
        body_memory suffix E0 after final Out_normal SUFFIX live fast_exit (statement_temps suffix)
        (@quiet_source_write_bound suffix SUFFIX_QUIET) SUFFIX_SCOPE BODY_PUBLIC)
        as [exit [TAIL EXIT]].
      exists exit; split; [|exact EXIT].
      unfold affine_empty_runtime_fast; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); eassumption.
    + exists middle; split.
      * eapply temp_agree_trans; [|apply temp_agree_set; exact FLAG_PRIVATE].
        rewrite CHECKED; eapply temp_agree_weaken;
          [|apply nested_expression_captured_frame; [exact ROOT_PRIVATE|exact CHILD_PRIVATE]].
        intros id MEMBER; apply in_or_app; right; apply in_or_app; left; exact MEMBER.
      * unfold affine_empty_runtime_source; eapply source_prefix_region_replay; eassumption.
Qed.

Theorem affine_empty_runtime_contract previous :
  PrivateRegion.projected_region_contract live (affine_empty_runtime_source loads original suffix) previous ->
  PrivateRegion.projected_region_contract live (affine_empty_runtime_source loads original suffix)
    (affine_empty_runtime_target site loads condition result suffix previous).
Proof.
  intros PREVIOUS temps p locals entry current memory after final SCOPE AGREE SOURCE fn continuation.
  assert (SUFFIX_SCOPE:statement_scope live suffix).
  { intros id MEMBER; apply SCOPE; unfold affine_empty_runtime_source; cbn [statement_temps];
      apply in_or_app; right; exact MEMBER. }
  assert (WRITES:writes_only (statement_temps (affine_empty_runtime_source loads original suffix))
    (affine_empty_runtime_source loads original suffix)).
  { apply quiet_source_write_bound; unfold affine_empty_runtime_source; cbn [quiet_statement].
    rewrite SUFFIX_QUIET.
    rewrite affine_empty_runtime_prefix_quiet.
    assert (QUIET:quiet_statement original=true).
    { rewrite affine_empty_runtime_frameable_quiet; exact (snapshot_capture_frameable capture). }
    rewrite QUIET; reflexivity. }
  exact (@projected_runtime_dispatch_contract live (affine_empty_runtime_source loads original suffix)
    (affine_empty_runtime_setup site loads condition result) (shared_guard_choice result)
    (affine_empty_runtime_fast site suffix) previous WRITES (affine_empty_runtime_prelude SUFFIX_SCOPE)
    PREVIOUS temps p locals entry current memory after final SCOPE AGREE SOURCE fn continuation).
Qed.
End PRELUDE.

Print Assumptions affine_empty_runtime_prelude.
Print Assumptions affine_empty_runtime_contract.
Print Assumptions affine_empty_runtime_frameable_quiet.
Print Assumptions affine_empty_runtime_prefix_quiet.
