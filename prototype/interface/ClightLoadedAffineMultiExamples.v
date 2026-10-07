From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightCountedLoop ClightRectangularGuard ClightNoWrap
  ClightTempFootprint ClightProjectedExecution.
From GuardMemory Require Import GuardMemoryWindowParameterGuard GuardMemoryIntervalGuard.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestGuardPackage AffineNestPackageGuard
  AffineNestDomainGuard AffineNestNumericGuard AffineNestProbe AffineNestScanAccesses AffineNestScanSeparation
  AffineNestMultiPresumption AffineNestPackageExamples AffineNestShadowTransport.
From GuardAffineNest Require Import AffineNestAliasOnlyGuard.
From GuardInterface Require Import ClightMaterializedCheck ClightCheckPlanFrame ClightSharedGuard ClightLoadedAffineNumericExamples ClightLoadedBodyPrefixExamples
  ClightLoadedAffineNumericSite ClightLoadedAffineScanSite ClightLoadedAffineScanExecution ClightLoadedAffineScanTransfer
  ClightLoadedAffineScanExamples ClightLoadedAffineScanAcceptExample ClightLoadedAffineMultiGuard ClightLoadedAffineCandidate
  ClightLoadedAffineMultiPreservation ClightLoadedSequenceProgress.
Import ListNotations.
Set Implicit Arguments.

Definition lnm_allocated := [101%positive;102%positive;201%positive;202%positive;103%positive;2%positive].
Definition lnm_describe := check_loaded_affine_multi_site lns_source [2%positive] lns_live lnm_allocated lns_proposal 11%positive.
Example loaded_multi_descriptor_selected : lnf_present lnm_describe=true.
Proof. vm_compute; reflexivity. Qed.
Definition lnm_site : loaded_affine_multi_site lns_source [2%positive] lns_live lnm_allocated lns_proposal 11%positive.
Proof.
  destruct lnm_describe as [site|] eqn:CHECK; [exact site|].
  pose proof loaded_multi_descriptor_selected as PRESENT; rewrite CHECK in PRESENT; discriminate.
Defined.

Example loaded_multi_cached_source_key_refused :
  lnf_present(check_loaded_affine_multi_site(affine_nest_source(affine_proposal_nest lns_proposal))
    [2%positive] lns_live lnm_allocated lns_proposal 11%positive)=false.
Proof. vm_compute; reflexivity. Qed.
Example loaded_multi_overlapping_private_scans_refused :
  lnf_present(check_loaded_affine_multi_site lns_source [2%positive] lns_live
    [101%positive;102%positive;101%positive;102%positive;103%positive;2%positive] lns_proposal 11%positive)=false.
Proof. vm_compute; reflexivity. Qed.
Example recursive_loaded_multi_descriptor_selected :
  lnf_present(check_loaded_affine_multi_site lnf_source affine_memory_example_parameters lnf_live
    [101%positive;104%positive;102%positive;105%positive;103%positive;106%positive;
     201%positive;204%positive;202%positive;205%positive;203%positive;206%positive;107%positive;4%positive]
    lnf_proposal 11%positive)=true.
Proof. vm_compute; reflexivity. Qed.
Example recursive_loaded_source_progress_selected : loaded_sequence_progress_supported lnf_source=true.
Proof. vm_compute; reflexivity. Qed.

Lemma lnm_single_array_flag ge locals reference memory :
  reference!1%positive=Some(Vint Int.zero) -> reference!2%positive=Some(Vint(Int.repr 2)) ->
  affine_multi_guard_flag [2%positive] lns_proposal(Entry ge locals reference memory)=true.
Proof.
  intros ROOT CACHE.
  unfold affine_multi_guard_flag,affine_package_guard_flag,affine_domain_guard_flag,affine_numeric_guard_flag,
    affine_multi_alias_result,affine_scan_separation_result,affine_scan_access_pair_result.
  cbn [lns_proposal affine_proposal_nest affine_scan_accesses lns_operation lns_access
    affine_first_path_flag affine_proposed_iterator affine_proposed_bound affine_proposed_body affine_proposed_child
    affine_proposed_parameter_ranges affine_proposed_floor affine_proposed_cap affine_proposed_operations
    affine_proposed_window_lower affine_proposed_window_upper].
  unfold window_parameters_accept,signed_interval_flag,signed_interval_lower_flag,register_at_most,temp_word.
  cbn [entry_temps]; rewrite ROOT,CACHE; vm_compute; reflexivity.
Qed.

Theorem loaded_multi_self_alias_refuses fe ge locals : exists after,
  exec_stmt fe ge locals lns_alias_temps lbp_two_memory
    (loaded_affine_multi_guard_body(loaded_multi_transfer lnm_site)(loaded_multi_package lnm_site))
    E0 after lbp_two_memory Out_normal /\
  expression_test(shared_guard_choice 103%positive)(Entry ge locals after lbp_two_memory) false /\
  loaded_affine_scan_entry_relation [2%positive] lns_live lns_proposal 11%positive
    (Entry ge locals lns_alias_temps lbp_two_memory)(Entry ge locals after lbp_two_memory).
Proof.
  destruct(@loaded_affine_scan_site_execution _ _ _ _ _ (loaded_transfer_scan(loaded_multi_transfer lnm_site))
    fe ge locals lns_alias_temps lbp_two_memory _ _ (@self_alias_original_stops_after_one fe ge locals))
    as [after [SCAN [_ [FLAG _]]]].
  rewrite(self_alias_complete_flag_refuses ge locals) in FLAG.
  pose proof(@shared_guard_choice_test ge locals after lbp_two_memory 103%positive false FLAG) as TEST.
  exists after; split.
  - unfold loaded_affine_multi_guard_body; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact SCAN|].
    destruct TEST as [value [EVAL BOOL]]; eapply exec_Sifthenelse with(v1:=value)(b:=false);
      [exact EVAL|exact BOOL|apply exec_Sskip].
  - split; [exact TEST|eapply loaded_affine_scan_transfer_execution; [apply self_alias_original_stops_after_one|exact SCAN]].
Qed.

Theorem loaded_multi_self_alias_fallback_stops_after_one fe ge locals candidate : exists after,
  exec_stmt fe ge locals lns_alias_temps lbp_two_memory(materialized_select(loaded_multi_test lnm_site) candidate lns_source)
    E0 after lbp_one_memory Out_normal /\
  temp_agree lns_live(PTree.set 1%positive(Vint Int.one)lns_alias_temps) after.
Proof.
  destruct(@loaded_multi_self_alias_refuses fe ge locals) as [checked [GUARD [TEST ENTRY]]].
  pose proof(loaded_affine_scan_entry_public(loaded_multi_transfer lnm_site) ENTRY) as [_ [_ [_ FRAME]]].
  destruct(@structured_execution_temp_transport fe ge locals lns_alias_temps lbp_two_memory lns_source
    E0 (PTree.set 1%positive(Vint Int.one)lns_alias_temps)lbp_one_memory Out_normal
    (@self_alias_original_stops_after_one fe ge locals) lns_live checked (statement_temps lns_source)
    (@check_plan_frameable_writes _
      (loaded_numeric_frameable(loaded_scan_numeric(loaded_transfer_scan(loaded_multi_transfer lnm_site)))))
    (@affine_statement_scope_check_sound lns_live lns_source ltac:(vm_compute; reflexivity)) FRAME) as [after [SOURCE EXIT]].
  exists after; split; [|exact EXIT].
  apply(proj2(materialized_select_execution_exact fe ge locals lns_alias_temps lbp_two_memory
    (loaded_multi_test lnm_site)candidate lns_source E0 after lbp_one_memory Out_normal)).
  exists false,checked; split.
  - rewrite(proj1(@describe_materialized_check_exact _ _ _ (loaded_multi_describe lnm_site))); exact GUARD.
  - split; [rewrite(proj2(@describe_materialized_check_exact _ _ _ (loaded_multi_describe lnm_site))); exact TEST|exact SOURCE].
Qed.

Theorem loaded_multi_same_block_accepts fe ge locals : exists after,
  exec_stmt fe ge locals lns_separate_temps lns_initial
    (loaded_affine_multi_guard_body(loaded_multi_transfer lnm_site)(loaded_multi_package lnm_site))
    E0 after lns_initial Out_normal /\
  expression_test(shared_guard_choice 103%positive)(Entry ge locals after lns_initial) true /\
  loaded_affine_candidate_presumption fe [2%positive] lns_live lns_proposal 11%positive
    (Entry ge locals lns_separate_temps lns_initial) /\
  loaded_affine_scan_entry_relation [2%positive] lns_live lns_proposal 11%positive
    (Entry ge locals lns_separate_temps lns_initial)(Entry ge locals after lns_initial).
Proof.
  pose proof(@same_block_original_completes fe ge locals) as SOURCE.
  destruct(@loaded_affine_scan_site_execution _ _ _ _ _ (loaded_transfer_scan(loaded_multi_transfer lnm_site))
    fe ge locals lns_separate_temps lns_initial _ _ SOURCE) as [reference [SCAN [_ [FLAG STABLE]]]].
  rewrite(same_block_nonoverlap_flag_accepts ge locals) in FLAG,STABLE; specialize(STABLE eq_refl).
  pose proof(@loaded_affine_scan_transfer_execution _ _ _ _ _ (loaded_multi_transfer lnm_site)
    fe ge locals lns_separate_temps lns_initial _ _ reference SOURCE SCAN) as ENTRY.
  destruct ENTRY as [upper [SNAPSHOT [GE [ENV [MEMORY FRAME]]]]].
  assert(UPPER:upper=Int.repr 2).
  { destruct SNAPSHOT as [block [offset [word [POINTER [READ CACHE]]]]].
    cbn [loaded_affine_scan_prepared entry_temps entry_memory] in POINTER,READ,CACHE.
    change(affine_proposed_bound lns_proposal) with 2%positive in *.
    rewrite PTree.gso in POINTER by discriminate; change(lns_separate_temps!11%positive)
      with(Some(Vptr 1%positive Ptrofs.zero)) in POINTER; inversion POINTER; subst block offset.
    rewrite(proj1 same_block_bound_reads) in READ; injection READ as WORD; subst word.
    rewrite PTree.gss in CACHE; congruence. }
  subst upper.
  assert(ROOT:reference!1%positive=Some(Vint Int.zero)).
  { rewrite FRAME; [reflexivity|vm_compute; tauto]. }
  assert(CACHE:reference!2%positive=Some(Vint(Int.repr 2))).
  { rewrite FRAME; [apply PTree.gss|vm_compute; tauto]. }
  pose proof(@lnm_single_array_flag ge locals reference lns_initial ROOT CACHE) as ALIAS_FLAG.
  destruct(@loaded_affine_cached_source_at_snapshot _ _ _ _ _ (loaded_transfer_scan(loaded_multi_transfer lnm_site))
    fe ge locals lns_separate_temps lns_initial _ _ (Int.repr 2) STABLE SNAPSHOT SOURCE) as [cached_after [CACHED _]].
  destruct(@Guard.ClightProjectedExecution.structured_execution_temp_transport fe ge locals _ lns_initial _ E0 cached_after
    lns_last Out_normal CACHED (loaded_affine_scan_ports [2%positive] lns_proposal lns_live) reference
    (affine_nest_controls(affine_proposal_nest lns_proposal))
    (ClightAffineNestMaterialized.affine_materialized_source_writes(AffineNestMultiStaticPackage.affine_multi_guard(loaded_multi_package lnm_site)))
    (loaded_multi_cached_scope lnm_site) FRAME) as [reference_after [REFERENCE_SOURCE _]].
  assert(NUMERIC:affine_package_guard_flag [2%positive] lns_proposal(Entry ge locals reference lns_initial)=true).
  { unfold affine_multi_guard_flag in ALIAS_FLAG; apply andb_true_iff in ALIAS_FLAG; tauto. }
  destruct(@affine_multi_alias_only_execution _ _ _ _ _ (loaded_multi_package lnm_site)
    fe ge locals reference lns_initial reference_after lns_last REFERENCE_SOURCE NUMERIC FLAG) as [after [ALIAS [AFTER RESULT]]].
  rewrite ALIAS_FLAG in RESULT.
  exists after; split.
  - unfold loaded_affine_multi_guard_body; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact SCAN|].
    destruct(@shared_guard_choice_test ge locals reference lns_initial 103%positive true FLAG) as [value [EVAL BOOL]].
    eapply exec_Sifthenelse with(v1:=value)(b:=true); eassumption.
  - split; [apply shared_guard_choice_test; exact RESULT|split].
    + split; [exact STABLE|exists(Int.repr 2),reference; auto].
    + exists(Int.repr 2); split; [exact SNAPSHOT|repeat split; try reflexivity; eapply temp_agree_trans; eassumption].
Qed.

Print Assumptions loaded_multi_descriptor_selected.
Print Assumptions loaded_multi_cached_source_key_refused.
Print Assumptions loaded_multi_overlapping_private_scans_refused.
Print Assumptions recursive_loaded_multi_descriptor_selected.
Print Assumptions recursive_loaded_source_progress_selected.
Print Assumptions lnm_single_array_flag.
Print Assumptions loaded_multi_self_alias_refuses.
Print Assumptions loaded_multi_self_alias_fallback_stops_after_one.
Print Assumptions loaded_multi_same_block_accepts.
