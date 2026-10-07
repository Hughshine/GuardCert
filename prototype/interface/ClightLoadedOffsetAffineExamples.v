From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightNoWrap ClightTempFootprint ClightProjectedExecution.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestGuardPackage AffineNestPackageGuard AffineNestDomainGuard AffineNestPackageExamples AffineNestShadowTransport.
From GuardInterface Require Import ClightLoadedOffsetHeader ClightExpressionHeaderCapture ClightStrictLoopProgress
  ClightSignedExpressionProgress ClightDualLoadedUnitSyntax ClightLoadedAffineNumericExamples ClightLoadedAffineScanExamples
  ClightLoadedAffineScanAcceptExample ClightLoadedAffineMultiExamples ClightLoadedBodyPrefixExamples
  ClightLoadedOffsetAliasExample ClightLoadedOffsetExamples ClightSharedGuard ClightMaterializedCheck ClightCheckPlanFrame
  ClightLoadedAffineScanExecution ClightLoadedOffsetAffineScanSite ClightLoadedOffsetAffineScanExecution
  ClightLoadedOffsetAffineScanCertificate ClightLoadedOffsetAffineScanTransfer ClightLoadedOffsetAffineCandidate
  ClightLoadedOffsetAffineMultiGuard ClightLoadedOffsetAffineMultiPreservation ClightExpressionAffineNumericSite.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition loe_proposal := AffineGuardProposal 1%positive 2%positive lns_body(AffineSourceLeaf lns_body)
  [(0,3);(1,4)] 0 1 [3%positive] [lns_operation] [(1,4)] 0 3 [] [101%positive;102%positive] 103%positive.
Definition loe_describe := check_offset_affine_multi_site loa_source [2%positive] lns_live lnm_allocated loe_proposal 11%positive Int.one.
Example offset_full_multi_site_selected : lnf_present loe_describe=true.
Proof. vm_compute; reflexivity. Qed.
Definition loe_site : offset_affine_multi_site loa_source [2%positive] lns_live lnm_allocated loe_proposal 11%positive Int.one.
Proof.
  destruct loe_describe as [site|] eqn:SELECT; [exact site|].
  pose proof offset_full_multi_site_selected as PRESENT; rewrite SELECT in PRESENT; discriminate.
Defined.
Example offset_full_multi_wrong_offset_refused :
  lnf_present(check_offset_affine_multi_site loa_source [2%positive] lns_live lnm_allocated loe_proposal 11%positive Int.zero)=false.
Proof. vm_compute; reflexivity. Qed.
Example offset_full_multi_private_cache_refused :
  lnf_present(check_offset_affine_multi_site loa_source [2%positive] (2%positive::lns_live) lnm_allocated loe_proposal 11%positive Int.one)=false.
Proof. vm_compute; reflexivity. Qed.
Example offset_recursive_full_multi_site_selected :
  lnf_present(check_offset_affine_multi_site lof_source affine_memory_example_parameters lnf_live
    [101%positive;104%positive;102%positive;105%positive;103%positive;106%positive;
     201%positive;204%positive;202%positive;205%positive;203%positive;206%positive;107%positive;4%positive]
    lnf_proposal 11%positive Int.one)=true.
Proof. vm_compute; reflexivity. Qed.
Example offset_recursive_host_progress_selected : signed_expression_region_progress_supported lof_source=true.
Proof. vm_compute; reflexivity. Qed.

Example offset_alias_numeric_phase_passes ge locals :
  affine_package_guard_flag [2%positive] loe_proposal
    (loaded_affine_scan_prepared loe_proposal(Entry ge locals lns_alias_temps lbp_two_memory)(Int.add(Int.repr 2)Int.one))=true.
Proof. vm_compute; reflexivity. Qed.
Example offset_alias_stability_phase_refuses ge locals :
  offset_affine_scan_flag [2%positive] loe_proposal 11%positive Int.one(Entry ge locals lns_alias_temps lbp_two_memory)=false.
Proof.
  unfold offset_affine_scan_flag; cbn [entry_temps entry_memory].
  change(lns_alias_temps!11%positive) with(Some(Vptr 1%positive Ptrofs.zero)); cbn -[Mem.loadv].
  rewrite lbp_concrete_read; vm_compute; reflexivity.
Qed.

Theorem offset_alias_full_guard_refuses fe ge locals : exists after,
  exec_stmt fe ge locals lns_alias_temps lbp_two_memory
    (offset_affine_multi_guard_body(offset_multi_transfer loe_site)(offset_multi_package loe_site))
    E0 after lbp_two_memory Out_normal /\
  expression_test(shared_guard_choice 103%positive)(Entry ge locals after lbp_two_memory) false /\
  offset_affine_scan_entry_relation [2%positive] lns_live loe_proposal 11%positive Int.one
    (Entry ge locals lns_alias_temps lbp_two_memory)(Entry ge locals after lbp_two_memory).
Proof.
  destruct(@offset_affine_scan_site_execution _ _ _ _ _ _ (offset_transfer_scan(offset_multi_transfer loe_site))
    fe ge locals lns_alias_temps lbp_two_memory _ _ (@offset_alias_original_stops_after_two fe ge locals))
    as [after [SCAN [_ [FLAG _]]]].
  rewrite offset_alias_stability_phase_refuses in FLAG.
  pose proof(@shared_guard_choice_test ge locals after lbp_two_memory 103%positive false FLAG) as TEST.
  exists after; split.
  - unfold offset_affine_multi_guard_body; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact SCAN|].
    destruct TEST as [value [EVAL BOOL]]; eapply exec_Sifthenelse with(v1:=value)(b:=false);
      [exact EVAL|exact BOOL|constructor].
  - split; [exact TEST|eapply offset_affine_scan_transfer_execution;
      [apply offset_alias_original_stops_after_two|exact SCAN]].
Qed.

Theorem offset_alias_fallback_keeps_repeated_header fe ge locals candidate : exists after,
  exec_stmt fe ge locals lns_alias_temps lbp_two_memory
    (materialized_select(offset_multi_test loe_site)candidate loa_source) E0 after loa_final Out_normal /\
  temp_agree lns_live loa_exit after.
Proof.
  destruct(@offset_alias_full_guard_refuses fe ge locals) as [checked [GUARD [TEST ENTRY]]].
  pose proof(offset_affine_scan_entry_public(offset_multi_transfer loe_site) ENTRY) as [_ [_ [_ FRAME]]].
  destruct(@structured_execution_temp_transport fe ge locals lns_alias_temps lbp_two_memory loa_source E0 loa_exit loa_final Out_normal
    (@offset_alias_original_stops_after_two fe ge locals) lns_live checked(statement_temps loa_source)
    (@check_plan_frameable_writes _ (expression_numeric_frameable(offset_scan_numeric(offset_transfer_scan(offset_multi_transfer loe_site)))))
    (@affine_statement_scope_check_sound lns_live loa_source ltac:(vm_compute; reflexivity)) FRAME) as [after [SOURCE EXIT]].
  exists after; split; [|exact EXIT].
  apply(proj2(materialized_select_execution_exact fe ge locals lns_alias_temps lbp_two_memory(offset_multi_test loe_site)
    candidate loa_source E0 after loa_final Out_normal)).
  exists false,checked; split.
  - rewrite(proj1(@describe_materialized_check_exact _ _ _ (offset_multi_describe loe_site))); exact GUARD.
  - split; [rewrite(proj2(@describe_materialized_check_exact _ _ _ (offset_multi_describe loe_site))); exact TEST|exact SOURCE].
Qed.

Definition loe_last_state : {memory | Mem.store Mint32 lns_last 1%positive 4(Vint Int.one)=Some memory}.
Proof.
  apply Mem.valid_access_store; eapply Mem.store_valid_access_1; [exact(proj2_sig lns_last_state)|].
  eapply Mem.store_valid_access_3; exact(proj2_sig lns_last_state).
Defined.
Definition loe_last := proj1_sig loe_last_state.
Definition loe_second := PTree.set 1%positive(Vint(Int.repr 2))(PTree.set 1%positive(Vint Int.one)lns_separate_temps).
Definition loe_exit := PTree.set 1%positive(Vint(Int.repr 3))loe_second.
Lemma offset_same_block_last_bound : Mem.loadv Mint32 loe_last(Vptr 1%positive Ptrofs.zero)=Some(Vint(Int.repr 2)).
Proof.
  change(Mem.load Mint32 loe_last 1%positive 0=Some(Vint(Int.repr 2))).
  rewrite(@Mem.load_store_other Mint32 lns_last 1%positive 4(Vint Int.one)loe_last(proj2_sig loe_last_state)
    Mint32 1%positive 0 ltac:(right; left; change(0+4<=4); lia)).
  exact(proj2(proj2 same_block_bound_reads)).
Qed.

Lemma offset_same_block_original_completes fe ge locals :
  exec_stmt fe ge locals lns_separate_temps lns_initial loa_source E0 loe_exit loe_last Out_normal.
Proof.
  destruct same_block_bound_reads as [READ [FIRST LAST]].
  unfold loa_source,loaded_offset_loop,loe_exit,loe_second.
  eapply strict_iteration_encode with(body_temps:=lns_separate_temps)(body_memory:=lns_first).
  - change true with(Int.lt Int.zero(Int.add(Int.repr 2)Int.one)).
    eapply signed_expression_test_eval; [reflexivity|reflexivity|eapply signed_load_offset_eval; [reflexivity|exact READ]].
  - exists Int.zero; split; [reflexivity|change(0<2147483647); lia].
  - apply same_block_constant_body; [reflexivity|exact(proj2_sig lns_first_state)].
  - change(exec_stmt fe ge locals(PTree.set 1%positive(Vint Int.one)lns_separate_temps)lns_first
      (loaded_offset_loop 1%positive 11%positive Int.one lns_body) E0
      (PTree.set 1%positive(Vint(Int.repr 3))(PTree.set 1%positive(Vint(Int.repr 2))(PTree.set 1%positive(Vint Int.one)lns_separate_temps)))loe_last Out_normal).
    unfold loaded_offset_loop; eapply strict_iteration_encode with
      (body_temps:=PTree.set 1%positive(Vint Int.one)lns_separate_temps)(body_memory:=lns_last).
    + change true with(Int.lt Int.one(Int.add(Int.repr 2)Int.one)).
      eapply signed_expression_test_eval; [reflexivity|apply PTree.gss|eapply signed_load_offset_eval; [reflexivity|exact FIRST]].
    + exists Int.one; split; [apply PTree.gss|change(1<2147483647); lia].
    + apply same_block_constant_body; [reflexivity|exact(proj2_sig lns_last_state)].
    + change(exec_stmt fe ge locals loe_second lns_last(loaded_offset_loop 1%positive 11%positive Int.one lns_body)
        E0 loe_exit loe_last Out_normal).
      unfold loaded_offset_loop; eapply strict_iteration_encode with(body_temps:=loe_second)(body_memory:=loe_last).
      * change true with(Int.lt(Int.repr 2)(Int.add(Int.repr 2)Int.one)).
        eapply signed_expression_test_eval; [reflexivity|apply PTree.gss|eapply signed_load_offset_eval; [reflexivity|exact LAST]].
      * exists(Int.repr 2); split; [apply PTree.gss|change(2<2147483647); lia].
      * apply same_block_constant_body; [reflexivity|exact(proj2_sig loe_last_state)].
      * apply signed_expression_zero_trip_execution; change false with(Int.lt(Int.repr 3)(Int.add(Int.repr 2)Int.one)).
        eapply signed_expression_test_eval; [reflexivity|apply PTree.gss|eapply signed_load_offset_eval;
          [reflexivity|exact offset_same_block_last_bound]].
Qed.

Example offset_same_block_stability_accepts ge locals :
  offset_affine_scan_flag [2%positive] loe_proposal 11%positive Int.one(Entry ge locals lns_separate_temps lns_initial)=true.
Proof.
  unfold offset_affine_scan_flag; cbn [entry_temps entry_memory].
  change(lns_separate_temps!11%positive) with(Some(Vptr 1%positive Ptrofs.zero)); cbn -[Mem.loadv].
  rewrite(proj1 same_block_bound_reads); vm_compute; reflexivity.
Qed.
Theorem offset_same_block_cached_source_is_derived fe ge locals : exists upper cached_after,
  exec_stmt fe ge locals(PTree.set 2%positive(Vint upper)lns_separate_temps)lns_initial
    (affine_nest_source(affine_proposal_nest loe_proposal)) E0 cached_after loe_last Out_normal /\ temp_agree lns_live loe_exit cached_after.
Proof.
  destruct(@offset_affine_scan_site_execution _ _ _ _ _ _ (offset_transfer_scan(offset_multi_transfer loe_site))
    fe ge locals lns_separate_temps lns_initial _ _ (@offset_same_block_original_completes fe ge locals))
    as [checked [RUN [FRAME [FLAG PRESUMPTION]]]].
  apply offset_affine_scan_presumption_cached_source with(site:=offset_transfer_scan(offset_multi_transfer loe_site)).
  - apply PRESUMPTION; apply offset_same_block_stability_accepts.
  - apply offset_same_block_original_completes.
Qed.

Print Assumptions offset_full_multi_site_selected.
Print Assumptions offset_full_multi_wrong_offset_refused.
Print Assumptions offset_full_multi_private_cache_refused.
Print Assumptions offset_recursive_full_multi_site_selected.
Print Assumptions offset_recursive_host_progress_selected.
Print Assumptions offset_alias_numeric_phase_passes.
Print Assumptions offset_alias_stability_phase_refuses.
Print Assumptions offset_alias_full_guard_refuses.
Print Assumptions offset_alias_fallback_keeps_repeated_header.
Print Assumptions offset_same_block_last_bound.
Print Assumptions offset_same_block_original_completes.
Print Assumptions offset_same_block_stability_accepts.
Print Assumptions offset_same_block_cached_source_is_derived.
