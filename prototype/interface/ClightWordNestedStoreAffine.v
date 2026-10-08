(** Actual header-guard exit to checked multi-array affine candidate execution.
    Empty outer acceptance bypasses preparation that could read an absent child
    cache.  The domain producer exports a region guarantee to the existing host. *)
From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightNoWrap
  ClightLoopSyntax ClightCountedLoop ClightRectangularLoops ClightGuard ClightGuardProof ClightPrivateRegion ClightProjectedExecution
  ClightMemorySteps CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemoryBooleanScan GuardMemoryMultiTensorSequence.
From GuardInterface Require Import ClightWordStoreSequenceFactory ClightWordStoreSequenceGuard
  ClightWordStoreNestedGuard ClightWordNestedStoreFactory ClightWordNestedStoreDataEntry
  ClightNestedExpressionCapture ClightNestedExpressionTransport ClightNestedLoadedOffset
  ClightStrictLoopProgress ClightSignedExpressionProgress ClightCheckPlanFrame ClightSharedGuard
  ClightMultiTensorDataPackage ClightMultiTensorAffineFactory.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

Definition nwsp_guard_code source public pool (package : word_nested_store_package source public pool) :=
  let d:=nwsp_description package in let a:=nwsp_allocation package in
  word_store_nested_guard_code (nws_row d) (nwa_cache a) (nws_pointer d) (nws_delta d)
    (nws_column d) (nwa_child_cache a) (nws_child_pointer d) (nws_child_delta d)
    (nwa_row_cursor a) (nwa_row_limit a) (nwa_column_cursor a) (nwa_column_limit a) (nwa_flag a)
    (nws_rename a) (wsbody_sites (nwsp_body package)).
Definition nwsp_guard_result source public pool (package : word_nested_store_package source public pool) entry :=
  let d:=nwsp_description package in let a:=nwsp_allocation package in
  word_store_nested_guard_result (nws_row d) (nwa_cache a) (nwa_child_cache a)
    (nwa_row_cursor a) (nwa_column_cursor a) (nws_rename a) (wsbody_sites (nwsp_body package))
    (nws_pointer d) (nws_child_pointer d) entry.
Definition nwsp_captured source public pool (package : word_nested_store_package source public pool) temps upper child :=
  let a:=nwsp_allocation package in nested_expression_captured (nwa_cache a) (nwa_child_cache a) temps upper child.

Definition nwsp_guard_receipt source public pool (package : word_nested_store_package source public pool)
    fe ge locals temps memory source_after final upper child prepared_after checked_after :=
  let captured:=Entry ge locals (nwsp_captured package temps upper child) memory in
  exec_stmt fe ge locals (entry_temps captured) memory source E0 prepared_after final Out_normal /\
  temp_agree public source_after prepared_after /\
  exec_stmt fe ge locals temps memory (nwsp_guard_code package) E0 checked_after memory Out_normal /\
  temp_agree (nws_scan_live (nwsp_allocation package)) (entry_temps captured) checked_after /\
  temp_agree public temps checked_after /\
  checked_after!(nwa_flag (nwsp_allocation package))=Some (memory_boolean_word (nwsp_guard_result package captured)) /\
  (nwsp_guard_result package captured=true -> exists cached_after,
    exec_stmt fe ge locals checked_after memory (nws_cached (nwsp_allocation package))
      E0 cached_after final Out_normal /\ temp_agree public source_after cached_after).

Theorem nwsp_guard_execution source public pool (package : word_nested_store_package source public pool)
    fe ge locals temps memory source_after final :
  exec_stmt fe ge locals temps memory source E0 source_after final Out_normal ->
  exists upper child prepared_after checked_after,
    nwsp_guard_receipt package fe ge locals temps memory source_after final upper child prepared_after checked_after.
Proof.
  intro SOURCE; rewrite (nwsp_source package) in SOURCE.
  pose (d:=nwsp_description package); pose (a:=nwsp_allocation package).
  pose (checked:=nwsp_body package); pose (STATIC:=nwsp_static package).
  pose proof (nwst_coordinates STATIC) as DISTINCT.
  edestruct (@word_store_nested_guard_execution fe (nws_row d) (nwa_cache a) (nws_pointer d)
    (nws_column d) (nwa_child_cache a) (nws_child_pointer d) (nwa_row_cursor a) (nwa_row_limit a)
    (nwa_column_cursor a) (nwa_column_limit a) (nwa_flag a) (nws_delta d) (nws_child_delta d)
    (nws_body d) checked (nws_stable a) (nws_scan_live a) public (nws_rename a))
    with (ge:=ge) (locals:=locals) (temps:=temps) (memory:=memory)
      (source_after:=source_after) (final:=final)
    as [upper [child [prepared_after [checked_after [CAPTURE [PREPARED [ROOT [CHILD
      [PUBLIC [GUARD [FRAME [INITIAL [FLAG CACHED]]]]]]]]]]]]].
  all: try solve [exact SOURCE|apply nws_stable_live|apply nws_public_live|
    apply nwa_controls_unique|apply nws_rename_stable|exact DISTINCT|
    exact (nwst_cached_scope STATIC)|exact (nwst_site_pointers STATIC)|exact (nwst_site_indices STATIC)|
    exact (nwst_controls STATIC)|apply nwa_caches_distinct].
  all: try solve [apply (nwst_members STATIC); cbn; tauto].
  all: try solve [eapply nws_coordinate_private; cbn; tauto].
  all: try solve [eapply (@nwa_private_fresh (nws_source d) public pool a);
    unfold nwa_private; cbn; tauto].
  all: try solve [exact (@nws_rename_row d public pool a)|exact (@nws_rename_column d public pool a DISTINCT)].
  exists upper,child,prepared_after,checked_after.
  unfold nwsp_guard_receipt,nwsp_guard_code,nwsp_guard_result,nwsp_captured;
    fold d a checked; rewrite (nwsp_source package).
  repeat split; assumption.
Qed.

Lemma nwsp_original_frameable source public pool (package : word_nested_store_package source public pool) :
  check_plan_frameable source=true.
Proof.
  rewrite (nwsp_source package); unfold nws_source,nested_loaded_offset_source,
    nested_expression_source,nested_expression_body,strict_frontend_loop.
  cbn [check_plan_frameable rectangle_reset counter_increment].
  rewrite (@word_store_structured_frameable [] (nws_body (nwsp_description package))
    (wsbody_writes (nwsp_body package))); reflexivity.
Qed.

Definition nwspp_affine_target source public pool
    (package : word_nested_store_polyhedral_package source public pool) candidate :=
  let header:=nwspp_header package in let a:=nwsp_allocation header in
  Ssequence (nwsp_guard_code header)
    (Sifthenelse (shared_guard_choice (nwa_flag a))
      (Sifthenelse (word_store_positive_test (nwa_cache a)) candidate (nws_cached a)) source).

Theorem nwspp_affine_execution source public pool
    (package : word_nested_store_polyhedral_package source public pool) proposal candidate
    fe ge locals temps memory source_after final :
  mayReturn (check_multi_tensor_affine_package_full (nwspp_model package) public
    (nwa_candidate_pool (nwsp_allocation (nwspp_header package))) proposal) (Some candidate) ->
  exec_stmt fe ge locals temps memory source E0 source_after final Out_normal ->
  exists after, exec_stmt fe ge locals temps memory (nwspp_affine_target package candidate)
    E0 after final Out_normal /\ temp_agree public source_after after.
Proof.
  intros CHECK SOURCE; pose (header:=nwspp_header package); pose (a:=nwsp_allocation header).
  destruct (@nwsp_guard_execution source public pool header fe ge locals temps memory source_after final SOURCE)
    as [upper [child [prepared_after [checked_after RECEIPT]]]].
  unfold nwsp_guard_receipt in RECEIPT; fold a in RECEIPT.
  destruct RECEIPT as [PREPARED [PUBLIC [GUARD [FRAME [INITIAL [FLAG CACHED]]]]]].
  set (captured:=Entry ge locals (nwsp_captured header temps upper child) memory) in *.
  set (accepted:=nwsp_guard_result header captured) in *.
  assert (FLAG_TEST : expression_test (shared_guard_choice (nwa_flag a)) (Entry ge locals checked_after memory) accepted).
  { apply shared_guard_choice_test; exact FLAG. }
  assert (ROOT_WORD : checked_after!(nwa_cache a)=Some (Vint upper)).
  { rewrite FRAME by (unfold nws_scan_live; apply in_eq).
    unfold nwsp_captured; fold a; apply nested_expression_captured_root; apply nwa_caches_distinct. }
  assert (POSITIVE_TEST : expression_test (word_store_positive_test (nwa_cache a))
    (Entry ge locals checked_after memory) (Int.lt Int.zero upper)).
  { apply word_store_positive_test_execution; exact ROOT_WORD. }
  destruct accepted eqn:ACCEPT.
  - destruct (CACHED eq_refl) as [cached_after [CACHED_RUN CACHED_PUBLIC]].
    assert (BRANCH : exists after,
      exec_stmt fe ge locals checked_after memory
        (if Int.lt Int.zero upper then candidate else nws_cached a) E0 after final Out_normal /\
        temp_agree public source_after after).
    { destruct (Int.lt Int.zero upper).
      - destruct (@check_multi_tensor_affine_package_full_execution _ (nwspp_model package) public
          (nwa_candidate_pool a) proposal candidate fe ge locals checked_after memory cached_after final
          CHECK CACHED_RUN) as [after [RUN EXIT]].
        exists after; split; [exact RUN|eapply temp_agree_trans; eassumption].
      - exists cached_after; split; assumption. }
    destruct BRANCH as [after [RUN EXIT]]; exists after; split; [|exact EXIT].
    unfold nwspp_affine_target; fold header a; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [exact GUARD|].
    eapply word_store_if_test_execution; [exact FLAG_TEST|].
    eapply word_store_if_test_execution; [exact POSITIVE_TEST|exact RUN].
  - assert (SCOPE : statement_scope (nws_scan_live a) source).
    { rewrite (nwsp_source header); apply nws_original_scope. }
    destruct (@structured_execution_temp_transport fe ge locals (entry_temps captured) memory source
      E0 prepared_after final Out_normal PREPARED (nws_scan_live a) checked_after (statement_temps source)
      (@check_plan_frameable_writes source (nwsp_original_frameable header)) SCOPE FRAME)
      as [after [RUN EXIT]].
    exists after; split.
    + unfold nwspp_affine_target; fold header a; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [exact GUARD|].
      eapply word_store_if_test_execution; [exact FLAG_TEST|exact RUN].
    + eapply temp_agree_trans; [exact PUBLIC|eapply temp_agree_weaken; [apply nws_public_live|exact EXIT]].
Qed.

Theorem nwspp_affine_contract source public pool
    (package : word_nested_store_polyhedral_package source public pool) proposal candidate :
  mayReturn (check_multi_tensor_affine_package_full (nwspp_model package) public
    (nwa_candidate_pool (nwsp_allocation (nwspp_header package))) proposal) (Some candidate) ->
  PrivateRegion.projected_region_contract public source (nwspp_affine_target package candidate).
Proof.
  intros CHECK temps p locals le current memory after final SCOPE AGREE SOURCE fn continuation.
  destruct (@structured_execution_temp_transport (adapter_entry temps) (globalenv p) locals le memory
    source E0 after final Out_normal SOURCE public current (statement_temps source)
    (@check_plan_frameable_writes source (nwsp_original_frameable (nwspp_header package))) SCOPE AGREE)
    as [middle [ORIGINAL PUBLIC]].
  destruct (@nwspp_affine_execution source public pool package proposal candidate
    (adapter_entry temps) (globalenv p) locals current memory middle final CHECK ORIGINAL)
    as [exit [RUN EXIT_PUBLIC]].
  destruct (exec_stmt_steps (adapter_entry temps) p _ _ _ _ _ _ _ _ RUN fn continuation)
    as [finish [STEPS EXIT]].
  inversion EXIT; subst finish; exists exit,final; split; [exact STEPS|split].
  - eapply temp_agree_trans; [exact PUBLIC|exact EXIT_PUBLIC].
  - apply memory_equivalent_refl.
Qed.

Definition word_nested_store_description_proposer := statement -> option word_nested_store_description.
Definition check_word_nested_store_affine_region public typed_pool
    (describe : word_nested_store_description_proposer)
    (describe_cached : multi_tensor_affine_description_proposer)
    (propose : multi_tensor_affine_candidate_proposer) source :=
  match describe source with
  | Some d=>match check_word_nested_store_data_polyhedral_source source public typed_pool d describe_cached with
    | Some package=>match propose (map mt_instruction (mtr_items (nwspp_model package))) with
      | Some proposal=>
        BIND candidate <- check_multi_tensor_affine_package_full (nwspp_model package) public
          (nwa_candidate_pool (nwsp_allocation (nwspp_header package))) proposal -;
        pure (match candidate with Some candidate=>Some (nwspp_affine_target package candidate)|None=>None end)
      | None=>pure None end
    | None=>pure None end
  | None=>pure None end.

Theorem check_word_nested_store_affine_region_contract public typed_pool describe describe_cached propose source target :
  mayReturn (check_word_nested_store_affine_region public typed_pool describe describe_cached propose source) (Some target) ->
  PrivateRegion.projected_region_contract public source target.
Proof.
  unfold check_word_nested_store_affine_region.
  destruct (describe source) as [d|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (check_word_nested_store_data_polyhedral_source source public typed_pool d describe_cached) as [package|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (propose (map mt_instruction (mtr_items (nwspp_model package)))) as [proposal|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN candidate CHECK; apply mayReturn_pure in RUN.
  destruct candidate as [code|]; [|discriminate]; inversion RUN; subst target.
  eapply nwspp_affine_contract; exact CHECK.
Qed.

Fixpoint checked_word_nested_store_affine_regions public typed_pool describe describe_cached propose sources :=
  match sources with
  | []=>pure []
  | source::rest=>
    BIND target <- check_word_nested_store_affine_region public typed_pool describe describe_cached propose source -;
    BIND table <- checked_word_nested_store_affine_regions public typed_pool describe describe_cached propose rest -;
    pure (match target with Some target=>(source,target)::table|None=>table end)
  end.
Theorem checked_word_nested_store_affine_regions_sound public typed_pool describe describe_cached propose sources table :
  mayReturn (checked_word_nested_store_affine_regions public typed_pool describe describe_cached propose sources) table ->
  Forall (fun pair=>PrivateRegion.projected_region_contract public (fst pair) (snd pair)) table.
Proof.
  revert table; induction sources as [|source sources IH]; intros table RUN; cbn in RUN.
  - apply mayReturn_pure in RUN; subst; constructor.
  - bind_imp_destruct RUN target CHECK; bind_imp_destruct RUN rest REST; apply mayReturn_pure in RUN.
    destruct target; subst;
      [constructor; [eapply check_word_nested_store_affine_region_contract; exact CHECK|]|]; apply IH; exact REST.
Qed.

Print Assumptions nwsp_guard_execution.
Print Assumptions nwsp_original_frameable.
Print Assumptions nwspp_affine_execution.
Print Assumptions nwspp_affine_contract.
Print Assumptions check_word_nested_store_affine_region_contract.
Print Assumptions checked_word_nested_store_affine_regions_sound.
