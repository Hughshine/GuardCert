From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightNoWrap ClightRedundantSet
  ClightRectangularGuard ClightLoopSyntax ClightRegionProgress ClightPureExpr ClightProjectedExecution ClightMatrixGuard.
From GuardMemory Require Import GuardMemoryBooleanScan.
From GuardInterface Require Import ClightTensorZeroRmwPreparation ClightTensorPreparedGenerated
  ClightTensorLoadedWordFactory ClightTensorLoadedWordDriver ClightTensorRegionPackage
  ClightNestedConstantSite ClightNestedConstantHeaders ClightNestedExpressionCapture ClightTensorHeaderCapture
  ClightLiteralBoundPreparation ClightConstantBoundModel ClightCheckPlanFrame ClightExpressionHeaderCapture
  ClightNestedExpressionTransport ClightSignedExpressionProgress ClightLoadedOffsetHeader
  ClightSignedIndexedOffsetHeader ClightLoadedBoundSyntax ClightStrictLoopProgress ClightDirectWordObservation
  ClightZeroRmwCondition ClightWordArithmeticTransport ClightQuietDeterminacy ClightSharedGuard
  ClightReadonlyRewrite ClightAffineJointObservation.
From GuardInterface Require Import ClightTensorZeroRmwScanBridge.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section DRIVER.
Variables live : list ident.
Variable d : loaded_word_description.
Variable alpha : ident.
Variable static : tensor_zero_rmw_static live d alpha.
Let shape:=lwd_shape d.
Let base:=tzr_base static.
Let ports:=tensor_word_driver_ports shape live.
Let scan_live:=tensor_word_driver_scan_live shape live.
Let row:=ncs_row shape.
Let column:=ncs_column shape.
Let iterator:=ncs_iterator shape.
Let root_cache:=ncs_root_cache shape.
Let child_cache:=ncs_child_cache shape.
Let upper:=ncs_upper shape.
Let helper:=ncs_component_helper shape.
Let flag:=lwd_flag d.

Let lwd_zero_caches_private:=@ClightTensorZeroRmwScanBridge.lwd_zero_caches_private live d alpha static.
Let lwd_zero_controls_private:=@ClightTensorZeroRmwScanBridge.lwd_zero_controls_private live d alpha static.
Let lwd_zero_flag_private:=@ClightTensorZeroRmwScanBridge.lwd_zero_flag_private live d alpha static.
Let lwd_zero_private_unique:=@ClightTensorZeroRmwScanBridge.lwd_zero_private_unique live d alpha static.
Let lwd_zero_row_scope:=@ClightTensorZeroRmwScanBridge.lwd_zero_row_scope live d.
Let lwd_zero_header_private:=@ClightTensorZeroRmwScanBridge.lwd_zero_header_private live d alpha static.
Let lwd_zero_cached_scope:=@ClightTensorZeroRmwScanBridge.lwd_zero_cached_scope live d alpha static.
Let lwd_zero_helper_cached_private:=@ClightTensorZeroRmwScanBridge.lwd_zero_helper_cached_private live d alpha static.
Let lwd_zero_flag_cached_private:=@ClightTensorZeroRmwScanBridge.lwd_zero_flag_cached_private live d alpha static.

Theorem lwd_zero_shortcut_execution fe ge locals temps memory after final observers
  (receipt:ncs_observation_receipt shape(Entry ge locals temps memory)observers) :
  temps!(ncs_row shape)=Some(Vint Int.zero) -> temps!alpha=Some(Vint Int.zero) ->
  tensor_word_driver_profile_flag shape(lwd_root_cap d)(lwd_child_cap d)(Entry ge locals temps memory)=true ->
  exec_stmt fe ge locals temps memory(ncs_original shape)E0 after final Out_normal ->
  exists checked,
    exec_stmt fe ge locals temps memory(lwd_zero_shortcut d)E0 checked memory Out_normal /\
    temp_agree ports temps checked /\ checked!flag=Some(memory_boolean_word true) /\
    exists exit,exec_stmt fe ge locals checked memory(tensor_word_driver_canonical shape)E0 exit final Out_normal /\ temp_agree live after exit.
Proof.
  intros ROW ZERO PROFILE SOURCE.
  pose(prepared:=literal_bound_temps helper(Int.repr(ncs_upper shape))temps).
  pose(checked:=PTree.set flag(Vint Int.one)prepared).
  assert(PUBLIC:temp_agree ports temps checked).
  { eapply temp_agree_trans; [apply literal_bound_temps_frame; apply lwd_zero_caches_private; cbn; auto|
      apply temp_agree_set; exact lwd_zero_flag_private]. }
  assert(KEEP:temp_agree(statement_temps(tensor_word_driver_cached shape)++live)temps checked).
  { eapply temp_agree_trans; [apply literal_bound_temps_frame; exact lwd_zero_helper_cached_private|
      apply temp_agree_set; exact lwd_zero_flag_cached_private]. }
  destruct(ncs_receipt_ready receipt)as [ROOT CHILD].
  assert(ROOT_DOMAIN:register_domain(ncs_root_cache shape)(Entry ge locals temps memory)).
  { destruct ROOT as [b [o [w [_ [_ WORD]]]]]; eexists; exact WORD. }
  assert(CHILD_DOMAIN:register_domain(ncs_child_cache shape)(Entry ge locals temps memory)).
  { destruct CHILD as [b [o [w [_ [_ WORD]]]]]; eexists; exact WORD. }
  unfold tensor_word_driver_profile_flag in PROFILE; apply andb_true_iff in PROFILE as [ROOT_OK CHILD_OK].
  pose proof(proj2(@register_range_sound _ _ _ (lws_root_cap base)ROOT_DOMAIN ROOT_OK))as ROOT_RANGE.
  pose proof(proj2(@register_range_sound _ _ _ (lws_child_cap base)CHILD_DOMAIN CHILD_OK))as CHILD_RANGE.
  change(0<Int.signed(temp_word(ncs_root_cache shape)temps)<=lwd_root_cap d)in ROOT_RANGE.
  change(0<Int.signed(temp_word(ncs_child_cache shape)temps)<=lwd_child_cap d)in CHILD_RANGE.
  assert(CACHED:exec_stmt fe ge locals temps memory(tensor_word_driver_cached shape)E0 after final Out_normal).
  { eapply tensor_zero_rmw_captured_cached; [exact static|exact receipt|exact ROW|exact ZERO| | |exact SOURCE].
    all: unfold shape in ROOT_RANGE,CHILD_RANGE; lia. }
  destruct(@structured_execution_temp_transport fe ge locals temps memory(tensor_word_driver_cached shape)E0 after final
    Out_normal CACHED(statement_temps(tensor_word_driver_cached shape)++live)checked
    (statement_temps(tensor_word_driver_cached shape))(@check_plan_frameable_writes _ (lws_cached_frame base))
    ltac:(unfold statement_scope; intros id MEMBER; apply in_or_app; left; exact MEMBER)KEEP)
    as [exit [TRANSPORT EXIT]].
  assert(HELPER:checked!helper=Some(Vint(Int.repr(ncs_upper shape)))).
  { unfold checked; rewrite PTree.gso; [unfold prepared; apply PTree.gss|].
    pose proof lwd_zero_private_unique as UNIQUE; unfold lwd_private,lwd_controls in UNIQUE.
    repeat rewrite NoDup_cons_iff in UNIQUE; cbn in UNIQUE; unfold helper,flag,shape; intuition congruence. }
  exists checked; split.
  - unfold lwd_zero_shortcut; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=prepared)(m1:=memory).
    + constructor; constructor.
    + constructor; constructor.
  - split; [exact PUBLIC|split; [unfold checked; apply PTree.gss|]].
    exists exit; split.
    + unfold tensor_word_driver_canonical; eapply literal_tests_prepare_execution; [exact TRANSPORT|
        apply check_plan_frameable_writes; exact(lws_cached_frame base)|apply lwd_member_false; exact(lws_helper_cached base)|exact HELPER].
    + eapply temp_agree_weaken; [|exact EXIT]; intros id MEMBER; apply in_or_app; right; exact MEMBER.
Qed.

(** Scalar definedness comes from an actual original first RMW, after the
    positive-count gate. A zero scalar chooses the constant-time preparation;
    every other word chooses the historical source-licensed scan. *)
Theorem lwd_zero_captured_execution fe ge locals temps memory after final observers
  (receipt:ncs_observation_receipt shape(Entry ge locals temps memory)observers) :
  temps!(ncs_row shape)=Some(Vint Int.zero) ->
  tensor_word_driver_profile_flag shape(lwd_root_cap d)(lwd_child_cap d)(Entry ge locals temps memory)=true ->
  exec_stmt fe ge locals temps memory(ncs_original shape)E0 after final Out_normal ->
  exists accepted checked,
    exec_stmt fe ge locals temps memory
      (tree_statement(zero_rmw_condition alpha)(lwd_zero_shortcut d)(lwd_scan_code d))
      E0 checked memory Out_normal /\
    temp_agree ports temps checked /\ checked!flag=Some(memory_boolean_word accepted) /\
    (accepted=true -> exists exit,
      exec_stmt fe ge locals checked memory(tensor_word_driver_canonical shape)E0 exit final Out_normal /\ temp_agree live after exit).
Proof.
  intros ROW PROFILE SOURCE.
  assert(DOMAIN:register_domain alpha(Entry ge locals temps memory)).
  { eapply tensor_zero_rmw_captured_scalar; [exact static|exact receipt|exact ROW|exact PROFILE|exact SOURCE]. }
  pose proof(@register_tree_run alpha Int.zero(Entry ge locals temps memory)DOMAIN)as CONDITION.
  unfold zero_rmw_condition.
  destruct(register_flag alpha Int.zero(Entry ge locals temps memory))eqn:ZERO.
  - destruct(lwd_zero_shortcut_execution receipt ROW
      (@register_flag_evidence alpha Int.zero _ DOMAIN ZERO)PROFILE SOURCE)
      as [checked [RUN [FRAME [FLAG CANONICAL]]]].
    exists true,checked; split; [eapply decision_fragment_run; eassumption|].
    split; [exact FRAME|split; [exact FLAG|intro; exact CANONICAL]].
  - destruct(lwd_zero_existing_scan static receipt ROW PROFILE SOURCE)
      as [accepted [checked [RUN [FRAME [FLAG [HELPER ACCEPTED]]]]]].
    exists accepted,checked; split; [eapply decision_fragment_run; eassumption|].
    split; [exact FRAME|split; assumption].
Qed.

(** Source progress licenses all capture and condition reads. Refusal preserves
    the entire original temporary footprint for the literal fallback. *)
Theorem lwd_zero_driver_execution fe ge locals temps memory source_after final :
  exec_stmt fe ge locals temps memory(ncs_original shape)E0 source_after final Out_normal ->
  exists accepted checked,
    exec_stmt fe ge locals temps memory(lwd_zero_code d alpha)E0 checked memory Out_normal /\
    temp_agree ports temps checked /\ checked!flag=Some(memory_boolean_word accepted) /\
    (accepted=true -> exists exit,
      exec_stmt fe ge locals checked memory(tensor_word_driver_canonical shape)E0 exit final Out_normal /\
      temp_agree live source_after exit).
Proof.
  intro SOURCE.
  assert(ROOT_PRIVATE:~In root_cache ports)by(apply lwd_zero_caches_private; cbn; auto 10).
  assert(CHILD_PRIVATE:~In child_cache ports)by(apply lwd_zero_caches_private; cbn; auto 10).
  assert(CACHES_DISTINCT:root_cache<>child_cache).
  { pose proof lwd_zero_private_unique as UNIQUE; unfold lwd_private in UNIQUE.
    repeat rewrite NoDup_cons_iff in UNIQUE; cbn in UNIQUE.
    unfold root_cache,child_cache,shape; intuition congruence. }
  destruct(@signed_expression_completed_header fe ge locals temps memory row
    (signed_load_offset(ncs_pointer shape)(ncs_delta shape))
    (nested_expression_body column(signed_indexed_offset(ncs_pointer shape)(ncs_index shape)(ncs_child_delta shape))
      (constant_body_source iterator(Int.repr upper)(ncs_leaf shape)))E0 source_after final Out_normal SOURCE)
    as [initial_flag TEST].
  destruct(@signed_expression_test_facts ge locals temps memory row
    (signed_load_offset(ncs_pointer shape)(ncs_delta shape))initial_flag eq_refl TEST)
    as [counter [bound [COUNTER _]]].
  assert(ROW_DOMAIN:register_domain row(Entry ge locals temps memory))by(exists counter; exact COUNTER).
  pose proof(@register_tree_run row Int.zero(Entry ge locals temps memory)ROW_DOMAIN)as START_RUN.
  unfold lwd_zero_code; fold shape flag.
  destruct(register_flag row Int.zero(Entry ge locals temps memory))eqn:START.
  - assert(ROW:temps!row=Some(Vint Int.zero))by(exact(@register_flag_evidence row Int.zero _ ROW_DOMAIN START)).
    destruct(@tensor_header_capture_execution fe ge locals shape live temps memory source_after final
      ltac:(unfold shape; rewrite(lws_leaf base); reflexivity)(lws_original_frame base) ROOT_PRIVATE CHILD_PRIVATE CACHES_DISTINCT lwd_zero_header_private SOURCE)
      as [root_word [child [prepared_after [CAPTURE [PREPARED [PUBLIC CHILD]]]]]].
    pose(captured:=tensor_header_captured shape temps root_word child).
    assert(CAPTURE_FRAME:temp_agree ports temps captured)by(apply nested_expression_captured_frame; assumption).
    assert(CACHE:captured!root_cache=Some(Vint root_word))by(apply nested_expression_captured_root; exact CACHES_DISTINCT).
    assert(ROOT_DOMAIN:register_domain root_cache(Entry ge locals captured memory))by(exists root_word; exact CACHE).
    assert(CHILD_DOMAIN:register_range_flag root_cache (lwd_root_cap d)(Entry ge locals captured memory)=true ->
      register_domain child_cache(Entry ge locals captured memory)).
    { intro ACTIVE; destruct child as [child_word|].
      - exists child_word; apply nested_expression_captured_child.
      - unfold register_range_flag in ACTIVE; apply andb_true_iff in ACTIVE as [POS _].
        change(Int.lt Int.zero(temp_word root_cache captured)=true)in POS.
        unfold temp_word in POS; rewrite CACHE in POS.
        change(Int.lt(temp_word row temps)root_word=false)in CHILD.
        unfold temp_word in CHILD; rewrite ROW in CHILD; congruence. }
    pose proof(@tensor_word_driver_profile_run shape (lwd_root_cap d) (lwd_child_cap d)(Entry ge locals captured memory)
      ROOT_DOMAIN CHILD_DOMAIN)as PROFILE_RUN.
    destruct(tensor_word_driver_profile_flag shape (lwd_root_cap d) (lwd_child_cap d)(Entry ge locals captured memory))eqn:PROFILE.
    + assert(CHILD_SOME:exists child_word,child=Some child_word).
      { destruct child as [child_word|]; [eauto|].
        unfold tensor_word_driver_profile_flag,register_range_flag in PROFILE.
        repeat rewrite andb_true_iff in PROFILE; destruct PROFILE as [[POS _] _].
        change(Int.lt Int.zero(temp_word root_cache captured)=true)in POS.
        unfold temp_word in POS; rewrite CACHE in POS.
        change(Int.lt(temp_word row temps)root_word=false)in CHILD.
        unfold temp_word in CHILD; rewrite ROW in CHILD; congruence. }
      destruct CHILD_SOME as [child_word SAME]; subst child; destruct CHILD as [_ [observers RECEIPT]].
      destruct(lwd_zero_captured_execution RECEIPT
        ltac:(rewrite CAPTURE_FRAME by exact lwd_zero_row_scope; exact ROW)PROFILE PREPARED)
        as [accepted [checked [SCAN [SCAN_FRAME [FLAG ACCEPTED]]]]].
      exists accepted,checked; split.
      * eapply decision_fragment_run; [exact START_RUN|].
        eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact CAPTURE|].
        eapply decision_fragment_run; [exact PROFILE_RUN|exact SCAN].
      * split; [eapply temp_agree_trans; eassumption|split; [exact FLAG|]].
        intro ACCEPT; destruct(ACCEPTED ACCEPT)as [exit [CANONICAL EXIT]]; exists exit; split; [exact CANONICAL|].
        eapply temp_agree_trans; [eapply temp_agree_weaken; [exact(@tensor_word_driver_ports_live shape live)|exact PUBLIC]|exact EXIT].
    + exists false,(PTree.set flag(Vint Int.zero)captured); split.
      * eapply decision_fragment_run; [exact START_RUN|].
        eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact CAPTURE|].
        eapply decision_fragment_run; [exact PROFILE_RUN|constructor; constructor].
      * split; [eapply temp_agree_trans; [exact CAPTURE_FRAME|apply temp_agree_set; exact lwd_zero_flag_private]|].
        split; [apply PTree.gss|discriminate].
  - exists false,(PTree.set flag(Vint Int.zero)temps); split.
    + eapply decision_fragment_run; [exact START_RUN|constructor; constructor].
    + split; [apply temp_agree_set; exact lwd_zero_flag_private|split; [apply PTree.gss|discriminate]].
Qed.

Definition lwd_zero_preparation_certificate : tensor_preparation_certificate live
  (ncs_original shape)(tensor_word_driver_canonical shape)(lwd_zero_code d alpha)flag.
Proof.
  refine(@TensorPreparationCertificate live(ncs_original shape)(tensor_word_driver_canonical shape)
    (lwd_zero_code d alpha)flag(lws_original_frame base)(lws_canonical_frame base)
    lwd_zero_flag_private _).
  exact lwd_zero_driver_execution.
Defined.
End DRIVER.

Print Assumptions lwd_zero_shortcut_execution.
Print Assumptions lwd_zero_captured_execution.

Print Assumptions lwd_zero_driver_execution.
Print Assumptions lwd_zero_preparation_certificate.
