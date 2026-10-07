From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightNoWrap
  ClightRedundantSet ClightRectangularGuard ClightCountedLoop ClightPureExpr ClightFrontendLoopProtocol
  ClightProjectedExecution ClightMatrixGuard ClightRegionProgress ClightPrivateRegion CompCertMemoryEquivalence ClightGuard.
From GuardMemory Require Import GuardMemoryBooleanScan.
From GuardInterface Require Import ClightTensorHeaderCapture ClightTensorWordOuterHeaders
  ClightNestedConstantSite ClightNestedConstantHeaders ClightNestedExpressionCapture
  ClightNestedExpressionTransport ClightConstantBoundModel ClightLiteralBoundPreparation
  ClightLoadedOffsetHeader ClightSignedIndexedOffsetHeader ClightLoadedBoundSyntax ClightAffineJointObservation
  ClightObservedHeaderPrefix ClightExpressionHeaderCapture ClightCheckPlanFrame
  ClightQuietDeterminacy ClightWordArithmeticTransport ClightDirectWordObservation
  ClightStrictLoopProgress ClightSignedExpressionProgress ClightTensorRegionPackage
  ClightTensorRegionPreservation ClightTensorGeneratedCandidates ClightReadonlyRewrite
  ClightSharedGuard ClightCheckPlan ClightStagedCheck ClightReadonlyTreeFacts GuardedRewrite.
From polcert.lib Require Import ImpureAlarmConfig.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition tensor_word_driver_ports shape live := statement_temps(ncs_original shape)++live.
Definition tensor_word_driver_scan_live shape live :=
  ncs_component_helper shape::ncs_root_cache shape::ncs_child_cache shape::tensor_word_driver_ports shape live.
Definition tensor_word_driver_cached shape := nested_cached_source(ncs_row shape)(ncs_root_cache shape)
  (ncs_column shape)(ncs_child_cache shape)
  (constant_body_source(ncs_iterator shape)(Int.repr(ncs_upper shape))(ncs_leaf shape)).
Definition tensor_word_driver_canonical shape := literal_tests_prepare(ncs_component_helper shape)
  (Int.repr(ncs_upper shape))(tensor_word_driver_cached shape).
Definition tensor_word_driver_profile_tree shape root_cap child_cap :=
  decision_bind(register_range_tree(ncs_root_cache shape)root_cap)
    (register_range_tree(ncs_child_cache shape)child_cap)(Decision false).
Definition tensor_word_driver_profile_flag shape root_cap child_cap entry :=
  register_range_flag(ncs_root_cache shape)root_cap entry &&
  register_range_flag(ncs_child_cache shape)child_cap entry.
Definition tensor_word_driver_refuse flag := Sset flag(Econst_int Int.zero type_int32s).
Definition tensor_word_driver_scan shape pointer row_cursor row_limit column_cursor column_limit
    component_cursor component_limit flag index rename :=
  Ssequence(literal_bound_set(ncs_component_helper shape)(Int.repr(ncs_upper shape)))
    (tensor_word_header_scan shape pointer row_cursor row_limit column_cursor column_limit
      component_cursor component_limit flag index rename).
Definition tensor_word_driver_code shape pointer row_cursor row_limit column_cursor column_limit
    component_cursor component_limit flag index rename root_cap child_cap :=
  tree_statement(register_tree(ncs_row shape)Int.zero)
    (Ssequence(tensor_header_capture shape)
      (tree_statement(tensor_word_driver_profile_tree shape root_cap child_cap)
        (tensor_word_driver_scan shape pointer row_cursor row_limit column_cursor column_limit
          component_cursor component_limit flag index rename)(tensor_word_driver_refuse flag)))
    (tensor_word_driver_refuse flag).

Definition tensor_word_driver_complete_check shape(package:tensor_region_package(tensor_word_driver_canonical shape))
    driver flag := Ssequence driver
  (Sifthenelse(shared_guard_choice flag)(shared_guard_code(tensor_region_guard package)flag)Sskip).
Definition tensor_word_driver_generated_target shape(package:tensor_region_package(tensor_word_driver_canonical shape))
    driver flag code := Ssequence(tensor_word_driver_complete_check package driver flag)
  (Sifthenelse(shared_guard_choice flag)(tensor_region_branch package code)(ncs_original shape)).

(** Only the header pointer and the two cached words occur in this receipt's
    runtime observations. Private helper initialization can transport it. *)
Theorem tensor_word_driver_receipt_transport shape ge locals memory before current observers :
  ncs_observation_receipt shape(Entry ge locals before memory)observers ->
  temp_agree[ncs_pointer shape;ncs_root_cache shape;ncs_child_cache shape]before current ->
  ncs_observation_receipt shape(Entry ge locals current memory)observers.
Proof.
  intros RECEIPT FRAME; constructor.
  - destruct(ncs_receipt_ready RECEIPT)as [ROOT CHILD]; split.
    + destruct ROOT as [block [offset [raw [POINTER [READ CACHE]]]]].
      exists block,offset,raw; cbn [entry_temps entry_memory] in *; split; [rewrite FRAME by(cbn; auto); exact POINTER|].
      split; [exact READ|rewrite FRAME by(cbn; auto); exact CACHE].
    + destruct CHILD as [block [offset [raw [POINTER [READ CACHE]]]]].
      exists block,offset,raw; cbn [entry_temps entry_memory] in *; split; [rewrite FRAME by(cbn; auto); exact POINTER|].
      split; [exact READ|rewrite FRAME by(cbn; auto); exact CACHE].
  - apply Forall_forall; intros observer MEMBER.
    eapply word_observer_receipt_frame with(live:=[ncs_pointer shape;ncs_root_cache shape;ncs_child_cache shape]).
    + pose proof(ncs_receipt_reads RECEIPT)as READS.
      rewrite Forall_forall in READS; exact(READS observer MEMBER).
    + apply tensor_word_header_observer_scope with(receipt:=RECEIPT); [cbn; auto|exact MEMBER].
    + exact FRAME.
  - exact(ncs_receipt_addresses RECEIPT).
  - rewrite(ncs_receipt_snapshots RECEIPT).
    unfold ncs_observations,loaded_offset_observations,indexed_offset_observations;
      cbn [entry_temps entry_memory]; rewrite FRAME by(cbn; auto); reflexivity.
  - exact(ncs_receipt_initial RECEIPT).
Qed.

Lemma tensor_word_driver_profile_run shape root_cap child_cap entry :
  register_domain(ncs_root_cache shape)entry ->
  (register_range_flag(ncs_root_cache shape)root_cap entry=true -> register_domain(ncs_child_cache shape)entry) ->
  decision_run entry(tensor_word_driver_profile_tree shape root_cap child_cap)
    (tensor_word_driver_profile_flag shape root_cap child_cap entry).
Proof.
  intros ROOT CHILD; unfold tensor_word_driver_profile_tree,tensor_word_driver_profile_flag.
  pose proof(register_range_tree_run root_cap ROOT)as RUN.
  destruct(register_range_flag(ncs_root_cache shape)root_cap entry)eqn:ACCEPT.
  - eapply decision_bind_run; [exact RUN|apply register_range_tree_run; apply CHILD; reflexivity].
  - eapply decision_bind_run; [exact RUN|constructor].
Qed.

Theorem tensor_word_driver_profile_root_refusal fe ge locals temps memory shape root_cap child_cap flag next :
  register_domain(ncs_root_cache shape)(Entry ge locals temps memory) ->
  register_range_flag(ncs_root_cache shape)root_cap(Entry ge locals temps memory)=false ->
  exec_stmt fe ge locals temps memory
    (tree_statement(tensor_word_driver_profile_tree shape root_cap child_cap)next(tensor_word_driver_refuse flag))
    E0(PTree.set flag(Vint Int.zero)temps)memory Out_normal.
Proof.
  intros DOMAIN REFUSE; eapply decision_fragment_run.
  - apply tensor_word_driver_profile_run; [exact DOMAIN|intro ACCEPT; congruence].
  - unfold tensor_word_driver_profile_flag; rewrite REFUSE; cbn; constructor; constructor.
Qed.

Theorem tensor_word_driver_start_refusal fe ge locals temps memory shape pointer row_cursor row_limit column_cursor column_limit
    component_cursor component_limit flag index rename root_cap child_cap :
  register_domain(ncs_row shape)(Entry ge locals temps memory) ->
  register_flag(ncs_row shape)Int.zero(Entry ge locals temps memory)=false ->
  exec_stmt fe ge locals temps memory
    (tensor_word_driver_code shape pointer row_cursor row_limit column_cursor column_limit
      component_cursor component_limit flag index rename root_cap child_cap)
    E0(PTree.set flag(Vint Int.zero)temps)memory Out_normal.
Proof.
  intros DOMAIN REFUSE; unfold tensor_word_driver_code; eapply decision_fragment_run with(b:=false).
  - rewrite <-REFUSE; apply register_tree_run; exact DOMAIN.
  - constructor; constructor.
Qed.

Section DRIVER.
Variable shape : nested_constant_shape.
Variables pointer row_cursor row_limit column_cursor column_limit component_cursor component_limit flag : ident.
Variables index rhs : expr.
Variable rename : ident -> ident.
Variables stable live : list ident.
Variables root_cap child_cap : Z.
Let ports:=tensor_word_driver_ports shape live.
Let scan_live:=tensor_word_driver_scan_live shape live.
Let row:=ncs_row shape.
Let column:=ncs_column shape.
Let iterator:=ncs_iterator shape.
Let root_cache:=ncs_root_cache shape.
Let child_cache:=ncs_child_cache shape.
Let helper:=ncs_component_helper shape.
Let upper:=ncs_upper shape.
Let inner_live:=row_cursor::row_limit::scan_live.
Let component_live:=column_cursor::column_limit::inner_live.
Hypothesis LEAF : ncs_leaf shape=direct_word_store pointer index rhs.
Hypothesis WORD : word_arithmetic index.
Hypotheses (NONNEGATIVE : 0<=upper) (UPPER : signed_range upper)
  (ROOT_CAP : signed_range root_cap) (CHILD_CAP : signed_range child_cap).
Hypotheses (FRAMEABLE : check_plan_frameable(ncs_original shape)=true)
  (CACHED_FRAMEABLE : check_plan_frameable(tensor_word_driver_cached shape)=true)
  (CACHED_SCOPE : incl(statement_temps(tensor_word_driver_cached shape))scan_live)
  (CACHED_HELPER_PRIVATE : ~In helper(statement_temps(tensor_word_driver_cached shape))).
Hypotheses (ROOT_PRIVATE : ~In root_cache ports) (CHILD_PRIVATE : ~In child_cache ports)
  (HELPER_PRIVATE : ~In helper ports) (CACHES_DISTINCT : root_cache<>child_cache)
  (HELPER_ROOT : helper<>root_cache) (HELPER_CHILD : helper<>child_cache)
  (CHILD_HEADER_PRIVATE : column<>ncs_pointer shape).
Hypotheses (HELPER : In helper stable) (ROOT_STABLE : In root_cache stable) (CHILD_STABLE : In child_cache stable)
  (POINTER_STABLE : In pointer stable) (HEADER_STABLE : In(ncs_pointer shape)stable) (STABLE_LIVE : incl stable scan_live).
Hypotheses (ROW_PRIVATE : ~In row stable) (COLUMN_PRIVATE : ~In column stable) (ITERATOR_PRIVATE : ~In iterator stable)
  (ROW_COLUMN : row<>column) (ITERATOR_ROW : iterator<>row) (ITERATOR_COLUMN : iterator<>column).
Hypothesis SOURCE_SCOPE : incl(expression_temps index)(iterator::column::row::stable).
Hypotheses (RENAME_ITERATOR : rename iterator=component_cursor) (RENAME_COLUMN : rename column=column_cursor)
  (RENAME_ROW : rename row=row_cursor).
Hypothesis RENAME_STABLE : forall id,In id stable -> rename id=id.
Hypotheses (ROW_CURSOR_PRIVATE : ~In row_cursor scan_live) (ROW_LIMIT_PRIVATE : ~In row_limit scan_live)
  (COLUMN_CURSOR_PRIVATE : ~In column_cursor inner_live) (COLUMN_LIMIT_PRIVATE : ~In column_limit inner_live)
  (FLAG_PRIVATE : ~In flag inner_live) (COMPONENT_CURSOR_PRIVATE : ~In component_cursor component_live)
  (COMPONENT_LIMIT_PRIVATE : ~In component_limit component_live).
Hypotheses (ROW_CONTROLS : row_cursor<>row_limit) (ROW_CURSOR_FLAG : row_cursor<>flag) (ROW_LIMIT_FLAG : row_limit<>flag)
  (COLUMN_CONTROLS : column_cursor<>column_limit) (COLUMN_CURSOR_FLAG : column_cursor<>flag) (COLUMN_LIMIT_FLAG : column_limit<>flag)
  (COMPONENT_CONTROLS : component_cursor<>component_limit) (COMPONENT_CURSOR_FLAG : component_cursor<>flag)
  (COMPONENT_LIMIT_FLAG : component_limit<>flag).

Lemma tensor_word_driver_ports_scan : incl ports scan_live.
Proof. intros id MEMBER; unfold scan_live,tensor_word_driver_scan_live; right; right; right; exact MEMBER. Qed.
Lemma tensor_word_driver_ports_live : incl live ports.
Proof. unfold ports,tensor_word_driver_ports; intros id MEMBER; apply in_or_app; right; exact MEMBER. Qed.
Lemma tensor_word_driver_flag_private : ~In flag ports.
Proof. intro MEMBER; apply FLAG_PRIVATE; right; right; apply tensor_word_driver_ports_scan; exact MEMBER. Qed.
Lemma tensor_word_driver_row_scope : In row ports.
Proof.
  unfold ports,tensor_word_driver_ports,ncs_original,nested_expression_source,strict_frontend_loop,signed_expression_test;
    cbn [statement_temps expression_temps]; repeat rewrite in_app_iff; cbn; tauto.
Qed.
Lemma tensor_word_driver_header_scope : In(ncs_pointer shape)ports.
Proof.
  unfold ports,tensor_word_driver_ports,ncs_original,nested_expression_source,strict_frontend_loop,signed_expression_test,
    signed_load_offset,signed_load; cbn [statement_temps expression_temps]; repeat rewrite in_app_iff; cbn; tauto.
Qed.

(** The accepted count gates license the complete scan. No caller initializes
    the helper, supplies cached-source completion, or supplies header laws. *)
Theorem tensor_word_driver_captured_scan fe ge locals captured memory source_after final observers
    (receipt:ncs_observation_receipt shape(Entry ge locals captured memory)observers) :
  captured!row=Some(Vint Int.zero) ->
  tensor_word_driver_profile_flag shape root_cap child_cap(Entry ge locals captured memory)=true ->
  exec_stmt fe ge locals captured memory(ncs_original shape)E0 source_after final Out_normal ->
  exists accepted checked,
    exec_stmt fe ge locals captured memory
      (tensor_word_driver_scan shape pointer row_cursor row_limit column_cursor column_limit
        component_cursor component_limit flag index rename)E0 checked memory Out_normal /\
    temp_agree ports captured checked /\ checked!flag=Some(memory_boolean_word accepted) /\
    checked!helper=Some(Vint(Int.repr upper)) /\
    (accepted=true -> exists exit,
      exec_stmt fe ge locals checked memory(tensor_word_driver_canonical shape)E0 exit final Out_normal /\
      temp_agree live source_after exit).
Proof.
  intros ROW PROFILE SOURCE.
  pose(prepared:=literal_bound_temps helper(Int.repr upper)captured).
  assert(PREPARED_FRAME:temp_agree ports captured prepared)by(apply literal_bound_temps_frame; exact HELPER_PRIVATE).
  destruct(@structured_execution_temp_transport fe ge locals captured memory(ncs_original shape)E0 source_after final Out_normal
    SOURCE ports prepared(statement_temps(ncs_original shape))(@check_plan_frameable_writes _ FRAMEABLE)
    ltac:(unfold statement_scope,ports,tensor_word_driver_ports; intros id MEMBER; apply in_or_app; left; exact MEMBER)
    PREPARED_FRAME)as [prepared_after [PREPARED_SOURCE PREPARED_PUBLIC]].
  assert(RECEIPT:ncs_observation_receipt shape(Entry ge locals prepared memory)observers).
  { eapply tensor_word_driver_receipt_transport; [exact receipt|].
    assert(HELPER_HEADER:helper<>ncs_pointer shape).
    { intro SAME; apply HELPER_PRIVATE; rewrite SAME; exact tensor_word_driver_header_scope. }
    apply literal_bound_temps_frame; intros [SAME|[SAME|[SAME|[]]]].
    - apply HELPER_HEADER; symmetry; exact SAME.
    - apply HELPER_ROOT; symmetry; exact SAME.
    - apply HELPER_CHILD; symmetry; exact SAME. }
  assert(ROOT_DOMAIN:register_domain root_cache(Entry ge locals captured memory)).
  { destruct(proj1(ncs_receipt_ready receipt))as [block [offset [raw [_ [_ CACHE]]]]]; eexists; exact CACHE. }
  assert(CHILD_DOMAIN:register_domain child_cache(Entry ge locals captured memory)).
  { destruct(proj2(ncs_receipt_ready receipt))as [block [offset [raw [_ [_ CACHE]]]]]; eexists; exact CACHE. }
  unfold tensor_word_driver_profile_flag in PROFILE; apply andb_true_iff in PROFILE as [ROOT_OK CHILD_OK].
  pose proof(proj2(@register_range_sound root_cache root_cap _ ROOT_CAP ROOT_DOMAIN ROOT_OK))as ROOT_RANGE.
  pose proof(proj2(@register_range_sound child_cache child_cap _ CHILD_CAP CHILD_DOMAIN CHILD_OK))as CHILD_RANGE.
  change(0<Int.signed(temp_word root_cache captured)<=root_cap)in ROOT_RANGE.
  change(0<Int.signed(temp_word child_cache captured)<=child_cap)in CHILD_RANGE.
  assert(CACHE_FRAME:temp_agree[root_cache;child_cache]captured prepared)by(apply literal_bound_temps_frame; cbn; intuition congruence).
  assert(ROOT_COUNT:Int.signed(temp_word root_cache prepared)=Int.signed(temp_word root_cache captured)).
  { unfold temp_word; rewrite CACHE_FRAME by(cbn; auto); reflexivity. }
  assert(CHILD_COUNT:Int.signed(temp_word child_cache prepared)=Int.signed(temp_word child_cache captured)).
  { unfold temp_word; rewrite CACHE_FRAME by(cbn; auto); reflexivity. }
  destruct(@tensor_word_header_scan_at_exit fe shape(Entry ge locals prepared memory)pointer row_cursor row_limit
    column_cursor column_limit component_cursor component_limit flag index rhs rename stable scan_live observers RECEIPT
    LEAF WORD NONNEGATIVE UPPER HELPER ltac:(apply PTree.gss)ROW_PRIVATE COLUMN_PRIVATE ITERATOR_PRIVATE
    ROW_COLUMN ITERATOR_ROW ITERATOR_COLUMN ROOT_STABLE CHILD_STABLE POINTER_STABLE HEADER_STABLE STABLE_LIVE
    SOURCE_SCOPE RENAME_ITERATOR RENAME_COLUMN RENAME_ROW RENAME_STABLE ROW_CURSOR_PRIVATE ROW_LIMIT_PRIVATE
    COLUMN_CURSOR_PRIVATE COLUMN_LIMIT_PRIVATE FLAG_PRIVATE COMPONENT_CURSOR_PRIVATE COMPONENT_LIMIT_PRIVATE
    ROW_CONTROLS ROW_CURSOR_FLAG ROW_LIMIT_FLAG COLUMN_CONTROLS COLUMN_CURSOR_FLAG COLUMN_LIMIT_FLAG
    COMPONENT_CONTROLS COMPONENT_CURSOR_FLAG COMPONENT_LIMIT_FLAG
    prepared prepared_after final ltac:(change(0<=Int.signed(temp_word root_cache prepared)); rewrite ROOT_COUNT; lia)
    ltac:(intro; change(0<=Int.signed(temp_word child_cache prepared)); rewrite CHILD_COUNT; lia)
    ltac:(rewrite PREPARED_FRAME by exact tensor_word_driver_row_scope; exact ROW)
    PREPARED_SOURCE CACHED_FRAMEABLE CACHED_SCOPE(temp_agree_refl _ _))as [checked [SCAN [FRAME [FLAG CACHED]]]].
  exists(@tensor_word_header_result shape(Entry ge locals prepared memory)pointer row_cursor row_limit column_cursor column_limit
    component_cursor index rename observers),checked.
  split; [unfold tensor_word_driver_scan; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0);
    [apply literal_bound_set_execution|exact SCAN]|].
  split; [eapply temp_agree_trans; [exact PREPARED_FRAME|eapply temp_agree_weaken; [exact tensor_word_driver_ports_scan|exact FRAME]]|].
  split; [exact FLAG|split].
  - rewrite FRAME by(unfold scan_live,tensor_word_driver_scan_live; left; reflexivity); apply PTree.gss.
  - intro ACCEPT; destruct(CACHED ACCEPT)as [exit [RAW [PUBLIC OBSERVED]]]; exists exit; split.
    + unfold tensor_word_driver_canonical; eapply literal_tests_prepare_execution; [exact RAW|
        apply check_plan_frameable_writes; exact CACHED_FRAMEABLE|exact CACHED_HELPER_PRIVATE|].
      rewrite FRAME by(unfold scan_live,tensor_word_driver_scan_live; left; reflexivity); apply PTree.gss.
    + eapply temp_agree_trans.
      * eapply temp_agree_weaken; [exact tensor_word_driver_ports_live|exact PREPARED_PUBLIC].
      * eapply temp_agree_weaken; [intros id MEMBER; apply tensor_word_driver_ports_scan,tensor_word_driver_ports_live; exact MEMBER|exact PUBLIC].
Qed.

(** The original execution supplies every dynamic definedness premise. The
    outer start and both count gates can refuse without executing the scan. *)
Theorem tensor_word_driver_execution fe ge locals temps memory source_after final :
  exec_stmt fe ge locals temps memory(ncs_original shape)E0 source_after final Out_normal ->
  exists accepted checked,
    exec_stmt fe ge locals temps memory
      (tensor_word_driver_code shape pointer row_cursor row_limit column_cursor column_limit
        component_cursor component_limit flag index rename root_cap child_cap)E0 checked memory Out_normal /\
    temp_agree ports temps checked /\ checked!flag=Some(memory_boolean_word accepted) /\
    (accepted=true -> exists exit,
      exec_stmt fe ge locals checked memory(tensor_word_driver_canonical shape)E0 exit final Out_normal /\
      temp_agree live source_after exit).
Proof.
  intro SOURCE.
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
  unfold tensor_word_driver_code.
  destruct(register_flag row Int.zero(Entry ge locals temps memory))eqn:START.
  - assert(ROW:temps!row=Some(Vint Int.zero))by(exact(@register_flag_evidence row Int.zero _ ROW_DOMAIN START)).
    destruct(@tensor_header_capture_execution fe ge locals shape live temps memory source_after final
      ltac:(rewrite LEAF; reflexivity)FRAMEABLE ROOT_PRIVATE CHILD_PRIVATE CACHES_DISTINCT CHILD_HEADER_PRIVATE SOURCE)
      as [root_word [child [prepared_after [CAPTURE [PREPARED [PUBLIC CHILD]]]]]].
    pose(captured:=tensor_header_captured shape temps root_word child).
    assert(CAPTURE_FRAME:temp_agree ports temps captured)by(apply nested_expression_captured_frame; assumption).
    assert(CACHE:captured!root_cache=Some(Vint root_word))by(apply nested_expression_captured_root; exact CACHES_DISTINCT).
    assert(ROOT_DOMAIN:register_domain root_cache(Entry ge locals captured memory))by(exists root_word; exact CACHE).
    assert(CHILD_DOMAIN:register_range_flag root_cache root_cap(Entry ge locals captured memory)=true ->
      register_domain child_cache(Entry ge locals captured memory)).
    { intro ACTIVE; destruct child as [child_word|].
      - exists child_word; apply nested_expression_captured_child.
      - unfold register_range_flag in ACTIVE; apply andb_true_iff in ACTIVE as [POS _].
        change(Int.lt Int.zero(temp_word root_cache captured)=true)in POS.
        unfold temp_word in POS; rewrite CACHE in POS.
        change(Int.lt(temp_word row temps)root_word=false)in CHILD.
        unfold temp_word in CHILD; rewrite ROW in CHILD; congruence. }
    pose proof(@tensor_word_driver_profile_run shape root_cap child_cap(Entry ge locals captured memory)
      ROOT_DOMAIN CHILD_DOMAIN)as PROFILE_RUN.
    destruct(tensor_word_driver_profile_flag shape root_cap child_cap(Entry ge locals captured memory))eqn:PROFILE.
    + assert(CHILD_SOME:exists child_word,child=Some child_word).
      { destruct child as [child_word|]; [eauto|].
        unfold tensor_word_driver_profile_flag,register_range_flag in PROFILE.
        repeat rewrite andb_true_iff in PROFILE; destruct PROFILE as [[POS _] _].
        change(Int.lt Int.zero(temp_word root_cache captured)=true)in POS.
        unfold temp_word in POS; rewrite CACHE in POS.
        change(Int.lt(temp_word row temps)root_word=false)in CHILD.
        unfold temp_word in CHILD; rewrite ROW in CHILD; congruence. }
      destruct CHILD_SOME as [child_word SAME]; subst child; destruct CHILD as [_ [observers RECEIPT]].
      destruct(tensor_word_driver_captured_scan RECEIPT
        ltac:(rewrite CAPTURE_FRAME by exact tensor_word_driver_row_scope; exact ROW)PROFILE PREPARED)
        as [accepted [checked [SCAN [SCAN_FRAME [FLAG [HELPER_WORD ACCEPTED]]]]]].
      exists accepted,checked; split.
      * eapply decision_fragment_run; [exact START_RUN|].
        eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact CAPTURE|].
        eapply decision_fragment_run; [exact PROFILE_RUN|exact SCAN].
      * split; [eapply temp_agree_trans; eassumption|split; [exact FLAG|]].
        intro ACCEPT; destruct(ACCEPTED ACCEPT)as [exit [CANONICAL EXIT]]; exists exit; split; [exact CANONICAL|].
        eapply temp_agree_trans; [eapply temp_agree_weaken; [exact tensor_word_driver_ports_live|exact PUBLIC]|exact EXIT].
    + exists false,(PTree.set flag(Vint Int.zero)captured); split.
      * eapply decision_fragment_run; [exact START_RUN|].
        eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact CAPTURE|].
        eapply decision_fragment_run; [exact PROFILE_RUN|constructor; constructor].
      * split; [eapply temp_agree_trans; [exact CAPTURE_FRAME|apply temp_agree_set; exact tensor_word_driver_flag_private]|].
        split; [apply PTree.gss|discriminate].
  - exists false,(PTree.set flag(Vint Int.zero)temps); split.
    + eapply decision_fragment_run; [exact START_RUN|constructor; constructor].
    + split; [apply temp_agree_set; exact tensor_word_driver_flag_private|split; [apply PTree.gss|discriminate]].
Qed.

(** Keeping the entire original footprint is what licenses the literal
    original fallback, even when a rejected check changed private state. *)
Theorem tensor_word_driver_execution_with_fallback fe ge locals temps memory source_after final :
  exec_stmt fe ge locals temps memory(ncs_original shape)E0 source_after final Out_normal ->
  exists accepted checked fallback_exit,
    exec_stmt fe ge locals temps memory
      (tensor_word_driver_code shape pointer row_cursor row_limit column_cursor column_limit
        component_cursor component_limit flag index rename root_cap child_cap)E0 checked memory Out_normal /\
    temp_agree ports temps checked /\ checked!flag=Some(memory_boolean_word accepted) /\
    exec_stmt fe ge locals checked memory(ncs_original shape)E0 fallback_exit final Out_normal /\
    temp_agree live source_after fallback_exit /\
    (accepted=true -> exists exit,
      exec_stmt fe ge locals checked memory(tensor_word_driver_canonical shape)E0 exit final Out_normal /\
      temp_agree live source_after exit).
Proof.
  intro SOURCE; destruct(tensor_word_driver_execution SOURCE)as [accepted [checked [RUN [FRAME [FLAG CANONICAL]]]]].
  destruct(@structured_execution_temp_transport fe ge locals temps memory(ncs_original shape)E0 source_after final Out_normal
    SOURCE ports checked(statement_temps(ncs_original shape))(@check_plan_frameable_writes _ FRAMEABLE)
    ltac:(unfold statement_scope,ports,tensor_word_driver_ports; intros id MEMBER; apply in_or_app; left; exact MEMBER)
    FRAME)as [fallback_exit [FALLBACK PUBLIC]].
  exists accepted,checked,fallback_exit; repeat split; try assumption.
  eapply temp_agree_weaken; [exact tensor_word_driver_ports_live|exact PUBLIC].
Qed.

Variable package : tensor_region_package(tensor_word_driver_canonical shape).
Let guard:=tensor_region_guard package.
Let driver:=tensor_word_driver_code shape pointer row_cursor row_limit column_cursor column_limit
  component_cursor component_limit flag index rename root_cap child_cap.
Let canonical_ports:=statement_temps(tensor_word_driver_canonical shape)++live++check_plan_reads(tree_check_plan guard).
Hypotheses (CANONICAL_FRAMEABLE : check_plan_frameable(tensor_word_driver_canonical shape)=true)
  (CANONICAL_FLAG_PRIVATE : ~In flag canonical_ports).

(** A scan refusal skips all numeric/layout checks. Scan acceptance supplies
    actual canonical-source definedness to the existing complete condition. *)
Theorem tensor_word_driver_complete_execution fe ge locals temps memory source_after final :
  exec_stmt fe ge locals temps memory(ncs_original shape)E0 source_after final Out_normal ->
  exists accepted checked,
    exec_stmt fe ge locals temps memory(tensor_word_driver_complete_check package driver flag)
      E0 checked memory Out_normal /\
    temp_agree ports temps checked /\ checked!flag=Some(memory_boolean_word accepted) /\
    (accepted=true -> exists exit,
      exec_stmt fe ge locals checked memory(tensor_word_driver_canonical shape)E0 exit final Out_normal /\
      temp_agree live source_after exit /\ decision_run(Entry ge locals checked memory)guard true).
Proof.
  intro SOURCE; destruct(tensor_word_driver_execution SOURCE)as [scanned [first [RUN [FRAME [FLAG CANONICAL]]]]].
  destruct(@shared_guard_choice_test ge locals first memory flag scanned FLAG)as [value [CHOICE BOOL]].
  unfold tensor_word_driver_complete_check; fold driver guard.
  destruct scanned.
  - destruct(CANONICAL eq_refl)as [canonical_exit [CANONICAL_RUN PUBLIC]].
    assert(DEFINED:tensor_region_domain package(Entry ge locals first memory)).
    { exists canonical_exit,final; apply(tensor_region_source_execution package).
      eapply quiet_execution_preserved; [split; reflexivity|exact CANONICAL_RUN|apply tensor_region_source_quiet; exact package]. }
    destruct(@readonly_available _ _ _ _ _ (tensor_region_condition package false live) _ DEFINED)
      as [accepted [observed [GUARD SAME]]]; subst observed.
    pose(checked:=PTree.set flag(Vint(shared_guard_word accepted))first).
    assert(CHECK_FRAME:temp_agree canonical_ports first checked)by(apply temp_agree_set; exact CANONICAL_FLAG_PRIVATE).
    exists accepted,checked; split.
    + eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact RUN|].
      eapply exec_Sifthenelse; [exact CHOICE|exact BOOL|apply shared_guard_execution; exact GUARD].
    + split; [eapply temp_agree_trans; [exact FRAME|apply temp_agree_set; exact tensor_word_driver_flag_private]|].
      split; [apply PTree.gss|].
      intro ACCEPT; subst accepted.
      destruct(@structured_execution_temp_transport fe ge locals first memory(tensor_word_driver_canonical shape)E0
        canonical_exit final Out_normal CANONICAL_RUN canonical_ports checked(statement_temps(tensor_word_driver_canonical shape))
        (@check_plan_frameable_writes _ CANONICAL_FRAMEABLE)
        ltac:(unfold statement_scope,canonical_ports; intros id MEMBER; apply in_or_app; left; exact MEMBER)CHECK_FRAME)
        as [exit [CANONICAL_CHECKED EXIT]].
      exists exit; split; [exact CANONICAL_CHECKED|split].
      * eapply temp_agree_trans; [exact PUBLIC|eapply temp_agree_weaken; [|exact EXIT]].
        unfold canonical_ports; intros id MEMBER; apply in_or_app; right; apply in_or_app; left; exact MEMBER.
      * eapply(@decision_tree_read_frame guard(Entry ge locals first memory)checked true); [|exact GUARD].
        eapply temp_agree_weaken; [|exact CHECK_FRAME].
        unfold canonical_ports; intros id MEMBER; apply in_or_app; right; apply in_or_app; right; exact MEMBER.
  - exists false,first; split.
    + eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact RUN|].
      eapply exec_Sifthenelse; [exact CHOICE|exact BOOL|constructor].
    + split; [exact FRAME|split; [exact FLAG|discriminate]].
Qed.

Variable pool : list(ident*ident).
Variable proposal : tensor_generated_candidate.
Variable code : statement.
Hypothesis CHECK : CoreAlarmed.Base.mayReturn(check_tensor_generated_region package live pool proposal)(Some code).

(** Consume the actual generated candidate checker at the actual complete
    check exit. A failed check executes the literal original source. *)
Theorem tensor_word_driver_generated_execution fe ge locals temps memory source_after final :
  exec_stmt fe ge locals temps memory(ncs_original shape)E0 source_after final Out_normal ->
  exists exit,exec_stmt fe ge locals temps memory(tensor_word_driver_generated_target package driver flag code)
    E0 exit final Out_normal /\ temp_agree live source_after exit.
Proof.
  intro SOURCE; destruct(tensor_word_driver_complete_execution SOURCE)as [accepted [checked [RUN [FRAME [FLAG ACCEPTED]]]]].
  destruct(@shared_guard_choice_test ge locals checked memory flag accepted FLAG)as [value [CHOICE BOOL]].
  assert(SELECTED:exists exit,exec_stmt fe ge locals checked memory
    (if accepted then tensor_region_branch package code else ncs_original shape)E0 exit final Out_normal /\
    temp_agree live source_after exit).
  { destruct accepted.
    - destruct(ACCEPTED eq_refl)as [canonical_exit [CANONICAL [PUBLIC GUARD]]].
      destruct(@tensor_region_generated_execution _ package fe ge locals checked memory canonical_exit final
        live pool proposal code CHECK CANONICAL GUARD)as [exit [CANDIDATE EXIT]].
      exists exit; split; [exact CANDIDATE|eapply temp_agree_trans; eassumption].
    - destruct(@structured_execution_temp_transport fe ge locals temps memory(ncs_original shape)E0 source_after final Out_normal
        SOURCE ports checked(statement_temps(ncs_original shape))(@check_plan_frameable_writes _ FRAMEABLE)
        ltac:(unfold statement_scope,ports,tensor_word_driver_ports; intros id MEMBER; apply in_or_app; left; exact MEMBER)
        FRAME)as [exit [FALLBACK PUBLIC]].
      exists exit; split; [exact FALLBACK|eapply temp_agree_weaken; [exact tensor_word_driver_ports_live|exact PUBLIC]]. }
  destruct SELECTED as [exit [SELECTED PUBLIC]]; exists exit; split; [|exact PUBLIC].
  unfold tensor_word_driver_generated_target; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact RUN|].
  eapply exec_Sifthenelse; [exact CHOICE|exact BOOL|exact SELECTED].
Qed.

(** The reusable finite-region language host consumes this local guarantee.
    Source progress, typed private allocation and site eligibility are further
    installation obligations; this theorem does not supply a compiler. *)
Theorem tensor_word_driver_generated_contract : PrivateRegion.projected_region_contract live(ncs_original shape)
  (tensor_word_driver_generated_target package driver flag code).
Proof.
  intros temps p locals le current memory after final SCOPE AGREE SOURCE fn continuation.
  destruct(@structured_execution_temp_transport(adapter_entry temps)(globalenv p)locals le memory(ncs_original shape)
    E0 after final Out_normal SOURCE live current(statement_temps(ncs_original shape))
    (@check_plan_frameable_writes _ FRAMEABLE)SCOPE AGREE)as [middle [ORIGINAL PUBLIC]].
  destruct(tensor_word_driver_generated_execution ORIGINAL)as [exit [RUN EXIT_PUBLIC]].
  destruct(exec_stmt_steps(adapter_entry temps)p _ _ _ _ _ _ _ _ RUN fn continuation)as [finish [STEPS EXIT]].
  inversion EXIT; subst finish; exists exit,final; split; [exact STEPS|split].
  - eapply temp_agree_trans; eassumption.
  - apply memory_equivalent_refl.
Qed.
End DRIVER.

Print Assumptions tensor_word_driver_receipt_transport.
Print Assumptions tensor_word_driver_profile_run.
Print Assumptions tensor_word_driver_profile_root_refusal.
Print Assumptions tensor_word_driver_start_refusal.
Print Assumptions tensor_word_driver_captured_scan.
Print Assumptions tensor_word_driver_execution.
Print Assumptions tensor_word_driver_execution_with_fallback.
Print Assumptions tensor_word_driver_complete_execution.
Print Assumptions tensor_word_driver_generated_execution.
Print Assumptions tensor_word_driver_generated_contract.
