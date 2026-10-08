(** Conditional capture, entry gates and complete dispatch for joint loaded
    scans. An inactive outer loop does not read the child header or cache. *)
From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes Cop ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightNoWrap
  ClightLoopSyntax ClightCountedLoop ClightCountedProtocol ClightFrontendLoopProtocol
  ClightProjectedExecution ClightRectangularLoops ClightRegionProgress.
From GuardMemory Require Import GuardMemoryBooleanScan.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightLoadedOffsetHeader
  ClightExpressionHeaderCapture ClightSignedExpressionProgress ClightStrictLoopProgress ClightDualLoadedUnitSyntax
  ClightNestedExpressionCapture ClightNestedExpressionTransport ClightNestedLoadedOffset
  ClightCheckPlanFrame ClightQuietDeterminacy ClightSharedGuard
  ClightWordStoreSequence ClightWordStoreSequenceFactory ClightWordStoreSequenceGuard
  ClightWordStoreNestedPrefix ClightWordStoreNestedScan ClightWordStoreNestedCached.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition word_store_positive_test cache :=
  Ebinop Olt(Econst_int Int.zero type_int32s)(Etempvar cache type_int32s) type_int32s.
Definition word_store_nested_controls row cache child_cache row_cursor row_limit column_cursor column_limit flag rename sites pointer child_pointer :=
  Sifthenelse(word_store_zero_test row)
    (Sifthenelse(word_store_nonnegative_test cache)
      (Sifthenelse(word_store_positive_test cache)
        (Sifthenelse(word_store_nonnegative_test child_cache)
          (word_store_nested_scan_code cache child_cache row_cursor row_limit column_cursor column_limit flag rename sites pointer child_pointer)
          (Sset flag(Econst_int Int.zero type_int32s)))
        (Sset flag(Econst_int Int.one type_int32s)))
      (Sset flag(Econst_int Int.zero type_int32s)))
    (Sset flag(Econst_int Int.zero type_int32s)).
Definition word_store_nested_guard_code row cache pointer delta (column : ident) child_cache child_pointer child_delta
    row_cursor row_limit column_cursor column_limit flag rename sites :=
  Ssequence(nested_expression_capture row cache(signed_load_offset pointer delta)
      child_cache(signed_load_offset child_pointer child_delta))
    (word_store_nested_controls row cache child_cache row_cursor row_limit column_cursor column_limit flag rename sites pointer child_pointer).
Definition word_store_nested_guard_result row cache child_cache row_cursor column_cursor rename sites pointer child_pointer entry :=
  if Int.eq(temp_word row(entry_temps entry)) Int.zero then
    if negb(Int.lt(temp_word cache(entry_temps entry)) Int.zero) then
      if Int.lt Int.zero(temp_word cache(entry_temps entry)) then
        if negb(Int.lt(temp_word child_cache(entry_temps entry)) Int.zero)
        then word_store_nested_scan_result cache child_cache row_cursor column_cursor rename sites pointer child_pointer entry
        else false
      else true
    else false
  else false.
Definition word_store_nested_rewrite_code row cache pointer delta column child_cache child_pointer child_delta
    row_cursor row_limit column_cursor column_limit flag rename sites body :=
  Ssequence(word_store_nested_guard_code row cache pointer delta column child_cache child_pointer child_delta
    row_cursor row_limit column_cursor column_limit flag rename sites)
    (Sifthenelse(shared_guard_choice flag)(nested_cached_source row cache column child_cache body)
      (nested_loaded_offset_source row pointer delta column child_pointer child_delta body)).

Lemma word_store_if_test_execution fe ge locals temps memory condition accepted yes no after final :
  expression_test condition(Entry ge locals temps memory) accepted ->
  exec_stmt fe ge locals temps memory(if accepted then yes else no) E0 after final Out_normal ->
  exec_stmt fe ge locals temps memory(Sifthenelse condition yes no) E0 after final Out_normal.
Proof. intros [value [EVAL BOOL]] RUN; eapply exec_Sifthenelse; eassumption. Qed.
Lemma word_store_positive_test_execution ge locals temps memory cache word :
  temps!cache=Some(Vint word) ->
  expression_test(word_store_positive_test cache)(Entry ge locals temps memory)(Int.lt Int.zero word).
Proof.
  intro WORD; exists(Val.of_bool(Int.lt Int.zero word)); split; [|apply bool_of_bool].
  unfold word_store_positive_test; eapply eval_Ebinop; [constructor|constructor; exact WORD|reflexivity].
Qed.
Lemma word_store_nonnegative_word word :
  negb(Int.lt word Int.zero)=true -> 0<=Int.signed word.
Proof.
  unfold Int.lt; rewrite Int.signed_zero; destruct(zlt(Int.signed word) 0); [discriminate|lia].
Qed.
Lemma word_store_nonpositive_nonnegative_zero word :
  negb(Int.lt word Int.zero)=true -> Int.lt Int.zero word=false -> word=Int.zero.
Proof.
  intros NONNEGATIVE NONPOSITIVE; pose proof(word_store_nonnegative_word word NONNEGATIVE) as RANGE.
  unfold Int.lt in NONPOSITIVE; rewrite Int.signed_zero in NONPOSITIVE.
  assert(ZERO : Int.signed word=0) by (destruct(zlt 0(Int.signed word)); [discriminate|lia]).
  rewrite <-(Int.repr_signed word),ZERO; reflexivity.
Qed.

Section GUARD.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variables row cache pointer column child_cache child_pointer row_cursor row_limit column_cursor column_limit flag : ident.
Variables delta child_delta : int.
Variable body : statement.
Variable checked : checked_word_store_body body.
Variables stable live public : list ident.
Variable rename : ident -> ident.
Hypotheses (POINTER_STABLE : In pointer stable) (CHILD_POINTER_STABLE : In child_pointer stable)
  (CACHE_STABLE : In cache stable) (CHILD_CACHE_STABLE : In child_cache stable)
  (ROW_PRIVATE : ~In row stable) (COLUMN_PRIVATE : ~In column stable) (ROW_COLUMN : row<>column)
  (STABLE_LIVE : incl stable live)
  (UNIQUE : NoDup [row_cursor;row_limit;column_cursor;column_limit;flag])
  (PRIVATE : forall id, In id [row_cursor;row_limit;column_cursor;column_limit;flag] -> ~In id live)
  (RENAME_ROW : rename row=row_cursor) (RENAME_COLUMN : rename column=column_cursor).
Hypothesis RENAME_STABLE : forall id, In id stable -> rename id=id.
Hypothesis SITE_POINTERS : forall site, In site(wsbody_sites checked) -> In(wss_pointer site) stable.
Hypothesis SITE_INDICES : forall site, In site(wsbody_sites checked) -> expression_scope(row::column::stable)(wss_index site).
Hypotheses (PUBLIC_LIVE : incl public live)
  (CACHED_SCOPE : statement_scope live(nested_cached_source row cache column child_cache body))
  (SOURCE_SCOPE : statement_scope live(nested_loaded_offset_source row pointer delta column child_pointer child_delta body))
  (CACHE_PRIVATE : ~In cache(statement_temps(nested_loaded_offset_source row pointer delta column child_pointer child_delta body)++public))
  (CHILD_CACHE_PRIVATE : ~In child_cache(statement_temps(nested_loaded_offset_source row pointer delta column child_pointer child_delta body)++public))
  (CACHES_DISTINCT : cache<>child_cache).
Let sites := wsbody_sites checked.
Let source := nested_loaded_offset_source row pointer delta column child_pointer child_delta body.
Let cached := nested_cached_source row cache column child_cache body.
Let result entry := word_store_nested_guard_result row cache child_cache row_cursor column_cursor rename sites pointer child_pointer entry.

Lemma word_store_nested_original_frameable : check_plan_frameable source=true.
Proof.
  unfold source,nested_loaded_offset_source,nested_expression_source,nested_expression_body,strict_frontend_loop;
    cbn [check_plan_frameable rectangle_reset counter_increment];
    rewrite(@word_store_structured_frameable [] body(wsbody_writes checked)); reflexivity.
Qed.

Lemma word_store_nested_empty_cached entry source_after final :
  loaded_offset_cached_header pointer delta cache entry ->
  (entry_temps entry)!row=Some(Vint Int.zero) -> (entry_temps entry)!cache=Some(Vint Int.zero) ->
  exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry) source E0 source_after final Out_normal ->
  exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry) cached E0 source_after final Out_normal.
Proof.
  intros ROOT ROW CACHE SOURCE.
  assert(ZERO : exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
    source E0(entry_temps entry)(entry_memory entry) Out_normal).
  { unfold source,nested_loaded_offset_source,nested_expression_source; apply strict_zero_trip_encode.
    change false with(Int.lt Int.zero Int.zero); eapply signed_expression_test_eval; [reflexivity|exact ROW|].
    eapply loaded_offset_bound_from_observations with(cache:=cache)(stable:=stable)(entry:=entry);
      [exact POINTER_STABLE|exact ROOT|exact CACHE|apply temp_agree_refl|eapply loaded_offset_initial_observations; exact ROOT]. }
  assert(QUIET : quiet_statement source=true).
  { unfold source,nested_loaded_offset_source,nested_expression_source,nested_expression_body,strict_frontend_loop;
    cbn [quiet_statement rectangle_reset counter_increment]; rewrite(wsbody_quiet checked); reflexivity. }
  destruct(quiet_execution_determinate SOURCE QUIET ZERO) as [TRACE [TEMPS [MEMORY OUT]]]; subst source_after final.
  unfold cached,nested_cached_source,frontend_counted_loop; apply strict_zero_trip_encode.
  change (expression_test(signed_expression_test row(Etempvar cache type_int32s)) entry(Int.lt Int.zero Int.zero)).
  eapply signed_expression_test_eval; [reflexivity|exact ROW|constructor; exact CACHE].
Qed.

(** Child ready is required only at entries where the original outer test
    succeeds. No child load/cache receipt is needed on an inactive entry. *)
Theorem word_store_nested_post_execution entry source_after final :
  loaded_offset_cached_header pointer delta cache entry ->
  (Int.lt(temp_word row(entry_temps entry))(temp_word cache(entry_temps entry))=true ->
    loaded_offset_cached_header child_pointer child_delta child_cache entry) ->
  exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry) source E0 source_after final Out_normal ->
  exists after,
    exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
      (word_store_nested_controls row cache child_cache row_cursor row_limit column_cursor column_limit flag rename sites pointer child_pointer)
      E0 after(entry_memory entry) Out_normal /\ temp_agree live(entry_temps entry) after /\
    after!flag=Some(memory_boolean_word(result entry)) /\
    (result entry=true -> exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
      cached E0 source_after final Out_normal).
Proof.
  intros ROOT CHILD SOURCE.
  destruct(signed_expression_completed_header SOURCE) as [first TEST].
  destruct(@signed_expression_test_facts (entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
    row(signed_load_offset pointer delta) first eq_refl TEST) as [row_word [word [ROW [BOUND FIRST]]]].
  assert(ROW_VALUE : temp_word row(entry_temps entry)=row_word) by (unfold temp_word; rewrite ROW; reflexivity).
  set(upper:=temp_word cache(entry_temps entry)).
  assert(CACHE : (entry_temps entry)!cache=Some(Vint upper)).
  { destruct ROOT as [block [offset [raw [PTR [READ CACHE]]]]]; unfold upper,temp_word; rewrite CACHE; reflexivity. }
  pose proof(@word_store_zero_test_execution (entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry) row row_word ROW) as ZERO_TEST.
  pose proof(@word_store_nonnegative_test_execution (entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry) cache upper CACHE) as NONNEGATIVE_TEST.
  pose proof(@word_store_positive_test_execution (entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry) cache upper CACHE) as POSITIVE_TEST.
  assert(FLAG_PRIVATE : ~In flag live) by (apply PRIVATE; cbn; tauto).
  destruct(Int.eq row_word Int.zero) eqn:ZERO;
    [destruct(negb(Int.lt upper Int.zero)) eqn:NONNEGATIVE|].
  { pose proof(Int.eq_spec row_word Int.zero) as ROW_EQUAL; rewrite ZERO in ROW_EQUAL.
    assert(ROW_ZERO : (entry_temps entry)!row=Some(Vint Int.zero)) by (rewrite <-ROW_EQUAL; exact ROW).
    pose proof(word_store_nonnegative_word upper NONNEGATIVE) as ROOT_NONNEGATIVE.
    destruct(Int.lt Int.zero upper) eqn:POSITIVE.
    - assert(CHILD_READY : loaded_offset_cached_header child_pointer child_delta child_cache entry).
      { apply CHILD; rewrite ROW_VALUE,ROW_EQUAL; exact POSITIVE. }
      set(child_upper:=temp_word child_cache(entry_temps entry)).
      assert(CHILD_CACHE : (entry_temps entry)!child_cache=Some(Vint child_upper)).
      { destruct CHILD_READY as [block [offset [raw [PTR [READ CACHE']]]]]; unfold child_upper,temp_word; rewrite CACHE'; reflexivity. }
      pose proof(@word_store_nonnegative_test_execution (entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry) child_cache child_upper CHILD_CACHE) as CHILD_TEST.
      destruct(negb(Int.lt child_upper Int.zero)) eqn:CHILD_NONNEGATIVE.
      + destruct(@word_store_nested_scan_from_source fe row cache pointer column child_cache child_pointer
          row_cursor row_limit column_cursor column_limit flag delta child_delta body checked stable live rename
          POINTER_STABLE CHILD_POINTER_STABLE CACHE_STABLE CHILD_CACHE_STABLE ROW_PRIVATE COLUMN_PRIVATE ROW_COLUMN
          STABLE_LIVE UNIQUE PRIVATE RENAME_ROW RENAME_COLUMN RENAME_STABLE SITE_POINTERS SITE_INDICES
          entry(entry_temps entry) source_after final (conj ROOT CHILD_READY) ROOT_NONNEGATIVE
          (word_store_nonnegative_word child_upper CHILD_NONNEGATIVE) ROW_ZERO SOURCE(temp_agree_refl _ _))
          as [after [SCAN [FRAME [FLAG CACHED]]]].
        assert(RESULT : result entry=word_store_nested_scan_result cache child_cache row_cursor column_cursor rename sites pointer child_pointer entry).
        { unfold result,word_store_nested_guard_result; rewrite ROW_VALUE,ROW_EQUAL; change(Int.eq Int.zero Int.zero) with true;
          fold upper child_upper; rewrite NONNEGATIVE,POSITIVE,CHILD_NONNEGATIVE; reflexivity. }
        exists after; split.
        * unfold word_store_nested_controls; eapply word_store_if_test_execution; [exact ZERO_TEST|].
          eapply word_store_if_test_execution; [exact NONNEGATIVE_TEST|].
          eapply word_store_if_test_execution; [exact POSITIVE_TEST|].
          eapply word_store_if_test_execution; [exact CHILD_TEST|exact SCAN].
        * split; [exact FRAME|split; rewrite RESULT; assumption].
      + set(after:=PTree.set flag(Vint Int.zero)(entry_temps entry)).
        assert(RESULT : result entry=false).
        { unfold result,word_store_nested_guard_result; rewrite ROW_VALUE,ROW_EQUAL; change(Int.eq Int.zero Int.zero) with true;
          fold upper child_upper; rewrite NONNEGATIVE,POSITIVE,CHILD_NONNEGATIVE; reflexivity. }
        exists after; split.
        * unfold word_store_nested_controls; eapply word_store_if_test_execution; [exact ZERO_TEST|].
          eapply word_store_if_test_execution; [exact NONNEGATIVE_TEST|].
          eapply word_store_if_test_execution; [exact POSITIVE_TEST|].
          eapply word_store_if_test_execution; [exact CHILD_TEST|constructor; constructor].
        * split; [apply temp_agree_set; exact FLAG_PRIVATE|split; rewrite RESULT;
            [unfold after; apply PTree.gss|discriminate]].
    - pose proof(word_store_nonpositive_nonnegative_zero upper NONNEGATIVE POSITIVE) as EMPTY.
      assert(CACHE_ZERO : (entry_temps entry)!cache=Some(Vint Int.zero)) by (rewrite <-EMPTY; exact CACHE).
      set(after:=PTree.set flag(Vint Int.one)(entry_temps entry)).
      assert(RESULT : result entry=true).
      { unfold result,word_store_nested_guard_result; rewrite ROW_VALUE,ROW_EQUAL; change(Int.eq Int.zero Int.zero) with true;
        fold upper; rewrite NONNEGATIVE,POSITIVE; reflexivity. }
      exists after; split.
      + unfold word_store_nested_controls; eapply word_store_if_test_execution; [exact ZERO_TEST|].
        eapply word_store_if_test_execution; [exact NONNEGATIVE_TEST|].
        eapply word_store_if_test_execution; [exact POSITIVE_TEST|constructor; constructor].
      + split; [apply temp_agree_set; exact FLAG_PRIVATE|split].
        * rewrite RESULT; unfold after; apply PTree.gss.
        * intro ACCEPT; apply word_store_nested_empty_cached; assumption. }
  all: set(after:=PTree.set flag(Vint Int.zero)(entry_temps entry));
    assert(RESULT : result entry=false) by
      (unfold result,word_store_nested_guard_result; rewrite ROW_VALUE,ZERO; fold upper; try rewrite NONNEGATIVE; reflexivity);
    exists after; split.
  all: try (unfold word_store_nested_controls; eapply word_store_if_test_execution; [exact ZERO_TEST|];
    first [constructor; constructor|eapply word_store_if_test_execution; [exact NONNEGATIVE_TEST|constructor; constructor]]).
  all: split; [apply temp_agree_set; exact FLAG_PRIVATE|split; rewrite RESULT;
    [unfold after; apply PTree.gss|discriminate]].
Qed.

Theorem word_store_nested_guard_execution ge locals temps memory source_after final :
  exec_stmt fe ge locals temps memory source E0 source_after final Out_normal ->
  exists upper child prepared_after after,
    let captured := Entry ge locals(nested_expression_captured cache child_cache temps upper child) memory in
    exec_stmt fe ge locals temps memory(nested_expression_capture row cache(signed_load_offset pointer delta)
      child_cache(signed_load_offset child_pointer child_delta)) E0(entry_temps captured) memory Out_normal /\
    exec_stmt fe ge locals(entry_temps captured) memory source E0 prepared_after final Out_normal /\
    loaded_offset_cached_header pointer delta cache captured /\
    (match child with
      | None=>Int.lt(temp_word row temps) upper=false
      | Some word=>Int.lt(temp_word row temps) upper=true /\
          loaded_offset_cached_header child_pointer child_delta child_cache captured
      end) /\
    temp_agree public source_after prepared_after /\
    exec_stmt fe ge locals temps memory(word_store_nested_guard_code row cache pointer delta column child_cache child_pointer child_delta
      row_cursor row_limit column_cursor column_limit flag rename sites) E0 after memory Out_normal /\
    temp_agree live(entry_temps captured) after /\ temp_agree public temps after /\
    after!flag=Some(memory_boolean_word(result captured)) /\
    (result captured=true -> exists cached_after,
      exec_stmt fe ge locals after memory cached E0 cached_after final Out_normal /\ temp_agree public source_after cached_after).
Proof.
  intro SOURCE.
  assert(CHILD_DISTINCT : column<>child_pointer) by (intro SAME; apply COLUMN_PRIVATE; rewrite SAME; exact CHILD_POINTER_STABLE).
  destruct(@nested_loaded_offset_capture fe ge locals temps memory row pointer delta column child_pointer child_delta body
    cache child_cache public source_after final(wsbody_quiet checked) word_store_nested_original_frameable
    CACHE_PRIVATE CHILD_CACHE_PRIVATE CACHES_DISTINCT CHILD_DISTINCT SOURCE)
    as [upper [child [prepared_after [CAPTURE [PREPARED [PUBLIC [ROOT CHILD]]]]]]].
  set(captured:=Entry ge locals(nested_expression_captured cache child_cache temps upper child) memory).
  assert(PUBLIC_SOURCE : temp_agree public source_after prepared_after).
  { eapply temp_agree_weaken; [|exact PUBLIC]; intros id MEMBER; apply in_or_app; right; exact MEMBER. }
  assert(SOURCE_CAPTURE : temp_agree(statement_temps source++public) temps(entry_temps captured)).
  { apply nested_expression_captured_frame; assumption. }
  assert(PUBLIC_CAPTURE : temp_agree public temps(entry_temps captured)).
  { eapply temp_agree_weaken; [|exact SOURCE_CAPTURE]; intros id MEMBER; apply in_or_app; right; exact MEMBER. }
  assert(ROW_SCOPE : In row(statement_temps source++public)).
  { unfold source,nested_loaded_offset_source,nested_expression_source,strict_frontend_loop,signed_expression_test;
      cbn [statement_temps expression_temps]; repeat rewrite in_app_iff; cbn; tauto. }
  assert(ROW_FRAME : temp_word row(entry_temps captured)=temp_word row temps).
  { unfold temp_word; rewrite <-(SOURCE_CAPTURE row ROW_SCOPE); reflexivity. }
  assert(ROOT_WORD : temp_word cache(entry_temps captured)=upper).
  { unfold temp_word; cbn [captured entry_temps]; rewrite nested_expression_captured_root by exact CACHES_DISTINCT; reflexivity. }
  assert(CHILD_LICENSE : Int.lt(temp_word row(entry_temps captured))(temp_word cache(entry_temps captured))=true ->
    loaded_offset_cached_header child_pointer child_delta child_cache captured).
  { rewrite ROW_FRAME,ROOT_WORD; destruct child as [word|]; [intros; exact(proj2 CHILD)|intro ACTIVE; congruence]. }
  destruct(word_store_nested_post_execution ROOT CHILD_LICENSE PREPARED) as [after [POST [FRAME [FLAG CACHED]]]].
  exists upper,child,prepared_after,after; cbn zeta; fold captured;
    split; [exact CAPTURE|split; [exact PREPARED|split; [exact ROOT|split; [exact CHILD|
      split; [exact PUBLIC_SOURCE|split; [|split; [exact FRAME|split; [|split; [exact FLAG|]]]]]]]]].
  - unfold word_store_nested_guard_code; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact CAPTURE|exact POST].
  - eapply temp_agree_trans; [exact PUBLIC_CAPTURE|eapply temp_agree_weaken; eassumption].
  - intro ACCEPT; destruct(@structured_execution_temp_transport fe ge locals(entry_temps captured) memory cached
      E0 prepared_after final Out_normal(CACHED ACCEPT) live after [row;column]
      (word_store_nested_cached_writes row cache column child_cache checked) CACHED_SCOPE FRAME)
      as [cached_after [RUN SAME]].
    exists cached_after; split; [exact RUN|eapply temp_agree_trans; [exact PUBLIC_SOURCE|eapply temp_agree_weaken; eassumption]].
Qed.

Theorem word_store_nested_rewrite_execution ge locals temps memory source_after final :
  exec_stmt fe ge locals temps memory source E0 source_after final Out_normal ->
  exists after,
    exec_stmt fe ge locals temps memory(word_store_nested_rewrite_code row cache pointer delta column child_cache child_pointer child_delta
      row_cursor row_limit column_cursor column_limit flag rename sites body) E0 after final Out_normal /\
    temp_agree public source_after after.
Proof.
  intro SOURCE; destruct(word_store_nested_guard_execution SOURCE)
    as [upper [child [prepared_after [checked_after [CAPTURE [PREPARED [ROOT [CHILD
      [PUBLIC [GUARD [FRAME [INITIAL [FLAG CACHED]]]]]]]]]]]]].
  set(captured:=Entry ge locals(nested_expression_captured cache child_cache temps upper child) memory).
  set(accepted:=result captured).
  assert(TEST : expression_test(shared_guard_choice flag)(Entry ge locals checked_after memory) accepted).
  { apply shared_guard_choice_test; exact FLAG. }
  destruct TEST as [value [EVAL BOOL]].
  destruct accepted eqn:ACCEPT.
  - destruct(CACHED ACCEPT) as [after [RUN SAME]]; exists after; split; [|exact SAME].
    unfold word_store_nested_rewrite_code; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact GUARD|].
    eapply exec_Sifthenelse; [exact EVAL|exact BOOL|exact RUN].
  - destruct(@structured_execution_temp_transport fe ge locals(entry_temps captured) memory source
      E0 prepared_after final Out_normal PREPARED live checked_after(statement_temps source)
      (@check_plan_frameable_writes source word_store_nested_original_frameable) SOURCE_SCOPE FRAME)
      as [after [RUN SAME]].
    exists after; split.
    + unfold word_store_nested_rewrite_code; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact GUARD|].
      eapply exec_Sifthenelse; [exact EVAL|exact BOOL|exact RUN].
    + eapply temp_agree_trans; [exact PUBLIC|eapply temp_agree_weaken; eassumption].
Qed.
End GUARD.

Print Assumptions word_store_if_test_execution.
Print Assumptions word_store_positive_test_execution.
Print Assumptions word_store_nonnegative_word.
Print Assumptions word_store_nonpositive_nonnegative_zero.
Print Assumptions word_store_nested_original_frameable.
Print Assumptions word_store_nested_empty_cached.
Print Assumptions word_store_nested_post_execution.
Print Assumptions word_store_nested_guard_execution.
Print Assumptions word_store_nested_rewrite_execution.
