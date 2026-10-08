(** Capture and dispatch for the source-licensed single-axis store scan.
    Static scope/name facts are language-instance obligations. The only
    dynamic license is execution of the original, uncached source. *)
From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes Cop ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightNoWrap
  ClightLoopSyntax ClightFrontendLoopProtocol ClightNestedFrontendProgress ClightProjectedExecution.
From GuardMemory Require Import GuardMemoryBooleanScan.
From GuardInterface Require Import ClightLoadedOffsetHeader ClightLoadedBoundSyntax
  ClightAffineFirstBodyReceipt ClightCheckPlanFrame ClightSharedGuard ClightStrictLoopProgress
  ClightWordStoreSequence ClightWordStoreSequenceFactory ClightWordStoreSequenceLoaded
  ClightWordStoreSequenceScan.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition word_store_zero_test row :=
  Ebinop Oeq (Etempvar row type_int32s) (Econst_int Int.zero type_int32s) type_int32s.
Definition word_store_nonnegative_test cache :=
  Ebinop Ole (Econst_int Int.zero type_int32s) (Etempvar cache type_int32s) type_int32s.
Definition word_store_loaded_gate_result row cache temps :=
  Int.eq (temp_word row temps) Int.zero && negb (Int.lt (temp_word cache temps) Int.zero).
Definition word_store_loaded_guard_code row cache pointer delta cursor bound flag rename sites :=
  Ssequence (Sset cache (signed_load_offset pointer delta))
    (Sifthenelse (word_store_zero_test row)
      (Sifthenelse (word_store_nonnegative_test cache)
        (word_store_loaded_scan_code cache cursor bound flag rename sites pointer)
        (Sset flag (Econst_int Int.zero type_int32s)))
      (Sset flag (Econst_int Int.zero type_int32s))).
Definition word_store_loaded_guard_result row cache cursor rename sites pointer entry :=
  if word_store_loaded_gate_result row cache (entry_temps entry)
  then word_store_loaded_scan_result cache cursor rename sites pointer entry else false.
Definition word_store_loaded_rewrite_code row cache pointer delta cursor bound flag rename sites body :=
  Ssequence (word_store_loaded_guard_code row cache pointer delta cursor bound flag rename sites)
    (Sifthenelse (shared_guard_choice flag) (frontend_counted_loop row cache body)
      (loaded_offset_loop row pointer delta body)).

Lemma word_store_structured_frameable allowed code :
  writes_only allowed code -> check_plan_frameable code = true.
Proof. intro WRITES; induction WRITES; cbn; try reflexivity; rewrite IHWRITES1,IHWRITES2; reflexivity. Qed.

Lemma word_store_zero_test_execution ge locals temps memory row word :
  temps!row = Some (Vint word) ->
  expression_test (word_store_zero_test row) (Entry ge locals temps memory) (Int.eq word Int.zero).
Proof.
  intro WORD; exists (Val.of_bool (Int.eq word Int.zero)); split; [|apply bool_of_bool].
  unfold word_store_zero_test; eapply eval_Ebinop; [constructor; exact WORD|constructor|reflexivity].
Qed.
Lemma word_store_nonnegative_test_execution ge locals temps memory cache word :
  temps!cache = Some (Vint word) ->
  expression_test (word_store_nonnegative_test cache) (Entry ge locals temps memory)
    (negb (Int.lt word Int.zero)).
Proof.
  intro WORD; exists (Val.of_bool (negb (Int.lt word Int.zero))); split; [|apply bool_of_bool].
  unfold word_store_nonnegative_test; eapply eval_Ebinop; [constructor|constructor; exact WORD|reflexivity].
Qed.
Lemma word_store_loaded_gate_properties row cache temps :
  word_store_loaded_gate_result row cache temps = true ->
  temp_word row temps = Int.zero /\ 0 <= Int.signed (temp_word cache temps).
Proof.
  unfold word_store_loaded_gate_result; rewrite andb_true_iff; intros [ROW BOUND].
  pose proof (Int.eq_spec (temp_word row temps) Int.zero) as ZERO; rewrite ROW in ZERO.
  split; [exact ZERO|].
  unfold Int.lt in BOUND; rewrite Int.signed_zero in BOUND.
  destruct (zlt (Int.signed (temp_word cache temps)) 0); [discriminate|lia].
Qed.

Section GUARD.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variables row cache pointer cursor bound flag : ident.
Variable delta : int.
Variable body : statement.
Variable checked : checked_word_store_body body.
Variable stable live public : list ident.
Variable rename : ident -> ident.
Hypotheses (POINTER_STABLE : In pointer stable) (CACHE_STABLE : In cache stable)
  (ROW_PRIVATE : ~In row stable) (CURSOR_PRIVATE : ~In cursor stable)
  (RENAME_ROW : rename row = cursor).
Hypothesis RENAME_STABLE : forall id, In id stable -> rename id = id.
Hypothesis SITE_POINTERS : forall site, In site (wsbody_sites checked) -> In (wss_pointer site) stable.
Hypothesis SITE_INDICES : forall site, In site (wsbody_sites checked) ->
  expression_scope (row :: stable) (wss_index site).
Hypotheses (DISTINCT : cursor <> bound) (CURSOR_FLAG : cursor <> flag) (BOUND_FLAG : bound <> flag)
  (CURSOR_LIVE : ~In cursor live) (BOUND_LIVE : ~In bound live) (FLAG_LIVE : ~In flag live)
  (STABLE_LIVE : incl stable live) (PUBLIC_LIVE : incl public live)
  (CACHED_SCOPE : statement_scope live (frontend_counted_loop row cache body))
  (SOURCE_SCOPE : statement_scope live (loaded_offset_loop row pointer delta body))
  (CACHE_PRIVATE : ~In cache (statement_temps (loaded_offset_loop row pointer delta body) ++ public)).
Let sites := wsbody_sites checked.
Let source := loaded_offset_loop row pointer delta body.

(** No READY, array availability, row-zero, or cached-source premise is
    requested at the input. The original first test licenses capture;
    nonzero/negative entries take the refusal branch before scanning. *)
Theorem word_store_loaded_guard_execution ge locals temps memory source_after final :
  exec_stmt fe ge locals temps memory source E0 source_after final Out_normal ->
  exists upper prepared_after after,
    let captured := Entry ge locals (PTree.set cache (Vint upper) temps) memory in
    exec_stmt fe ge locals (entry_temps captured) memory source E0 prepared_after final Out_normal /\
    loaded_offset_cached_header pointer delta cache captured /\
    temp_agree public source_after prepared_after /\
    exec_stmt fe ge locals temps memory
      (word_store_loaded_guard_code row cache pointer delta cursor bound flag rename sites)
      E0 after memory Out_normal /\
    temp_agree live (entry_temps captured) after /\
    temp_agree public temps after /\
    after!flag = Some (memory_boolean_word
      (word_store_loaded_guard_result row cache cursor rename sites pointer captured)) /\
    (word_store_loaded_guard_result row cache cursor rename sites pointer captured = true ->
      exists cached_after,
        exec_stmt fe ge locals after memory (frontend_counted_loop row cache body)
          E0 cached_after final Out_normal /\ temp_agree public source_after cached_after).
Proof.
  intro SOURCE.
  assert (FRAMEABLE : check_plan_frameable source = true).
  { unfold source,loaded_offset_loop,strict_frontend_loop; cbn [check_plan_frameable];
      rewrite (@word_store_structured_frameable [] body (wsbody_writes checked)); reflexivity. }
  destruct (@loaded_offset_capture_receipt fe ge locals temps memory row pointer delta body cache public
    source_after final (wsbody_normal checked) (wsbody_quiet checked) FRAMEABLE CACHE_PRIVATE SOURCE)
    as [upper [prepared_after [CAPTURE [PREPARED [PREPARED_FRAME [RECEIPT READY]]]]]].
  set (captured := Entry ge locals (PTree.set cache (Vint upper) temps) memory).
  assert (PUBLIC_CAPTURE : temp_agree public temps (entry_temps captured)).
  { apply temp_agree_set; intro MEMBER; apply CACHE_PRIVATE,in_or_app; right; exact MEMBER. }
  assert (PUBLIC_SOURCE : temp_agree public source_after prepared_after).
  { eapply temp_agree_weaken; [|exact PREPARED_FRAME]; intros id MEMBER; apply in_or_app; right; exact MEMBER. }
  destruct RECEIPT as [[row_word ROW] [CACHE REST]].
  cbn [entry_temps] in ROW,CACHE.
  pose proof (@word_store_zero_test_execution ge locals (entry_temps captured) memory row row_word ROW)
    as [row_value [ROW_EVAL ROW_BOOL]].
  pose proof (@word_store_nonnegative_test_execution ge locals (entry_temps captured) memory cache upper
    (PTree.gss _ _ _)) as [cache_value [CACHE_EVAL CACHE_BOOL]].
  assert (GATE : word_store_loaded_gate_result row cache (entry_temps captured) =
    Int.eq row_word Int.zero && negb (Int.lt upper Int.zero)).
  { unfold word_store_loaded_gate_result,temp_word; cbn [captured entry_temps]; rewrite ROW,PTree.gss; reflexivity. }
  assert (CACHE_LIVE : In cache live) by (apply STABLE_LIVE; exact CACHE_STABLE).
  destruct (Int.eq row_word Int.zero) eqn:ZERO;
    [destruct (negb (Int.lt upper Int.zero)) eqn:NONNEGATIVE|].
  { assert (ACCEPT_GATE : word_store_loaded_gate_result row cache (entry_temps captured) = true)
      by (rewrite GATE; reflexivity).
    destruct (@word_store_loaded_gate_properties row cache (entry_temps captured) ACCEPT_GATE)
      as [ROW_ZERO NONNEGATIVE_BOUND].
    assert (ROW_VALUE : (entry_temps captured)!row = Some (Vint Int.zero)).
    { cbn [captured entry_temps] in ROW_ZERO |- *; unfold temp_word in ROW_ZERO;
      rewrite ROW in ROW_ZERO; rewrite <-ROW_ZERO; exact ROW. }
    destruct (@word_store_loaded_scan_cached_exit fe row cache pointer cursor delta body checked stable rename
      POINTER_STABLE ROW_PRIVATE CURSOR_PRIVATE RENAME_ROW RENAME_STABLE SITE_POINTERS SITE_INDICES
      captured bound flag live (entry_temps captured) prepared_after final CACHE_STABLE DISTINCT CURSOR_FLAG
      BOUND_FLAG CURSOR_LIVE BOUND_LIVE FLAG_LIVE STABLE_LIVE CACHE_LIVE CACHED_SCOPE READY
      NONNEGATIVE_BOUND ROW_VALUE PREPARED (temp_agree_refl _ _))
      as [after [SCAN [FRAME [FLAG CACHED]]]].
    exists upper,prepared_after,after; cbn zeta; fold captured;
      split; [exact PREPARED|split; [exact READY|split; [exact PUBLIC_SOURCE|split; [|]]]].
    + unfold word_store_loaded_guard_code; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [exact CAPTURE|].
      eapply exec_Sifthenelse; [exact ROW_EVAL|exact ROW_BOOL|].
      eapply exec_Sifthenelse; [exact CACHE_EVAL|exact CACHE_BOOL|exact SCAN].
    + split; [exact FRAME|split; [|split; [|]]].
      * eapply temp_agree_trans; [exact PUBLIC_CAPTURE|eapply temp_agree_weaken; eassumption].
      * unfold word_store_loaded_guard_result; rewrite ACCEPT_GATE; exact FLAG.
      * unfold word_store_loaded_guard_result; rewrite ACCEPT_GATE; intro ACCEPT.
        destruct (CACHED ACCEPT) as [cached_after [RUN PUBLIC]]; exists cached_after; split; [exact RUN|].
        eapply temp_agree_trans; [exact PUBLIC_SOURCE|eapply temp_agree_weaken; eassumption]. }
  all: set (after := PTree.set flag (Vint Int.zero) (entry_temps captured));
      assert (REFUSED : word_store_loaded_guard_result row cache cursor rename sites pointer captured = false)
        by (unfold word_store_loaded_guard_result; rewrite GATE; reflexivity);
      exists upper,prepared_after,after; cbn zeta; fold captured;
      split; [exact PREPARED|split; [exact READY|split; [exact PUBLIC_SOURCE|split; [|]]]].
    all: try (unfold word_store_loaded_guard_code; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);
      [exact CAPTURE|]; eapply exec_Sifthenelse;
      [exact ROW_EVAL|exact ROW_BOOL|];
      first [constructor; constructor|eapply exec_Sifthenelse;
        [exact CACHE_EVAL|exact CACHE_BOOL|constructor; constructor]]).
    all: split; [apply temp_agree_set; exact FLAG_LIVE|split; [|split; [|]]].
    all: try (eapply temp_agree_trans; [exact PUBLIC_CAPTURE|eapply temp_agree_weaken;
      [exact PUBLIC_LIVE|apply temp_agree_set; exact FLAG_LIVE]]).
    all: rewrite REFUSED; first [unfold after; apply PTree.gss|discriminate].
Qed.

(** The cached arm is a first useful transformation: hoisting a loaded loop
    bound. On refusal the complete original source runs from the guard exit.
    A later scheduling adapter can consume the same accepted cached receipt. *)
Theorem word_store_loaded_rewrite_execution ge locals temps memory source_after final :
  exec_stmt fe ge locals temps memory source E0 source_after final Out_normal ->
  exists after,
    exec_stmt fe ge locals temps memory
      (word_store_loaded_rewrite_code row cache pointer delta cursor bound flag rename sites body)
      E0 after final Out_normal /\ temp_agree public source_after after.
Proof.
  intro SOURCE; destruct (word_store_loaded_guard_execution SOURCE)
    as [upper [prepared_after [checked_after [PREPARED [READY [PUBLIC [GUARD [FRAME [INITIAL [FLAG CACHED]]]]]]]]]].
  set (captured := Entry ge locals (PTree.set cache (Vint upper) temps) memory).
  set (accepted := word_store_loaded_guard_result row cache cursor rename sites pointer captured).
  assert (TEST : expression_test (shared_guard_choice flag) (Entry ge locals checked_after memory) accepted).
  { apply shared_guard_choice_test; exact FLAG. }
  destruct TEST as [value [EVAL BOOL]].
  destruct accepted eqn:ACCEPT.
  - destruct (CACHED ACCEPT) as [after [RUN SAME]].
    exists after; split; [|exact SAME].
    unfold word_store_loaded_rewrite_code; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [exact GUARD|].
    eapply exec_Sifthenelse; [exact EVAL|exact BOOL|exact RUN].
  - destruct (@structured_execution_temp_transport fe ge locals (entry_temps captured) memory source
      E0 prepared_after final Out_normal PREPARED live checked_after (statement_temps source)
      (@check_plan_frameable_writes source
        ltac:(unfold source,loaded_offset_loop,strict_frontend_loop; cbn [check_plan_frameable];
          rewrite (@word_store_structured_frameable [] body (wsbody_writes checked)); reflexivity))
      SOURCE_SCOPE FRAME) as [after [RUN SAME]].
    exists after; split.
    + unfold word_store_loaded_rewrite_code; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [exact GUARD|].
      eapply exec_Sifthenelse; [exact EVAL|exact BOOL|exact RUN].
    + eapply temp_agree_trans; [exact PUBLIC|eapply temp_agree_weaken; eassumption].
Qed.
End GUARD.

Print Assumptions word_store_structured_frameable.
Print Assumptions word_store_zero_test_execution.
Print Assumptions word_store_nonnegative_test_execution.
Print Assumptions word_store_loaded_gate_properties.
Print Assumptions word_store_loaded_guard_execution.
Print Assumptions word_store_loaded_rewrite_execution.
