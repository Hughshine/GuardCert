(** Source-licensed column scans for loaded bounds and dynamic word addresses.
    Actual source prefixes supply point permissions; accepted scans preserve
    captured observations before advancing. No cached source run is assumed. *)
From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightTempFrame ClightTempFootprint ClightCondition ClightNoWrap
 ClightCountedLoop ClightRectangularLoops ClightLoopSyntax ClightRegionProgress
 CompCertMemoryActions ClightFramedLoop ClightRedundantSet ClightFrontendLoopProtocol.
From GuardMemory Require Import GuardMemoryBooleanScan.
From GuardInterface Require Import ClightWordArithmeticTransport ClightWordCoordinateRename
 ClightDirectWordObservation ClightWordComponentScan ClightConstantBoundModel
 ClightAffineJointObservation ClightObservedHeaderPrefix ClightExpressionBodyPrefix
 ClightExpressionPrefixAt ClightExpressionReachedPrefix ClightStrictLoopProgress
 ClightSignedExpressionProgress ClightShortCircuitPrefixLoop ClightStructuredStorePermissions
 ClightExpressionBodyTransport ClightNestedExpressionCapture ClightNestedExpressionPrefix
 ClightJointInnerRowFrame.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Private component scans can start after earlier scans changed their
    scratch state. Their result depends only on the protected address inputs. *)
Lemma tensor_word_component_point_base_frame pointer cursor index rename observers live before current :
  word_arithmetic index -> ~In cursor live -> In pointer live ->
  incl(expression_temps(word_rename rename index))(cursor::live) ->
  temp_agree live before current -> forall k,
  word_component_test pointer cursor index rename current observers k=
  word_component_test pointer cursor index rename before observers k.
Proof.
  intros WORD PRIVATE POINTER SCOPE FRAME k.
  unfold word_component_test.
  rewrite(@word_address_evaluate_frame pointer(word_rename rename index)
    (word_component_at cursor before k)(word_component_at cursor current k)
    (word_rename_arithmetic rename WORD)); [reflexivity|].
  intros id [SAME|MEMBER].
  - subst id; unfold word_component_at; rewrite !PTree.gso;
      try(intro SAME; apply PRIVATE; congruence); apply FRAME; exact POINTER.
  - specialize(SCOPE id MEMBER); unfold word_component_at.
    destruct SCOPE as [SAME|MEMBER']; [subst id; rewrite !PTree.gss; reflexivity|].
    rewrite !PTree.gso; try(intro SAME; apply PRIVATE; congruence); apply FRAME; exact MEMBER'.
Qed.

Theorem tensor_word_component_result_base_frame pointer cursor index rename observers live before current upper :
  word_arithmetic index -> ~In cursor live -> In pointer live ->
  incl(expression_temps(word_rename rename index))(cursor::live) ->
  temp_agree live before current ->
  word_component_result pointer cursor index rename current observers upper=
  word_component_result pointer cursor index rename before observers upper.
Proof.
  intros WORD PRIVATE POINTER SCOPE FRAME; unfold word_component_result.
  apply memory_boolean_scan_ext; eapply tensor_word_component_point_base_frame; eassumption.
Qed.

Definition tensor_word_column_component_entry iterator column j entry :=
  Entry(entry_ge entry)(entry_env entry)
    (PTree.set iterator(Vint Int.zero)(PTree.set column(Vint(Int.repr j))(entry_temps entry)))
    (entry_memory entry).

Lemma tensor_word_column_component_cache iterator column j entry stable helper upper :
  ~In iterator stable -> ~In column stable -> In helper stable ->
  (entry_temps entry)!helper=Some(Vint upper) ->
  (entry_temps(tensor_word_column_component_entry iterator column j entry))!helper=Some(Vint upper).
Proof.
  intros ITERATOR COLUMN HELPER CACHE; cbn [tensor_word_column_component_entry entry_temps].
  rewrite !PTree.gso; try exact CACHE; intro SAME; subst helper; contradiction.
Qed.

Lemma tensor_word_column_component_frame iterator column j entry stable current :
  iterator<>column -> ~In iterator stable -> ~In column stable ->
  current!column=Some(Vint(Int.repr j)) -> temp_agree stable(entry_temps entry)current ->
  temp_agree(column::stable)(entry_temps(tensor_word_column_component_entry iterator column j entry))
    (PTree.set iterator(Vint Int.zero)current).
Proof.
  intros DISTINCT ITERATOR COLUMN COUNTER FRAME id [SAME|MEMBER].
  - subst id; cbn [tensor_word_column_component_entry entry_temps].
    rewrite !PTree.gso by congruence; rewrite PTree.gss; exact COUNTER.
  - cbn [tensor_word_column_component_entry entry_temps]; rewrite !PTree.gso;
      try(intro SAME; subst id; contradiction); apply FRAME; exact MEMBER.
Qed.

Lemma tensor_word_column_source_writes iterator upper pointer index rhs :
  writes_only[iterator](constant_body_source iterator upper(direct_word_store pointer index rhs)).
Proof.
  unfold constant_body_source,rectangle_reset,strict_frontend_loop,counter_increment,direct_word_store.
  repeat constructor; left; reflexivity.
Qed.

(** Open the next literal component from a column's original execution. The
    ghost coordinate entry shares the global captured-memory anchor, even when
    the reached original body executes in memory modified by preceding stores. *)
Theorem tensor_word_column_component_prefix_open fe iterator helper column cache bound pointer index rhs
    upper stable ready observers entry j :
  typeof bound=type_int32s -> iterator<>column ->
  ~In iterator stable -> ~In column stable -> In helper stable ->
  (entry_temps entry)!helper=Some(Vint(Int.repr upper)) -> 0<=upper -> signed_range upper ->
  (forall point current memory,
    ready entry -> 0<=point<=Int.signed(temp_word cache(entry_temps entry)) ->
    current!column=Some(Vint(Int.repr point)) -> temp_agree stable(entry_temps entry)current ->
    header_observations_match(map word_observer_snapshot observers)memory ->
    eval_expr(entry_ge entry)(entry_env entry)current memory bound(Vint(temp_word cache(entry_temps entry)))) ->
  expression_body_prefix fe column cache bound
    (constant_body_source iterator(Int.repr upper)(direct_word_store pointer index rhs))
    stable ready(fun _=>map word_observer_snapshot observers)j entry ->
  j<Int.signed(temp_word cache(entry_temps entry)) ->
  word_component_prefix fe(entry_ge entry)(entry_env entry)(entry_memory entry)iterator helper pointer index rhs
    (column::stable)(entry_temps(tensor_word_column_component_entry iterator column j entry))observers upper 0.
Proof.
  intros TYPE DISTINCT ITERATOR COLUMN HELPER CACHE NONNEGATIVE UPPER HEADER PREFIX ACTIVE.
  pose proof PREFIX as [_ [_ [_ [INITIAL _]]]].
  destruct(@expression_body_prefix_receipt_at fe column cache bound
    (constant_body_source iterator(Int.repr upper)(direct_word_store pointer index rhs))
    stable ready(fun _=>map word_observer_snapshot observers)entry TYPE eq_refl eq_refl HEADER j PREFIX ACTIVE)
    as [current [memory [after [final [COUNTER [FRAME [OBSERVED [BACK SOURCE]]]]]]]].
  destruct(sequence_normal_decode SOURCE)as [reset [reset_memory [RESET LOOP]]].
  destruct(rectangle_reset_decode RESET)as [_ [TEMPS [MEMORY _]]]; subst reset reset_memory.
  unfold word_component_prefix.
  eapply expression_body_prefix_reached with(current:=PTree.set iterator(Vint Int.zero)current)
    (memory:=memory)(after:=after)(final:=final).
  - exact I.
  - exists(Int.repr upper); apply tensor_word_column_component_cache with(stable:=stable); assumption.
  - change(0<=0<=Int.signed(temp_word helper(entry_temps(tensor_word_column_component_entry iterator column j entry)))).
    unfold temp_word; rewrite(@tensor_word_column_component_cache iterator column j entry stable helper(Int.repr upper)
      ITERATOR COLUMN HELPER CACHE); rewrite Int.signed_repr by exact UPPER; lia.
  - exact INITIAL.
  - apply PTree.gss.
  - eapply tensor_word_column_component_frame; eassumption.
  - exact OBSERVED.
  - exact BACK.
  - exact LOOP.
Qed.

Definition tensor_word_column_scan_code cache column_cursor column_limit flag component :=
  Ssequence(Sset column_limit(Etempvar cache type_int32s))
    (Ssequence(Sset column_cursor(Econst_int Int.zero type_int32s))
      (short_circuit_prefix_loop column_cursor column_limit flag component)).

Section COLUMN.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable entry : clight_entry.
Variables iterator helper column cache pointer column_cursor column_limit component_cursor component_limit flag : ident.
Variables index rhs bound : expr.
Variable upper : Z.
Variable rename : ident -> ident.
Variables stable live : list ident.
Variable base : temp_env.
Variable observers : list clight_word_observer.
Variable ready : clight_entry -> Prop.
Let count := Int.signed(temp_word cache(entry_temps entry)).
Let snapshots := map word_observer_snapshot observers.
Let source := constant_body_source iterator(Int.repr upper)(direct_word_store pointer index rhs).
Definition tensor_word_column_prefix j := expression_body_prefix fe column cache bound source stable ready(fun _=>snapshots)j entry.
Definition tensor_word_column_source_base j := entry_temps(tensor_word_column_component_entry iterator column j entry).
Definition tensor_word_column_guard_base j := PTree.set column_limit(Vint(Int.repr count))
  (PTree.set column_cursor(Vint(Int.repr j))base).
Let component_live := column_cursor::column_limit::live.
Definition tensor_word_column_test j := word_component_result pointer component_cursor index rename(tensor_word_column_guard_base j)observers upper.
Definition tensor_word_column_result := memory_boolean_scan_result tensor_word_column_test 0(Z.to_nat count).
Definition tensor_word_column_component_code := word_component_scan_code pointer component_cursor component_limit flag index rename observers upper.
Definition tensor_word_column_code := tensor_word_column_scan_code cache column_cursor column_limit flag tensor_word_column_component_code.

Hypothesis WORD : word_arithmetic index.
Hypotheses (NONNEGATIVE : 0<=upper) (UPPER : signed_range upper).
Hypothesis HELPER : In helper stable.
Hypothesis CACHE : (entry_temps entry)!helper=Some(Vint(Int.repr upper)).
Hypotheses (ITERATOR_COLUMN : iterator<>column) (ITERATOR_PRIVATE : ~In iterator stable) (COLUMN_PRIVATE : ~In column stable).
Hypothesis TYPE : typeof bound=type_int32s.
Hypothesis HEADER : forall j current memory,
  ready entry -> 0<=j<=count -> current!column=Some(Vint(Int.repr j)) ->
  temp_agree stable(entry_temps entry)current -> header_observations_match snapshots memory ->
  eval_expr(entry_ge entry)(entry_env entry)current memory bound(Vint(temp_word cache(entry_temps entry))).
Hypotheses (POINTER_STABLE : In pointer stable) (POINTER_LIVE : In pointer live).
Hypothesis POINTER : (entry_temps entry)!pointer=base!pointer.
Hypothesis SOURCE_SCOPE : incl(expression_temps index)(iterator::column::stable).
Hypotheses (RENAME_ITERATOR : rename iterator=component_cursor) (RENAME_COLUMN : rename column=column_cursor).
Hypothesis RENAME_STABLE : incl(map rename stable)live.
Hypothesis SOURCE_WORDS : forall id,In id stable -> (entry_temps entry)!id=base!(rename id).
Hypotheses (COLUMN_CURSOR_PRIVATE : ~In column_cursor live) (COLUMN_LIMIT_PRIVATE : ~In column_limit live) (FLAG_PRIVATE : ~In flag live).
Hypotheses (COLUMN_CONTROLS : column_cursor<>column_limit) (COLUMN_CURSOR_FLAG : column_cursor<>flag) (COLUMN_LIMIT_FLAG : column_limit<>flag).
Hypotheses (COMPONENT_CURSOR_PRIVATE : ~In component_cursor component_live) (COMPONENT_LIMIT_PRIVATE : ~In component_limit component_live).
Hypotheses (COMPONENT_CONTROLS : component_cursor<>component_limit) (COMPONENT_CURSOR_FLAG : component_cursor<>flag)
  (COMPONENT_LIMIT_FLAG : component_limit<>flag).
Hypothesis BOUND_LIVE : In cache live.
Hypothesis BOUND_STABLE : In cache stable.
Hypothesis BOUND_WORD : base!cache=(entry_temps entry)!cache.
Hypothesis READS : Forall(word_observer_receipt(entry_ge entry)(entry_env entry)base(entry_memory entry))observers.
Hypothesis OBSERVER_SCOPE : forall observer,In observer observers -> expression_scope live(word_observer_address observer).

Lemma tensor_word_column_live_frame j : temp_agree live base(tensor_word_column_guard_base j).
Proof. unfold tensor_word_column_guard_base; eapply temp_agree_trans; apply temp_agree_set; assumption. Qed.
Lemma tensor_word_column_runtime_frame j current :
  current!column_cursor=Some(Vint(Int.repr j)) -> current!column_limit=Some(Vint(Int.repr count)) ->
  temp_agree live base current -> temp_agree component_live(tensor_word_column_guard_base j)current.
Proof.
  intros CURSOR LIMIT FRAME id [SAME|[SAME|MEMBER]].
  - subst id; unfold tensor_word_column_guard_base; rewrite PTree.gso by congruence; rewrite PTree.gss; exact CURSOR.
  - subst id; unfold tensor_word_column_guard_base; rewrite PTree.gss; exact LIMIT.
  - unfold tensor_word_column_guard_base; rewrite !PTree.gso;
      try(intro SAME; apply COLUMN_CURSOR_PRIVATE; congruence);
      try(intro SAME; apply COLUMN_LIMIT_PRIVATE; congruence); apply FRAME; exact MEMBER.
Qed.
Lemma tensor_word_column_renamed_stable : incl(map rename(column::stable))component_live.
Proof.
  cbn [map]; intros id [SAME|MEMBER].
  - subst id; rewrite RENAME_COLUMN; left; reflexivity.
  - right; right; apply RENAME_STABLE; exact MEMBER.
Qed.
Lemma tensor_word_column_renamed_scope : incl(expression_temps(word_rename rename index))(component_cursor::component_live).
Proof.
  rewrite(word_rename_temps rename WORD); intros id MEMBER.
  apply in_map_iff in MEMBER as [raw [SAME MEMBER]]; subst id.
  specialize(SOURCE_SCOPE raw MEMBER); destruct SOURCE_SCOPE as [SAME|MEMBER']; [subst raw|].
  - rewrite RENAME_ITERATOR; left; reflexivity.
  - right; apply tensor_word_column_renamed_stable,in_map; exact MEMBER'.
Qed.
Lemma tensor_word_column_component_words j : forall id,In id(column::stable) ->
  (tensor_word_column_source_base j)!id=(tensor_word_column_guard_base j)!(rename id).
Proof.
  intros id [SAME|MEMBER].
  - subst id; unfold tensor_word_column_source_base,tensor_word_column_guard_base;
      cbn [tensor_word_column_component_entry entry_temps].
    rewrite PTree.gso by congruence; rewrite PTree.gss,RENAME_COLUMN.
    rewrite PTree.gso by congruence; rewrite PTree.gss; reflexivity.
  - assert(MAPPED:In(rename id)live)by(apply RENAME_STABLE,in_map; exact MEMBER).
    unfold tensor_word_column_source_base,tensor_word_column_guard_base; cbn [tensor_word_column_component_entry entry_temps].
    rewrite !PTree.gso; try(intro SAME; apply ITERATOR_PRIVATE; congruence);
      try(intro SAME; apply COLUMN_PRIVATE; congruence);
      try(intro SAME; apply COLUMN_CURSOR_PRIVATE; congruence);
      try(intro SAME; apply COLUMN_LIMIT_PRIVATE; congruence).
    apply SOURCE_WORDS; exact MEMBER.
Qed.
Lemma tensor_word_column_component_pointer j : (tensor_word_column_source_base j)!pointer=(tensor_word_column_guard_base j)!pointer.
Proof.
  unfold tensor_word_column_source_base,tensor_word_column_guard_base; cbn [tensor_word_column_component_entry entry_temps].
  rewrite !PTree.gso; try(intro SAME; apply ITERATOR_PRIVATE; congruence);
    try(intro SAME; apply COLUMN_PRIVATE; congruence);
    try(intro SAME; apply COLUMN_CURSOR_PRIVATE; congruence);
    try(intro SAME; apply COLUMN_LIMIT_PRIVATE; congruence); exact POINTER.
Qed.
Lemma tensor_word_column_component_ready j : tensor_word_column_prefix j -> j<count ->
  word_component_prefix fe(entry_ge entry)(entry_env entry)(entry_memory entry)iterator helper pointer index rhs
    (column::stable)(tensor_word_column_source_base j)observers upper 0.
Proof. eapply tensor_word_column_component_prefix_open; eassumption. Qed.

Theorem tensor_word_column_component_execution j current :
  tensor_word_column_prefix j -> j<count ->
  current!column_cursor=Some(Vint(Int.repr j)) -> current!column_limit=Some(Vint(Int.repr count)) ->
  current!flag=Some(memory_boolean_word true) -> temp_agree live base current -> exists after,
    exec_stmt fe(entry_ge entry)(entry_env entry)current(entry_memory entry)tensor_word_column_component_code
      E0 after(entry_memory entry)Out_normal /\
    temp_agree component_live current after /\ after!flag=Some(memory_boolean_word(tensor_word_column_test j)).
Proof.
  intros PREFIX ACTIVE CURSOR LIMIT FLAG FRAME.
  pose proof(tensor_word_column_runtime_frame CURSOR LIMIT FRAME)as RUNTIME.
  assert(RUN:exists after,
    exec_stmt fe(entry_ge entry)(entry_env entry)current(entry_memory entry)tensor_word_column_component_code E0 after(entry_memory entry)Out_normal /\
    temp_agree component_live current after /\
    after!flag=Some(memory_boolean_word(word_component_result pointer component_cursor index rename current observers upper)) /\
    (word_component_result pointer component_cursor index rename current observers upper=true -> forall point,0<=point<upper ->
      expression_body_preserved fe iterator(direct_word_store pointer index rhs)(column::stable)
        (fun _=>snapshots)point(Entry(entry_ge entry)(entry_env entry)(tensor_word_column_source_base j)(entry_memory entry)))).
  { eapply(@word_component_scan_execution fe(entry_ge entry)(entry_env entry)(entry_memory entry)
      iterator helper pointer component_cursor component_limit flag index rhs rename(column::stable)component_live
      (tensor_word_column_source_base j)current observers upper).
    - exact WORD.
    - exact NONNEGATIVE.
    - exact UPPER.
    - apply tensor_word_column_component_cache with(stable:=stable); assumption.
    - cbn; intros [SAME|MEMBER]; [congruence|contradiction].
    - right; exact POINTER_STABLE.
    - right; right; exact POINTER_LIVE.
    - rewrite RUNTIME by(right; right; exact POINTER_LIVE); apply tensor_word_column_component_pointer.
    - exact SOURCE_SCOPE.
    - exact RENAME_ITERATOR.
    - exact tensor_word_column_renamed_stable.
    - intros id MEMBER; rewrite RUNTIME by(apply tensor_word_column_renamed_stable,in_map; exact MEMBER).
      apply tensor_word_column_component_words; exact MEMBER.
    - exact COMPONENT_CONTROLS.
    - exact COMPONENT_CURSOR_FLAG.
    - exact COMPONENT_LIMIT_FLAG.
    - exact COMPONENT_CURSOR_PRIVATE.
    - exact COMPONENT_LIMIT_PRIVATE.
    - cbn; intros [SAME|[SAME|MEMBER]]; congruence.
    - rewrite Forall_forall in READS|-*; intros observer MEMBER.
      eapply word_observer_receipt_frame; [apply READS; exact MEMBER|apply OBSERVER_SCOPE; exact MEMBER|exact FRAME].
    - intros observer MEMBER id READ; right; right; exact(OBSERVER_SCOPE observer MEMBER id READ).
    - apply tensor_word_column_component_ready; assumption.
    - exact FLAG.
    - apply temp_agree_refl. }
  destruct RUN as [after [RUN [PUBLIC [RESULT PRESERVE]]]].
  rewrite(@tensor_word_component_result_base_frame pointer component_cursor index rename observers component_live
    (tensor_word_column_guard_base j)current upper WORD COMPONENT_CURSOR_PRIVATE
    ltac:(right; right; exact POINTER_LIVE)tensor_word_column_renamed_scope RUNTIME)in RESULT.
  exists after; split; [exact RUN|split; assumption].
Qed.

Theorem tensor_word_column_component_preserved j : tensor_word_column_prefix j -> j<count -> tensor_word_column_test j=true ->
  expression_body_preserved fe column source stable(fun _=>snapshots)j entry.
Proof.
  intros PREFIX ACTIVE ACCEPT original memory after final COUNTER FRAME OBSERVED SOURCE.
  destruct(sequence_normal_decode SOURCE)as [reset [reset_memory [RESET LOOP]]].
  destruct(rectangle_reset_decode RESET)as [_ [TEMPS [MEMORY _]]]; subst reset reset_memory.
  assert(TRANSPORT:
    exec_stmt fe(entry_ge entry)(entry_env entry)(PTree.set iterator(Vint Int.zero)original)memory
      (frontend_counted_loop iterator helper(direct_word_store pointer index rhs))E0 after final Out_normal /\
    header_observations_match snapshots final).
  { eapply(@word_component_accepted_source_transport fe(entry_ge entry)(entry_env entry)(entry_memory entry)
      iterator helper pointer component_cursor component_limit flag index rhs rename(column::stable)component_live
      (tensor_word_column_source_base j)(tensor_word_column_guard_base j)observers upper)with(i:=0).
    - exact WORD.
    - exact NONNEGATIVE.
    - exact UPPER.
    - apply tensor_word_column_component_cache with(stable:=stable); assumption.
    - right; exact HELPER.
    - cbn; intros [SAME|MEMBER]; [congruence|contradiction].
    - right; exact POINTER_STABLE.
    - right; right; exact POINTER_LIVE.
    - apply tensor_word_column_component_pointer.
    - exact SOURCE_SCOPE.
    - exact RENAME_ITERATOR.
    - exact tensor_word_column_renamed_stable.
    - exact(tensor_word_column_component_words j).
    - exact COMPONENT_CONTROLS.
    - exact COMPONENT_CURSOR_FLAG.
    - exact COMPONENT_LIMIT_FLAG.
    - exact COMPONENT_CURSOR_PRIVATE.
    - exact COMPONENT_LIMIT_PRIVATE.
    - cbn; intros [SAME|[SAME|MEMBER]]; congruence.
    - rewrite Forall_forall in READS|-*; intros observer MEMBER.
      eapply word_observer_receipt_frame; [apply READS; exact MEMBER|apply OBSERVER_SCOPE; exact MEMBER|apply tensor_word_column_live_frame].
    - intros observer MEMBER id READ; right; right; exact(OBSERVER_SCOPE observer MEMBER id READ).
    - apply tensor_word_column_component_ready; assumption.
    - exact ACCEPT.
    - lia.
    - apply PTree.gss.
    - apply tensor_word_column_component_frame; assumption.
    - exact OBSERVED.
    - exact LOOP. }
  exact(proj2 TRANSPORT).
Qed.

Theorem tensor_word_column_next_prefix j :
  0<=j<count -> tensor_word_column_prefix j -> tensor_word_column_test j=true -> tensor_word_column_prefix(j+1).
Proof.
  intros RANGE PREFIX ACCEPT; unfold tensor_word_column_prefix.
  eapply expression_body_prefix_advance_at with(written:=[iterator]); try eassumption.
  - reflexivity.
  - reflexivity.
  - apply tensor_word_column_source_writes.
  - cbn; intros [SAME|[]]; congruence.
  - intros id MEMBER; cbn; intros [SAME|[]]; subst id; contradiction.
  - intros ge locals current before after final RUN; eapply structured_memory_accesses_back;
      [exact RUN|apply tensor_word_column_source_writes].
  - exact(proj2 RANGE).
  - apply tensor_word_column_component_preserved; [exact PREFIX|lia|exact ACCEPT].
Qed.

Theorem tensor_word_column_scan_execution current : tensor_word_column_prefix 0 ->
  current!flag=Some(memory_boolean_word true) -> temp_agree live base current -> exists after,
    exec_stmt fe(entry_ge entry)(entry_env entry)current(entry_memory entry)tensor_word_column_code E0 after(entry_memory entry)Out_normal /\
    temp_agree live current after /\ after!flag=Some(memory_boolean_word tensor_word_column_result) /\
    (tensor_word_column_result=true -> forall j,0<=j<count -> expression_body_preserved fe column source stable(fun _=>snapshots)j entry).
Proof.
  intros PREFIX FLAG FRAME; pose proof PREFIX as [_ [BOUND [RANGE _]]].
  assert(NONNEG:0<=count)by lia.
  set(cached:=PTree.set column_limit(Vint(temp_word cache(entry_temps entry)))current).
  set(prepared:=PTree.set column_cursor(Vint Int.zero)cached).
  assert(PUBLIC:temp_agree live current prepared).
  { unfold prepared,cached; eapply temp_agree_trans; apply temp_agree_set; assumption. }
  assert(CURSOR:prepared!column_cursor=Some(Vint(Int.repr 0)))by(apply PTree.gss).
  assert(LIMIT:prepared!column_limit=Some(Vint(Int.repr count))).
  { unfold prepared,cached; rewrite PTree.gso by congruence; rewrite PTree.gss;
      unfold count; rewrite Int.repr_signed; reflexivity. }
  assert(TRUE:prepared!flag=Some(memory_boolean_word true)).
  { unfold prepared,cached; rewrite !PTree.gso by congruence; exact FLAG. }
  destruct(@short_circuit_prefix_loop_execution fe(entry_ge entry)(entry_env entry)(entry_memory entry)
    column_cursor column_limit flag tensor_word_column_component_code live base 0 count tensor_word_column_prefix tensor_word_column_test
    COLUMN_CONTROLS COLUMN_CURSOR_FLAG COLUMN_LIMIT_FLAG COLUMN_CURSOR_PRIVATE(Int.signed_range _)
    tensor_word_column_next_prefix ltac:(intros; eapply tensor_word_column_component_execution; eauto; lia)
    (Z.to_nat count)0 prepared)as [after [LOOP [KEEP [RESULT CHECKED]]]].
  - rewrite Z2Nat.id by exact NONNEG; lia.
  - lia.
  - change(-2147483648<=0<=2147483647); lia.
  - exact PREFIX.
  - exact CURSOR.
  - exact LIMIT.
  - exact TRUE.
  - eapply temp_agree_trans; eassumption.
  - exists after; split.
    + unfold tensor_word_column_code,tensor_word_column_scan_code.
      eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=cached)(m1:=entry_memory entry).
      * constructor; constructor; rewrite FRAME by exact BOUND_LIVE; rewrite BOUND_WORD.
        destruct BOUND as [word VALUE]; unfold temp_word; rewrite VALUE; reflexivity.
      * eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=prepared)(m1:=entry_memory entry); [constructor; constructor|exact LOOP].
    + split; [eapply temp_agree_trans; eassumption|split; [exact RESULT|]].
      intros ACCEPT j ACTIVE; destruct(CHECKED ACCEPT j ACTIVE)as [INV CHECK].
      eapply tensor_word_column_component_preserved; eauto; lia.
Qed.

Theorem tensor_word_column_accepted_source_transport j original memory trace after final outcome :
  tensor_word_column_prefix 0 -> tensor_word_column_result=true -> 0<=j<=count ->
  original!column=Some(Vint(Int.repr j)) -> temp_agree stable(entry_temps entry)original ->
  header_observations_match snapshots memory ->
  exec_stmt fe(entry_ge entry)(entry_env entry)original memory
    (strict_frontend_loop column(signed_expression_test column bound)source)trace after final outcome ->
  exec_stmt fe(entry_ge entry)(entry_env entry)original memory(frontend_counted_loop column cache source)trace after final outcome /\
    header_observations_match snapshots final.
Proof.
  intros PREFIX ACCEPT RANGE COUNTER FRAME OBSERVED SOURCE.
  pose proof PREFIX as [READY [[word VALUE] _]].
  assert(CACHE_WORD:(entry_temps entry)!cache=Some(Vint(temp_word cache(entry_temps entry)))).
  { unfold temp_word; rewrite VALUE; reflexivity. }
  destruct(@tensor_word_column_scan_execution(PTree.set flag(memory_boolean_word true)base)PREFIX(PTree.gss _ _ _)
    ltac:(apply temp_agree_set; exact FLAG_PRIVATE))as [checked [RUN [PUBLIC [RESULT PRESERVE]]]].
  assert(CACHED:
    exec_stmt fe(entry_ge entry)(entry_env entry)original memory(frontend_counted_loop column cache source)trace after final outcome /\
    expression_body_snapshot column stable(entry_temps entry)snapshots count after final).
  { eapply(@expression_body_bound_cached fe(entry_ge entry)(entry_env entry)column cache bound source
      stable[iterator](entry_temps entry)snapshots(temp_word cache(entry_temps entry)))with(temps:=original)(memory:=memory).
    - exact TYPE.
    - exact CACHE_WORD.
    - exact BOUND_STABLE.
    - exact COLUMN_PRIVATE.
    - reflexivity.
    - reflexivity.
    - apply tensor_word_column_source_writes.
    - cbn; intros [SAME|[]]; congruence.
    - intros id MEMBER; cbn; intros [SAME|[]]; subst id; contradiction.
    - intros point current before ACTIVE ROW STABLE INITIAL; eapply HEADER; eassumption.
    - intros point current before exit last ACTIVE ROW STABLE INITIAL BODY.
      exact(PRESERVE ACCEPT point ACTIVE current before exit last ROW STABLE INITIAL BODY).
    - exists j; split; [exact RANGE|split; [exact COUNTER|split; assumption]].
    - exact SOURCE. }
  destruct CACHED as [MODEL [last [LAST_RANGE [LAST_COUNTER [LAST_FRAME LAST_OBSERVED]]]]].
  split; assumption.
Qed.
Theorem tensor_word_column_first_refusal current :
  tensor_word_column_prefix 0 -> 0<count -> tensor_word_column_test 0=false ->
  current!flag=Some(memory_boolean_word true) -> temp_agree live base current ->
  exists after,
    exec_stmt fe(entry_ge entry)(entry_env entry) current(entry_memory entry)
      (tensor_word_column_code)
      E0 after(entry_memory entry) Out_normal /\ temp_agree live current after /\
    after!column_cursor=Some(Vint Int.zero) /\ after!flag=Some(memory_boolean_word false).
Proof.
  intros PREFIX ACTIVE REFUSE FLAG FRAME.
  pose proof PREFIX as [READY [BOUND [RANGE REST]]].
  set(cached:=PTree.set column_limit(Vint(temp_word cache(entry_temps entry))) current).
  set(initialized:=PTree.set column_cursor(Vint Int.zero) cached).
  assert (INIT_FRAME : temp_agree live current initialized).
  { eapply temp_agree_trans with(le1:=cached); apply temp_agree_set; assumption. }
  assert (INIT_CURSOR : initialized!column_cursor=Some(Vint(Int.repr 0))) by(unfold initialized; apply PTree.gss).
  assert (INIT_BOUND : initialized!column_limit=Some(Vint(Int.repr count))).
  { unfold initialized,cached; rewrite PTree.gso by congruence; rewrite PTree.gss; unfold count; rewrite Int.repr_signed; reflexivity. }
  assert (INIT_FLAG : initialized!flag=Some(memory_boolean_word true)).
  { unfold initialized,cached; rewrite !PTree.gso by congruence; exact FLAG. }
  assert (FIRST : exists after,
    exec_stmt fe(entry_ge entry)(entry_env entry) initialized(entry_memory entry)
      (tensor_word_column_component_code) E0 after(entry_memory entry) Out_normal /\
    temp_agree(column_cursor::column_limit::live) initialized after /\ after!flag=Some(memory_boolean_word(tensor_word_column_test 0))).
  { eapply tensor_word_column_component_execution;
      [exact PREFIX|lia|exact INIT_CURSOR|exact INIT_BOUND|exact INIT_FLAG|eapply temp_agree_trans; eassumption]. }
  destruct FIRST as [after [BODY [KEEP RESULT]]].
  rewrite REFUSE in RESULT.
  assert (STOP : exec_stmt fe(entry_ge entry)(entry_env entry) initialized(entry_memory entry)
    (short_circuit_prefix_loop column_cursor column_limit flag(tensor_word_column_component_code))
    E0 after(entry_memory entry) Out_normal).
  { unfold short_circuit_prefix_loop,counted_loop.
    destruct(@counter_condition_at(entry_ge entry)(entry_env entry) initialized(entry_memory entry) column_cursor column_limit 0 count
      COLUMN_CONTROLS INIT_CURSOR INIT_BOUND
      ltac:(unfold signed_range; change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia)
      (Int.signed_range(temp_word cache(entry_temps entry)))) as [value [EVAL BOOL]].
    assert (LT : (0<?count)=true) by(apply Z.ltb_lt; exact ACTIVE); rewrite LT in BOOL.
    eapply exec_Sloop_stop1 with(out':=Out_break); [|constructor].
    eapply exec_Sifthenelse; [exact EVAL|exact BOOL|].
    eapply short_circuit_point_execution with(answer:=false); eassumption. }
  exists after; split.
  - unfold tensor_word_column_code,tensor_word_column_scan_code.
    eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=cached)(m1:=entry_memory entry).
    + constructor; constructor.
      assert (DEFINED_CACHE : (entry_temps entry)!cache=Some(Vint(temp_word cache(entry_temps entry)))).
      { destruct BOUND as [word VALUE]; unfold temp_word; rewrite VALUE; reflexivity. }
      rewrite FRAME by exact BOUND_LIVE; rewrite BOUND_WORD; exact DEFINED_CACHE.
    + eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=initialized)(m1:=entry_memory entry); [constructor; constructor|exact STOP].
  - split.
    + eapply temp_agree_trans; [exact INIT_FRAME|].
      eapply temp_agree_weaken; [|exact KEEP]; intros identifier MEMBER; right; right; exact MEMBER.
    + split; [rewrite KEEP by(left; reflexivity); exact INIT_CURSOR|exact RESULT].
Qed.

Theorem tensor_word_column_current_row_execution origin row root_cache root_bound outer_stable outer_ready row_index checked :
  stable=row::outer_stable -> entry=nested_expression_inner_entry row column row_index origin ->
  ~In row outer_stable -> ~In column outer_stable -> row<>column -> In cache outer_stable ->
  typeof root_bound=type_int32s -> register_domain cache origin -> 0<=count -> ready entry ->
  (forall k current memory,outer_ready origin -> 0<=k<=Int.signed(temp_word root_cache(entry_temps origin)) ->
    current!row=Some(Vint(Int.repr k)) -> temp_agree outer_stable(entry_temps origin) current ->
    header_observations_match snapshots memory ->
    eval_expr(entry_ge origin)(entry_env origin) current memory root_bound(Vint(temp_word root_cache(entry_temps origin)))) ->
  expression_body_prefix fe row root_cache root_bound(nested_expression_body column bound source) outer_stable
    outer_ready(fun _=>snapshots) row_index origin -> row_index<Int.signed(temp_word root_cache(entry_temps origin)) ->
  checked!flag=Some(memory_boolean_word true) -> temp_agree live base checked -> exists after,
    exec_stmt fe(entry_ge origin)(entry_env origin) checked(entry_memory origin)
      (tensor_word_column_code)
      E0 after(entry_memory origin) Out_normal /\ temp_agree live checked after /\
    after!flag=Some(memory_boolean_word(tensor_word_column_result)) /\
    (tensor_word_column_result=true ->
      (forall j current memory exit final,0<=j<Int.signed(temp_word cache(entry_temps origin)) ->
        current!row=Some(Vint(Int.repr row_index)) -> current!column=Some(Vint(Int.repr j)) ->
        temp_agree outer_stable(entry_temps origin) current -> header_observations_match snapshots memory ->
        exec_stmt fe(entry_ge origin)(entry_env origin) current memory source E0 exit final Out_normal ->
        header_observations_match snapshots final) /\
      expression_body_prefix fe row root_cache root_bound(nested_expression_body column bound source) outer_stable
        outer_ready(fun _=>snapshots)(row_index+1) origin).
Proof.
  intros STABLE ENTRY ROW_PRIVATE COLUMN_FRESH DISTINCT CACHE_MEMBER ROOT_TYPE CACHE_DOMAIN CHILD_NONNEGATIVE INNER_READY
    ROOT_HEADER PREFIX ACTIVE FLAG FRAME.
  pose proof PREFIX as [OUTER_READY [ROOT_DOMAIN [ROOT_RANGE REST]]].
  assert (CACHE_WORD : temp_word cache(entry_temps entry)=temp_word cache(entry_temps origin)).
  { unfold temp_word; rewrite ENTRY;
      rewrite(@joint_inner_cache_frame row column row_index origin outer_stable cache ROW_PRIVATE COLUMN_FRESH CACHE_MEMBER); reflexivity. }
  assert (COUNT : count=Int.signed(temp_word cache(entry_temps origin))) by(unfold count; rewrite CACHE_WORD; reflexivity).
  assert (INITIAL : tensor_word_column_prefix 0).
  { unfold tensor_word_column_prefix.
    eapply expression_body_prefix_ready_change with(first:=fun _=>outer_ready origin); [|exact INNER_READY].
    rewrite ENTRY,STABLE.
    eapply nested_expression_prefix_open with(entry:=origin)(row:=row)(cache:=root_cache)(bound:=root_bound)
      (column:=column)(child_cache:=cache)(child_bound:=bound)(body:=source)(stable:=outer_stable)(i:=row_index)
      (ready:=outer_ready)(observations:=fun _=>snapshots)(fe:=fe);
      [exact ROOT_TYPE|reflexivity|exact ROW_PRIVATE|exact COLUMN_FRESH|exact DISTINCT|exact CACHE_MEMBER|
       exact CACHE_DOMAIN|rewrite <-COUNT; exact CHILD_NONNEGATIVE| |exact PREFIX|exact ACTIVE].
    intros current memory ROW CURRENT OBSERVED; eapply ROOT_HEADER; eassumption. }
  assert (INNER : exists after,
    exec_stmt fe(entry_ge entry)(entry_env entry) checked(entry_memory entry)
      (tensor_word_column_code)
      E0 after(entry_memory entry) Out_normal /\ temp_agree live checked after /\
    after!flag=Some(memory_boolean_word(tensor_word_column_result)) /\
    (tensor_word_column_result=true -> forall j,0<=j<count ->
      expression_body_preserved fe column source stable(fun _=>snapshots) j entry)).
  { apply tensor_word_column_scan_execution; assumption. }
  destruct INNER as [after [RUN [KEEP [RESULT PRESERVES]]]].
  exists after; split.
  - rewrite ENTRY in RUN; cbn [nested_expression_inner_entry entry_ge entry_env entry_memory] in RUN; exact RUN.
  - split; [exact KEEP|split; [exact RESULT|]].
    intro ACCEPT.
    assert (ROW_PRESERVED : forall j current memory exit final,0<=j<Int.signed(temp_word cache(entry_temps origin)) ->
      current!row=Some(Vint(Int.repr row_index)) -> current!column=Some(Vint(Int.repr j)) ->
      temp_agree outer_stable(entry_temps origin) current -> header_observations_match snapshots memory ->
      exec_stmt fe(entry_ge origin)(entry_env origin) current memory source E0 exit final Out_normal ->
      header_observations_match snapshots final).
    { intros j current memory exit final RANGE ROW COLUMN CURRENT OBSERVED SOURCE.
      pose proof(PRESERVES ACCEPT j ltac:(rewrite COUNT; exact RANGE)) as PRESERVE.
      eapply PRESERVE; [exact COLUMN| |exact OBSERVED|].
      - rewrite STABLE,ENTRY; eapply joint_inner_row_frame; eassumption.
      - rewrite ENTRY; cbn [nested_expression_inner_entry entry_ge entry_env]; exact SOURCE. }
    split; [exact ROW_PRESERVED|].
    eapply expression_body_prefix_ready_change with(first:=fun other=>outer_ready other /\ other=origin); [|exact OUTER_READY].
    eapply nested_expression_prefix_advance with(child_cache:=cache)(written:=[iterator])
      (ready:=fun other=>outer_ready other /\ other=origin);
      [exact ROOT_TYPE|exact TYPE|exact ROW_PRIVATE|exact COLUMN_FRESH|exact DISTINCT|exact CACHE_MEMBER|
       reflexivity|reflexivity|apply tensor_word_column_source_writes| |cbn; intros [SAME|[]]; congruence| | |exact CACHE_DOMAIN|
       rewrite <-COUNT; exact CHILD_NONNEGATIVE| | | |exact ACTIVE].
    + cbn; intros [SAME|[]]; apply ITERATOR_PRIVATE; rewrite STABLE; left; congruence.
    + intros identifier MEMBER; cbn; intros [SAME|[]]; apply ITERATOR_PRIVATE; rewrite STABLE; right; congruence.
    + intros other k current memory [READY SAME]; subst other; eapply ROOT_HEADER; eassumption.
    + intros j current memory RANGE ROW COLUMN CURRENT OBSERVED.
      rewrite <-CACHE_WORD.
      replace(entry_ge origin) with(entry_ge entry) by(rewrite ENTRY; reflexivity).
      replace(entry_env origin) with(entry_env entry) by(rewrite ENTRY; reflexivity).
      eapply HEADER; [exact INNER_READY|rewrite COUNT; exact RANGE|exact COLUMN| |exact OBSERVED].
      rewrite STABLE,ENTRY; eapply joint_inner_row_frame; eassumption.
    + exact ROW_PRESERVED.
    + eapply expression_body_prefix_ready_change with(first:=outer_ready); [exact PREFIX|split; [exact OUTER_READY|reflexivity]].
Qed.
End COLUMN.

(** A zero child count licenses no point reads. This theorem requires no
    source prefix, observer receipt, word operands or executable component. *)
Theorem tensor_word_column_empty_execution fe ge locals memory cache cursor limit flag component current live :
  cursor<>limit -> cursor<>flag -> limit<>flag -> ~In cursor live -> ~In limit live ->
  current!cache=Some(Vint Int.zero) ->
  let initialized:=PTree.set cursor(Vint Int.zero)(PTree.set limit(Vint Int.zero)current)in
  exec_stmt fe ge locals current memory(tensor_word_column_scan_code cache cursor limit flag component)
    E0 initialized memory Out_normal /\ temp_agree(flag::live)current initialized.
Proof.
  intros DISTINCT CURSOR_FLAG LIMIT_FLAG CURSOR_PRIVATE LIMIT_PRIVATE CACHE; cbn zeta.
  set(cached:=PTree.set limit(Vint Int.zero)current).
  set(initialized:=PTree.set cursor(Vint Int.zero)cached).
  assert(CURSOR:initialized!cursor=Some(Vint(Int.repr 0)))by(apply PTree.gss).
  assert(LIMIT:initialized!limit=Some(Vint(Int.repr 0))).
  { unfold initialized,cached; rewrite PTree.gso by congruence; apply PTree.gss. }
  assert(LOOP:exec_stmt fe ge locals initialized memory(short_circuit_prefix_loop cursor limit flag component)
      E0 initialized memory Out_normal).
  { unfold short_circuit_prefix_loop,counted_loop.
    destruct(@counter_condition_at ge locals initialized memory cursor limit 0 0 DISTINCT CURSOR LIMIT
      ltac:(change(-2147483648<=0<=2147483647); lia)
      ltac:(change(-2147483648<=0<=2147483647); lia))as [value [EVAL BOOL]].
    rewrite Z.ltb_irrefl in BOOL.
    eapply exec_Sloop_stop1 with(out':=Out_break); [|constructor].
    eapply exec_Sifthenelse; [exact EVAL|exact BOOL|constructor]. }
  split.
  - unfold tensor_word_column_scan_code.
    eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=cached)(m1:=memory); [constructor; constructor; exact CACHE|].
    eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=initialized)(m1:=memory); [constructor; constructor|exact LOOP].
  - eapply temp_agree_trans with(le1:=cached).
    + apply temp_agree_set; cbn; intros [SAME|MEMBER]; [congruence|exact(LIMIT_PRIVATE MEMBER)].
    + apply temp_agree_set; cbn; intros [SAME|MEMBER]; [congruence|exact(CURSOR_PRIVATE MEMBER)].
Qed.


Print Assumptions tensor_word_component_point_base_frame.
Print Assumptions tensor_word_component_result_base_frame.
Print Assumptions tensor_word_column_component_cache.
Print Assumptions tensor_word_column_component_frame.
Print Assumptions tensor_word_column_source_writes.
Print Assumptions tensor_word_column_component_prefix_open.
Print Assumptions tensor_word_column_live_frame.
Print Assumptions tensor_word_column_runtime_frame.
Print Assumptions tensor_word_column_renamed_scope.
Print Assumptions tensor_word_column_component_words.
Print Assumptions tensor_word_column_component_pointer.
Print Assumptions tensor_word_column_component_ready.
Print Assumptions tensor_word_column_component_execution.
Print Assumptions tensor_word_column_component_preserved.
Print Assumptions tensor_word_column_next_prefix.
Print Assumptions tensor_word_column_scan_execution.
Print Assumptions tensor_word_column_accepted_source_transport.
Print Assumptions tensor_word_column_first_refusal.
Print Assumptions tensor_word_column_current_row_execution.
Print Assumptions tensor_word_column_empty_execution.
