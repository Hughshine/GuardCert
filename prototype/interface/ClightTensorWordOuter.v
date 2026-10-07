(** Complete source-licensed scans for loaded root/child bounds and word
    addresses. Future source permissions follow only from accepted prefixes. *)
From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightTempFrame ClightTempFootprint ClightCondition ClightNoWrap
  ClightCountedLoop ClightRectangularLoops ClightLoopSyntax ClightRegionProgress
  ClightFramedLoop ClightFrontendLoopProtocol ClightRedundantSet ClightProjectedExecution.
From GuardMemory Require Import GuardMemoryBooleanScan.
From GuardInterface Require Import ClightWordArithmeticTransport ClightWordCoordinateRename
  ClightDirectWordObservation ClightWordComponentScan ClightConstantBoundModel
  ClightAffineJointObservation ClightObservedHeaderPrefix ClightExpressionBodyPrefix
  ClightStrictLoopProgress ClightSignedExpressionProgress ClightShortCircuitPrefixLoop
  ClightNestedExpressionCapture ClightNestedExpressionPrefix ClightNestedExpressionTransport ClightExpressionReachedPrefix
  ClightJointInnerRowFrame ClightTensorWordColumn ClightEmptyExpressionTransport ClightCheckPlanFrame.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition tensor_word_outer_scan_code root_cache row_cursor row_limit flag row_code :=
  Ssequence(Sset row_limit(Etempvar root_cache type_int32s))
    (Ssequence(Sset flag(Econst_int Int.one type_int32s))
      (Ssequence(Sset row_cursor(Econst_int Int.zero type_int32s))
        (short_circuit_prefix_loop row_cursor row_limit flag row_code))).

Definition tensor_word_outer_statement root_cache child_cache pointer row_cursor row_limit column_cursor column_limit
    component_cursor component_limit flag index upper rename observers :=
  tensor_word_outer_scan_code root_cache row_cursor row_limit flag
    (tensor_word_column_code child_cache pointer column_cursor column_limit component_cursor component_limit
      flag index upper rename observers).

(** An empty outer loop never evaluates its child code. Its cache is the only
    source value needed; observers, pointers and child caches may be undefined. *)
Theorem tensor_word_outer_empty_execution fe ge locals memory root_cache row_cursor row_limit flag row_code temps live :
  row_cursor<>row_limit -> row_cursor<>flag -> row_limit<>flag ->
  ~In row_cursor live -> ~In row_limit live -> ~In flag live ->
  temps!root_cache=Some(Vint Int.zero) ->
  let after:=PTree.set row_cursor(Vint Int.zero)
    (PTree.set flag(memory_boolean_word true)(PTree.set row_limit(Vint Int.zero)temps))in
  exec_stmt fe ge locals temps memory(tensor_word_outer_scan_code root_cache row_cursor row_limit flag row_code)
    E0 after memory Out_normal /\ temp_agree live temps after /\ after!flag=Some(memory_boolean_word true).
Proof.
  intros DISTINCT CURSOR_FLAG LIMIT_FLAG CURSOR_PRIVATE LIMIT_PRIVATE FLAG_PRIVATE ROOT; cbn zeta.
  split.
  - unfold tensor_word_outer_scan_code.
    eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [constructor; constructor; exact ROOT|].
    eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [constructor; constructor|].
    eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [constructor; constructor|].
    unfold short_circuit_prefix_loop,counted_loop; eapply exec_Sloop_stop1 with(out':=Out_break); [|constructor].
    destruct(@counter_condition_at ge locals
      (PTree.set row_cursor(Vint Int.zero)(PTree.set flag(memory_boolean_word true)(PTree.set row_limit(Vint Int.zero)temps)))
      memory row_cursor row_limit 0 0 DISTINCT(PTree.gss _ _ _)
      ltac:(rewrite !PTree.gso by congruence; apply PTree.gss)
      ltac:(change(-2147483648<=0<=2147483647); lia)ltac:(change(-2147483648<=0<=2147483647); lia))
      as [value [EVAL BOOL]].
    rewrite Z.ltb_irrefl in BOOL; eapply exec_Sifthenelse; [exact EVAL|exact BOOL|constructor].
  - split.
    + eapply temp_agree_trans; [apply temp_agree_set; exact LIMIT_PRIVATE|].
      eapply temp_agree_trans; apply temp_agree_set; assumption.
    + rewrite PTree.gso by congruence; apply PTree.gss.
Qed.

(** A refused first row stops the outer cursor without requiring an execution
    or a safety premise for any later row. *)
Theorem tensor_word_outer_first_refusal fe ge locals memory root_cache row_cursor row_limit flag row_code temps word after :
  row_cursor<>row_limit -> row_cursor<>flag -> row_limit<>flag ->
  temps!root_cache=Some(Vint word) -> 0<Int.signed word ->
  let initialized:=PTree.set row_cursor(Vint Int.zero)
    (PTree.set flag(memory_boolean_word true)(PTree.set row_limit(Vint word)temps))in
  exec_stmt fe ge locals initialized memory row_code E0 after memory Out_normal ->
  temp_agree[row_cursor;row_limit]initialized after -> after!flag=Some(memory_boolean_word false) ->
  exec_stmt fe ge locals temps memory(tensor_word_outer_scan_code root_cache row_cursor row_limit flag row_code)
    E0 after memory Out_normal /\ after!row_cursor=Some(Vint Int.zero).
Proof.
  intros DISTINCT CURSOR_FLAG LIMIT_FLAG ROOT POSITIVE; cbn zeta; intros BODY FRAME FLAG; split.
  - unfold tensor_word_outer_scan_code.
    eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [constructor; constructor; exact ROOT|].
    eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [constructor; constructor|].
    eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [constructor; constructor|].
    unfold short_circuit_prefix_loop,counted_loop; eapply exec_Sloop_stop1 with(out':=Out_break); [|constructor].
    destruct(@counter_condition_at ge locals
      (PTree.set row_cursor(Vint Int.zero)(PTree.set flag(memory_boolean_word true)(PTree.set row_limit(Vint word)temps)))
      memory row_cursor row_limit 0(Int.signed word)DISTINCT(PTree.gss _ _ _)
      ltac:(rewrite !PTree.gso by congruence; rewrite Int.repr_signed; apply PTree.gss)
      ltac:(change(-2147483648<=0<=2147483647); lia)(Int.signed_range word))as [value [EVAL BOOL]].
    assert(LT:(0<?Int.signed word)=true)by(apply Z.ltb_lt; exact POSITIVE); rewrite LT in BOOL.
    eapply exec_Sifthenelse; [exact EVAL|exact BOOL|].
    exact(@short_circuit_point_execution fe ge locals _ memory row_code after flag false BODY FLAG).
  - rewrite FRAME by(left; reflexivity); apply PTree.gss.
Qed.

Section OUTER.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable entry : clight_entry.
Variables iterator helper row column root_cache child_cache pointer : ident.
Variables row_cursor row_limit column_cursor column_limit component_cursor component_limit flag : ident.
Variables index rhs root_bound child_bound : expr.
Variable upper : Z.
Variable rename : ident -> ident.
Variables stable live : list ident.
Variable observers : list clight_word_observer.
Variable ready : clight_entry -> Prop.
Let source := constant_body_source iterator(Int.repr upper)(direct_word_store pointer index rhs).
Let snapshots := map word_observer_snapshot observers.
Let root_count := Int.signed(temp_word root_cache(entry_temps entry)).
Let child_count := Int.signed(temp_word child_cache(entry_temps entry)).
Let inner_live := row_cursor::row_limit::live.
Let component_live := column_cursor::column_limit::inner_live.
Definition tensor_word_outer_prefix i := expression_body_prefix fe row root_cache root_bound
  (nested_expression_body column child_bound source)stable ready(fun _=>snapshots)i entry.
Definition tensor_word_outer_inner_entry i := nested_expression_inner_entry row column i entry.
Definition tensor_word_outer_row_base i := PTree.set row_limit(Vint(Int.repr root_count))
  (PTree.set row_cursor(Vint(Int.repr i))(entry_temps entry)).
Definition tensor_word_outer_row_test i := tensor_word_column_result(tensor_word_outer_inner_entry i)
  child_cache pointer column_cursor column_limit component_cursor index upper rename(tensor_word_outer_row_base i)observers.
Definition tensor_word_outer_result := memory_boolean_scan_result tensor_word_outer_row_test 0(Z.to_nat root_count).
Let row_code := tensor_word_column_code child_cache pointer column_cursor column_limit component_cursor component_limit
  flag index upper rename observers.
Definition tensor_word_outer_code := tensor_word_outer_statement root_cache child_cache pointer row_cursor row_limit
  column_cursor column_limit component_cursor component_limit flag index upper rename observers.

Hypothesis WORD : word_arithmetic index.
Hypotheses (NONNEGATIVE : 0<=upper) (UPPER : signed_range upper).
Hypotheses (HELPER : In helper stable) (HELPER_WORD : (entry_temps entry)!helper=Some(Vint(Int.repr upper))).
Hypotheses (ROW_PRIVATE : ~In row stable) (COLUMN_PRIVATE : ~In column stable) (ITERATOR_PRIVATE : ~In iterator stable).
Hypotheses (ROW_COLUMN : row<>column) (ITERATOR_ROW : iterator<>row) (ITERATOR_COLUMN : iterator<>column).
Hypotheses (ROOT_TYPE : typeof root_bound=type_int32s) (CHILD_TYPE : typeof child_bound=type_int32s).
Hypothesis ROOT_HEADER : forall i current memory, ready entry -> 0<=i<=root_count ->
  current!row=Some(Vint(Int.repr i)) -> temp_agree stable(entry_temps entry)current ->
  header_observations_match snapshots memory ->
  eval_expr(entry_ge entry)(entry_env entry)current memory root_bound(Vint(temp_word root_cache(entry_temps entry))).
Hypothesis CHILD_HEADER : forall i j current memory,0<=i<root_count -> 0<=j<=child_count ->
  current!row=Some(Vint(Int.repr i)) -> current!column=Some(Vint(Int.repr j)) ->
  temp_agree stable(entry_temps entry)current -> header_observations_match snapshots memory ->
  eval_expr(entry_ge entry)(entry_env entry)current memory child_bound(Vint(temp_word child_cache(entry_temps entry))).
Hypotheses (CHILD_DOMAIN : 0<root_count -> register_domain child_cache entry)
  (CHILD_NONNEGATIVE : 0<root_count -> 0<=child_count).
Hypotheses (ROOT_STABLE : In root_cache stable) (CHILD_STABLE : In child_cache stable)
  (POINTER_STABLE : In pointer stable) (STABLE_LIVE : incl stable live).
Hypothesis SOURCE_SCOPE : incl(expression_temps index)(iterator::column::row::stable).
Hypotheses (RENAME_ITERATOR : rename iterator=component_cursor) (RENAME_COLUMN : rename column=column_cursor)
  (RENAME_ROW : rename row=row_cursor).
Hypothesis RENAME_STABLE : forall id,In id stable -> rename id=id.
Hypotheses (ROW_CURSOR_PRIVATE : ~In row_cursor live) (ROW_LIMIT_PRIVATE : ~In row_limit live)
  (COLUMN_CURSOR_PRIVATE : ~In column_cursor inner_live) (COLUMN_LIMIT_PRIVATE : ~In column_limit inner_live)
  (FLAG_PRIVATE : ~In flag inner_live) (COMPONENT_CURSOR_PRIVATE : ~In component_cursor component_live)
  (COMPONENT_LIMIT_PRIVATE : ~In component_limit component_live).
Hypotheses (ROW_CONTROLS : row_cursor<>row_limit) (ROW_CURSOR_FLAG : row_cursor<>flag) (ROW_LIMIT_FLAG : row_limit<>flag)
  (COLUMN_CONTROLS : column_cursor<>column_limit) (COLUMN_CURSOR_FLAG : column_cursor<>flag) (COLUMN_LIMIT_FLAG : column_limit<>flag)
  (COMPONENT_CONTROLS : component_cursor<>component_limit) (COMPONENT_CURSOR_FLAG : component_cursor<>flag)
  (COMPONENT_LIMIT_FLAG : component_limit<>flag).
Hypothesis READS : 0<root_count -> Forall(word_observer_receipt(entry_ge entry)(entry_env entry)
  (entry_temps entry)(entry_memory entry))observers.
Hypothesis OBSERVER_SCOPE : forall observer,In observer observers -> expression_scope live(word_observer_address observer).

Lemma tensor_word_outer_inner_stable i : temp_agree stable(entry_temps entry)(entry_temps(tensor_word_outer_inner_entry i)).
Proof.
  intros id MEMBER; unfold tensor_word_outer_inner_entry,nested_expression_inner_entry; cbn [entry_temps].
  rewrite !PTree.gso; try reflexivity; intro SAME; subst id; contradiction.
Qed.
Lemma tensor_word_outer_inner_cache i id : In id stable ->
  (entry_temps(tensor_word_outer_inner_entry i))!id=(entry_temps entry)!id.
Proof. intro MEMBER; apply tensor_word_outer_inner_stable; exact MEMBER. Qed.
Lemma tensor_word_outer_child_count i :
  Int.signed(temp_word child_cache(entry_temps(tensor_word_outer_inner_entry i)))=child_count.
Proof. unfold temp_word; rewrite tensor_word_outer_inner_cache by exact CHILD_STABLE; reflexivity. Qed.
Lemma tensor_word_outer_row_frame i : temp_agree live(entry_temps entry)(tensor_word_outer_row_base i).
Proof.
  unfold tensor_word_outer_row_base; eapply temp_agree_trans;
    [apply temp_agree_set; exact ROW_CURSOR_PRIVATE|apply temp_agree_set; exact ROW_LIMIT_PRIVATE].
Qed.
Lemma tensor_word_outer_runtime_frame i current :
  current!row_cursor=Some(Vint(Int.repr i)) -> current!row_limit=Some(Vint(Int.repr root_count)) ->
  temp_agree live(entry_temps entry)current -> temp_agree inner_live(tensor_word_outer_row_base i)current.
Proof.
  intros CURSOR LIMIT FRAME id [SAME|[SAME|MEMBER]].
  - subst id; unfold tensor_word_outer_row_base; rewrite PTree.gso by congruence; rewrite PTree.gss; exact CURSOR.
  - subst id; unfold tensor_word_outer_row_base; rewrite PTree.gss; exact LIMIT.
  - rewrite FRAME by exact MEMBER; symmetry; apply tensor_word_outer_row_frame; exact MEMBER.
Qed.
Lemma tensor_word_outer_renamed_stable : incl(map rename(row::stable))inner_live.
Proof.
  intros id MEMBER; apply in_map_iff in MEMBER as [raw [SAME MEMBER]]; subst id.
  destruct MEMBER as [SAME|MEMBER]; [subst raw; rewrite RENAME_ROW; left; reflexivity|].
  rewrite RENAME_STABLE by exact MEMBER; right; right; apply STABLE_LIVE; exact MEMBER.
Qed.
Lemma tensor_word_outer_source_words i : forall id,In id(row::stable) ->
  (entry_temps(tensor_word_outer_inner_entry i))!id=(tensor_word_outer_row_base i)!(rename id).
Proof.
  intros id [SAME|MEMBER].
  - subst id; unfold tensor_word_outer_inner_entry,nested_expression_inner_entry,tensor_word_outer_row_base; cbn [entry_temps].
    rewrite PTree.gso by congruence; rewrite PTree.gss,RENAME_ROW.
    rewrite PTree.gso by congruence; rewrite PTree.gss; reflexivity.
  - rewrite tensor_word_outer_inner_cache,RENAME_STABLE by exact MEMBER.
    symmetry; apply tensor_word_outer_row_frame,STABLE_LIVE; exact MEMBER.
Qed.

Theorem tensor_word_outer_row_execution i current :
  0<=i<root_count -> tensor_word_outer_prefix i ->
  current!row_cursor=Some(Vint(Int.repr i)) -> current!row_limit=Some(Vint(Int.repr root_count)) ->
  current!flag=Some(memory_boolean_word true) -> temp_agree live(entry_temps entry)current -> exists after,
    exec_stmt fe(entry_ge entry)(entry_env entry)current(entry_memory entry)row_code E0 after(entry_memory entry)Out_normal /\
    temp_agree inner_live current after /\ after!flag=Some(memory_boolean_word(tensor_word_outer_row_test i)) /\
    (tensor_word_outer_row_test i=true ->
      (forall j temps memory exit final,0<=j<child_count ->
        temps!row=Some(Vint(Int.repr i)) -> temps!column=Some(Vint(Int.repr j)) ->
        temp_agree stable(entry_temps entry)temps -> header_observations_match snapshots memory ->
        exec_stmt fe(entry_ge entry)(entry_env entry)temps memory source E0 exit final Out_normal ->
        header_observations_match snapshots final) /\ tensor_word_outer_prefix(i+1)).
Proof.
  intros RANGE PREFIX CURSOR LIMIT FLAG FRAME.
  unfold tensor_word_outer_row_test.
  eapply(@tensor_word_column_current_row_execution fe(tensor_word_outer_inner_entry i)
    iterator helper column child_cache pointer column_cursor column_limit component_cursor component_limit flag
    index rhs child_bound upper rename(row::stable)inner_live(tensor_word_outer_row_base i)observers(fun _=>True))
    with(origin:=entry)(row:=row)(root_cache:=root_cache)(root_bound:=root_bound)
      (outer_stable:=stable)(outer_ready:=ready)(row_index:=i)(checked:=current).
  - exact WORD.
  - exact NONNEGATIVE.
  - exact UPPER.
  - right; exact HELPER.
  - rewrite tensor_word_outer_inner_cache by exact HELPER; exact HELPER_WORD.
  - exact ITERATOR_COLUMN.
  - cbn; intros [SAME|MEMBER]; [congruence|exact(ITERATOR_PRIVATE MEMBER)].
  - cbn; intros [SAME|MEMBER]; [congruence|exact(COLUMN_PRIVATE MEMBER)].
  - exact CHILD_TYPE.
  - intros j current' memory _ ACTIVE COLUMN INNER OBSERVED.
    cbn [tensor_word_outer_inner_entry nested_expression_inner_entry entry_ge entry_env].
    unfold temp_word; rewrite tensor_word_outer_inner_cache by exact CHILD_STABLE;
      fold(temp_word child_cache(entry_temps entry)).
    eapply CHILD_HEADER; [exact RANGE|rewrite tensor_word_outer_child_count in ACTIVE; exact ACTIVE| |exact COLUMN| |exact OBSERVED].
    + rewrite INNER by(left; reflexivity).
      unfold tensor_word_outer_inner_entry,nested_expression_inner_entry; cbn [entry_temps];
        rewrite PTree.gso by congruence; apply PTree.gss.
    + intros id MEMBER; rewrite INNER by(right; exact MEMBER); apply tensor_word_outer_inner_stable; exact MEMBER.
  - right; exact POINTER_STABLE.
  - right; right; apply STABLE_LIVE; exact POINTER_STABLE.
  - rewrite tensor_word_outer_inner_cache by exact POINTER_STABLE; symmetry;
      apply tensor_word_outer_row_frame,STABLE_LIVE; exact POINTER_STABLE.
  - exact SOURCE_SCOPE.
  - exact RENAME_ITERATOR.
  - exact RENAME_COLUMN.
  - exact tensor_word_outer_renamed_stable.
  - exact(tensor_word_outer_source_words i).
  - exact COLUMN_CURSOR_PRIVATE.
  - exact COLUMN_LIMIT_PRIVATE.
  - exact FLAG_PRIVATE.
  - exact COLUMN_CONTROLS.
  - exact COLUMN_CURSOR_FLAG.
  - exact COLUMN_LIMIT_FLAG.
  - exact COMPONENT_CURSOR_PRIVATE.
  - exact COMPONENT_LIMIT_PRIVATE.
  - exact COMPONENT_CONTROLS.
  - exact COMPONENT_CURSOR_FLAG.
  - exact COMPONENT_LIMIT_FLAG.
  - right; right; apply STABLE_LIVE; exact CHILD_STABLE.
  - rewrite tensor_word_outer_inner_cache by exact CHILD_STABLE;
      apply tensor_word_outer_row_frame,STABLE_LIVE; exact CHILD_STABLE.
  - cbn [tensor_word_outer_inner_entry nested_expression_inner_entry entry_ge entry_env entry_memory].
    rewrite Forall_forall; intros observer MEMBER; eapply word_observer_receipt_frame.
    + pose proof(READS ltac:(lia))as CAPTURED; rewrite Forall_forall in CAPTURED;
        apply CAPTURED; exact MEMBER.
    + apply OBSERVER_SCOPE; exact MEMBER.
    + apply tensor_word_outer_row_frame.
  - intros observer MEMBER id READ; right; right; exact(OBSERVER_SCOPE observer MEMBER id READ).
  - reflexivity.
  - reflexivity.
  - exact ROW_PRIVATE.
  - exact COLUMN_PRIVATE.
  - exact ROW_COLUMN.
  - exact CHILD_STABLE.
  - exact ROOT_TYPE.
  - apply CHILD_DOMAIN; lia.
  - rewrite tensor_word_outer_child_count; apply CHILD_NONNEGATIVE; lia.
  - exact I.
  - exact ROOT_HEADER.
  - exact PREFIX.
  - exact(proj2 RANGE).
  - exact FLAG.
  - eapply tensor_word_outer_runtime_frame; eassumption.
Qed.

Let row_checked i := PTree.set flag(memory_boolean_word true)(tensor_word_outer_row_base i).
Lemma tensor_word_outer_row_checked_frame i : temp_agree live(entry_temps entry)(row_checked i).
Proof.
  unfold row_checked; eapply temp_agree_trans; [apply tensor_word_outer_row_frame|apply temp_agree_set].
  intro MEMBER; apply FLAG_PRIVATE; right; right; exact MEMBER.
Qed.
Lemma tensor_word_outer_row_accepted i :
  0<=i<root_count -> tensor_word_outer_prefix i -> tensor_word_outer_row_test i=true ->
  tensor_word_outer_prefix(i+1) /\
  (forall j temps memory exit final,0<=j<child_count ->
    temps!row=Some(Vint(Int.repr i)) -> temps!column=Some(Vint(Int.repr j)) ->
    temp_agree stable(entry_temps entry)temps -> header_observations_match snapshots memory ->
    exec_stmt fe(entry_ge entry)(entry_env entry)temps memory source E0 exit final Out_normal ->
    header_observations_match snapshots final).
Proof.
  intros RANGE PREFIX ACCEPT.
  destruct(@tensor_word_outer_row_execution i(row_checked i)RANGE PREFIX
    ltac:(unfold row_checked,tensor_word_outer_row_base; rewrite !PTree.gso by congruence; apply PTree.gss)
    ltac:(unfold row_checked,tensor_word_outer_row_base; rewrite PTree.gso by congruence; apply PTree.gss)
    ltac:(unfold row_checked; apply PTree.gss)(tensor_word_outer_row_checked_frame i))
    as [after [RUN [FRAME [RESULT SOUND]]]].
  destruct(SOUND ACCEPT)as [PRESERVE NEXT]; split; assumption.
Qed.
Lemma tensor_word_outer_next_prefix i :
  0<=i<root_count -> tensor_word_outer_prefix i -> tensor_word_outer_row_test i=true -> tensor_word_outer_prefix(i+1).
Proof. intros RANGE PREFIX ACCEPT; exact(proj1(tensor_word_outer_row_accepted RANGE PREFIX ACCEPT)). Qed.

Theorem tensor_word_outer_scan_execution current :
  tensor_word_outer_prefix 0 -> temp_agree live(entry_temps entry)current -> exists after,
    exec_stmt fe(entry_ge entry)(entry_env entry)current(entry_memory entry)tensor_word_outer_code
      E0 after(entry_memory entry)Out_normal /\ temp_agree live current after /\
    after!flag=Some(memory_boolean_word tensor_word_outer_result) /\
    (tensor_word_outer_result=true -> forall i,0<=i<root_count -> tensor_word_outer_prefix i /\
      tensor_word_outer_row_test i=true /\
      (forall j temps memory exit final,0<=j<child_count ->
        temps!row=Some(Vint(Int.repr i)) -> temps!column=Some(Vint(Int.repr j)) ->
        temp_agree stable(entry_temps entry)temps -> header_observations_match snapshots memory ->
        exec_stmt fe(entry_ge entry)(entry_env entry)temps memory source E0 exit final Out_normal ->
        header_observations_match snapshots final)).
Proof.
  intros PREFIX FRAME; pose proof PREFIX as [READY [CACHE [RANGE REST]]].
  assert(NONNEG:0<=root_count)by lia.
  assert(FLAG_LIVE_PRIVATE:~In flag live)by(intro MEMBER; apply FLAG_PRIVATE; right; right; exact MEMBER).
  set(cached:=PTree.set row_limit(Vint(temp_word root_cache(entry_temps entry)))current).
  set(flagged:=PTree.set flag(memory_boolean_word true)cached).
  set(initialized:=PTree.set row_cursor(Vint Int.zero)flagged).
  assert(INIT_FRAME:temp_agree live current initialized).
  { eapply temp_agree_trans with(le1:=cached); [apply temp_agree_set; exact ROW_LIMIT_PRIVATE|].
    eapply temp_agree_trans with(le1:=flagged); apply temp_agree_set; assumption. }
  assert(CURSOR:initialized!row_cursor=Some(Vint(Int.repr 0)))by(apply PTree.gss).
  assert(LIMIT:initialized!row_limit=Some(Vint(Int.repr root_count))).
  { unfold initialized,flagged,cached; rewrite !PTree.gso by congruence; rewrite PTree.gss;
      unfold root_count; rewrite Int.repr_signed; reflexivity. }
  assert(FLAG:initialized!flag=Some(memory_boolean_word true)).
  { unfold initialized,flagged; rewrite PTree.gso by congruence; apply PTree.gss. }
  assert(BODY:forall i current',signed_range i -> 0<=i<root_count -> tensor_word_outer_prefix i ->
    current'!row_cursor=Some(Vint(Int.repr i)) -> current'!row_limit=Some(Vint(Int.repr root_count)) ->
    current'!flag=Some(memory_boolean_word true) -> temp_agree live(entry_temps entry)current' -> exists after,
      exec_stmt fe(entry_ge entry)(entry_env entry)current'(entry_memory entry)row_code E0 after(entry_memory entry)Out_normal /\
      temp_agree inner_live current' after /\ after!flag=Some(memory_boolean_word(tensor_word_outer_row_test i))).
  { intros i current' SIGNED ACTIVE INV ROW LIMIT' FLAG' CURRENT.
    destruct(tensor_word_outer_row_execution ACTIVE INV ROW LIMIT' FLAG' CURRENT)as [after [RUN [KEEP [RESULT SOUND]]]].
    exists after; repeat split; assumption. }
  destruct(@short_circuit_prefix_loop_execution fe(entry_ge entry)(entry_env entry)(entry_memory entry)
    row_cursor row_limit flag row_code live(entry_temps entry)0 root_count tensor_word_outer_prefix tensor_word_outer_row_test
    ROW_CONTROLS ROW_CURSOR_FLAG ROW_LIMIT_FLAG ROW_CURSOR_PRIVATE(Int.signed_range _)tensor_word_outer_next_prefix BODY
    (Z.to_nat root_count)0 initialized)as [after [RUN [KEEP [RESULT CHECKED]]]].
  - rewrite Z2Nat.id by exact NONNEG; lia.
  - lia.
  - change(-2147483648<=0<=2147483647); lia.
  - exact PREFIX.
  - exact CURSOR.
  - exact LIMIT.
  - exact FLAG.
  - eapply temp_agree_trans; eassumption.
  - exists after; split.
    + unfold tensor_word_outer_code,tensor_word_outer_statement,tensor_word_outer_scan_code.
      eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=cached)(m1:=entry_memory entry).
      * constructor; constructor; rewrite FRAME by(apply STABLE_LIVE; exact ROOT_STABLE).
        destruct CACHE as [word VALUE]; unfold temp_word; rewrite VALUE; reflexivity.
      * eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=flagged)(m1:=entry_memory entry); [constructor; constructor|].
        eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=initialized)(m1:=entry_memory entry); [constructor; constructor|exact RUN].
    + split; [eapply temp_agree_trans; eassumption|split; [exact RESULT|]].
      intros ACCEPT i ACTIVE; destruct(CHECKED ACCEPT i ACTIVE)as [INV CHECK].
      split; [exact INV|split; [exact CHECK|exact(proj2(tensor_word_outer_row_accepted ACTIVE INV CHECK))]].
Qed.

Theorem tensor_word_outer_acceptance_preserves_all :
  tensor_word_outer_prefix 0 -> tensor_word_outer_result=true -> forall i j temps memory exit final,
    0<=i<root_count -> 0<=j<child_count ->
    temps!row=Some(Vint(Int.repr i)) -> temps!column=Some(Vint(Int.repr j)) ->
    temp_agree stable(entry_temps entry)temps -> header_observations_match snapshots memory ->
    exec_stmt fe(entry_ge entry)(entry_env entry)temps memory source E0 exit final Out_normal ->
    header_observations_match snapshots final.
Proof.
  intros PREFIX ACCEPT i j temps memory exit final ROWS COLUMNS ROW COLUMN FRAME OBSERVED SOURCE.
  destruct(@tensor_word_outer_scan_execution(entry_temps entry)PREFIX(temp_agree_refl _ _))
    as [after [RUN [KEEP [FLAG SOUND]]]].
  destruct(SOUND ACCEPT i ROWS)as [INV [CHECK PRESERVE]]; eapply PRESERVE; eassumption.
Qed.

Theorem tensor_word_outer_cached_source after final :
  tensor_word_outer_prefix 0 -> tensor_word_outer_result=true -> (entry_temps entry)!row=Some(Vint Int.zero) ->
  exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
    (nested_expression_source row root_bound column child_bound source)E0 after final Out_normal ->
  exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
    (nested_cached_source row root_cache column child_cache source)E0 after final Out_normal /\
  header_observations_match snapshots final.
Proof.
  intros PREFIX ACCEPT ROW SOURCE; pose proof PREFIX as [READY [ROOT_DOMAIN [ROOT_RANGE [INITIAL REST]]]].
  assert(ROOT_WORD:(entry_temps entry)!root_cache=Some(Vint(temp_word root_cache(entry_temps entry)))).
  { destruct ROOT_DOMAIN as [word VALUE]; unfold temp_word; rewrite VALUE; reflexivity. }
  destruct(Z.eq_dec root_count 0)as [EMPTY|ACTIVE].
  - assert(ZERO:temp_word root_cache(entry_temps entry)=Int.zero).
    { rewrite <-(Int.repr_signed(temp_word root_cache(entry_temps entry))); fold root_count; rewrite EMPTY; reflexivity. }
    assert(HEADER:eval_expr(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)root_bound(Vint Int.zero)).
    { rewrite <-ZERO; eapply ROOT_HEADER with(i:=0); [exact READY|lia|exact ROW|apply temp_agree_refl|exact INITIAL]. }
    destruct(@expression_zero_cached_transport fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
      row root_cache root_bound(nested_expression_body column child_bound source)(nested_cached_body column child_cache source)
      after final ROOT_TYPE(@nested_expression_body_quiet column child_bound source eq_refl)ROW
      ltac:(rewrite <-ZERO; exact ROOT_WORD)HEADER SOURCE)as [CACHED [TEMPS MEMORY]].
    split; [exact CACHED|rewrite MEMORY; exact INITIAL].
  - assert(ROOT_ACTIVE:0<root_count)by lia.
    assert(CHILD_WORD:(entry_temps entry)!child_cache=Some(Vint(temp_word child_cache(entry_temps entry)))).
    { destruct(CHILD_DOMAIN ROOT_ACTIVE)as [word VALUE]; unfold temp_word; rewrite VALUE; reflexivity. }
    eapply nested_expression_initial_cached with(stable:=stable)(written:=[iterator])
      (upper:=temp_word root_cache(entry_temps entry))(child_upper:=temp_word child_cache(entry_temps entry)).
    + exact ROOT_TYPE.
    + exact CHILD_TYPE.
    + exact ROOT_WORD.
    + exact CHILD_WORD.
    + exact ROOT_STABLE.
    + exact CHILD_STABLE.
    + exact ROW_PRIVATE.
    + exact COLUMN_PRIVATE.
    + exact ROW_COLUMN.
    + reflexivity.
    + reflexivity.
    + apply tensor_word_column_source_writes.
    + cbn; intuition congruence.
    + cbn; intuition congruence.
    + intros id MEMBER; cbn; intros [SAME|[]]; subst id; contradiction.
    + apply CHILD_NONNEGATIVE; exact ROOT_ACTIVE.
    + intros i current memory RANGE COUNTER FRAME OBSERVED; eapply ROOT_HEADER; eassumption.
    + exact CHILD_HEADER.
    + eapply tensor_word_outer_acceptance_preserves_all; eassumption.
    + lia.
    + exact ROW.
    + exact INITIAL.
    + exact SOURCE.
Qed.

(** The first prefix comes from the original source, not from cached-source
    completion. Capture/profile services supply the entry words and observations. *)
Theorem tensor_word_outer_initial_prefix after final :
  ready entry -> register_domain root_cache entry -> 0<=root_count ->
  (entry_temps entry)!row=Some(Vint Int.zero) -> header_observations_match snapshots(entry_memory entry) ->
  exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
    (nested_expression_source row root_bound column child_bound source)E0 after final Out_normal ->
  tensor_word_outer_prefix 0.
Proof.
  intros READY ROOT RANGE ROW INITIAL SOURCE; unfold tensor_word_outer_prefix.
  eapply expression_body_prefix_initial; eassumption.
Qed.

(** Same-entry composition retains the actual guard exit frame. A future
    model/candidate adapter must transport its cached source to that exit. *)
Theorem tensor_word_outer_original_scan current after final :
  ready entry -> register_domain root_cache entry -> 0<=root_count ->
  (entry_temps entry)!row=Some(Vint Int.zero) -> header_observations_match snapshots(entry_memory entry) ->
  exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
    (nested_expression_source row root_bound column child_bound source)E0 after final Out_normal ->
  temp_agree live(entry_temps entry)current -> exists checked,
    exec_stmt fe(entry_ge entry)(entry_env entry)current(entry_memory entry)tensor_word_outer_code
      E0 checked(entry_memory entry)Out_normal /\ temp_agree live current checked /\
    checked!flag=Some(memory_boolean_word tensor_word_outer_result) /\
    (tensor_word_outer_result=true ->
      exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
        (nested_cached_source row root_cache column child_cache source)E0 after final Out_normal /\
      header_observations_match snapshots final).
Proof.
  intros READY ROOT RANGE ROW INITIAL SOURCE FRAME.
  pose proof(tensor_word_outer_initial_prefix READY ROOT RANGE ROW INITIAL SOURCE)as PREFIX.
  destruct(tensor_word_outer_scan_execution PREFIX FRAME)as [checked [RUN [PUBLIC [FLAG SOUND]]]].
  exists checked; split; [exact RUN|split; [exact PUBLIC|split; [exact FLAG|]]].
  intro ACCEPT; eapply tensor_word_outer_cached_source; eassumption.
Qed.

(** The optimizer can protect the cached source's footprint with the same
    public frame. Complete acceptance then supplies execution at the actual
    guard exit, with the source's final memory and related public temporaries. *)
Theorem tensor_word_outer_original_scan_at_exit current after final :
  ready entry -> register_domain root_cache entry -> 0<=root_count ->
  (entry_temps entry)!row=Some(Vint Int.zero) -> header_observations_match snapshots(entry_memory entry) ->
  exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
    (nested_expression_source row root_bound column child_bound source)E0 after final Out_normal ->
  check_plan_frameable(nested_cached_source row root_cache column child_cache source)=true ->
  incl(statement_temps(nested_cached_source row root_cache column child_cache source))live ->
  temp_agree live(entry_temps entry)current -> exists checked,
    exec_stmt fe(entry_ge entry)(entry_env entry)current(entry_memory entry)tensor_word_outer_code
      E0 checked(entry_memory entry)Out_normal /\ temp_agree live current checked /\
    checked!flag=Some(memory_boolean_word tensor_word_outer_result) /\
    (tensor_word_outer_result=true -> exists exit,
      exec_stmt fe(entry_ge entry)(entry_env entry)checked(entry_memory entry)
        (nested_cached_source row root_cache column child_cache source)E0 exit final Out_normal /\
      temp_agree live after exit /\ header_observations_match snapshots final).
Proof.
  intros READY ROOT RANGE ROW INITIAL SOURCE FRAMEABLE SCOPE FRAME.
  destruct(tensor_word_outer_original_scan READY ROOT RANGE ROW INITIAL SOURCE FRAME)
    as [checked [RUN [PUBLIC [FLAG SOUND]]]].
  exists checked; split; [exact RUN|split; [exact PUBLIC|split; [exact FLAG|]]].
  intro ACCEPT; destruct(SOUND ACCEPT)as [CACHED OBSERVED].
  destruct(@structured_execution_temp_transport fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
    (nested_cached_source row root_cache column child_cache source)E0 after final Out_normal CACHED live checked
    (statement_temps(nested_cached_source row root_cache column child_cache source))
    (@check_plan_frameable_writes _ FRAMEABLE)SCOPE ltac:(eapply temp_agree_trans; eassumption))
    as [exit [MODEL EXIT]].
  exists exit; split; [exact MODEL|split; assumption].
Qed.
End OUTER.

Print Assumptions tensor_word_outer_inner_stable.
Print Assumptions tensor_word_outer_inner_cache.
Print Assumptions tensor_word_outer_child_count.
Print Assumptions tensor_word_outer_row_frame.
Print Assumptions tensor_word_outer_runtime_frame.
Print Assumptions tensor_word_outer_renamed_stable.
Print Assumptions tensor_word_outer_source_words.
Print Assumptions tensor_word_outer_row_execution.
Print Assumptions tensor_word_outer_row_checked_frame.
Print Assumptions tensor_word_outer_row_accepted.
Print Assumptions tensor_word_outer_next_prefix.
Print Assumptions tensor_word_outer_scan_execution.
Print Assumptions tensor_word_outer_acceptance_preserves_all.
Print Assumptions tensor_word_outer_cached_source.
Print Assumptions tensor_word_outer_initial_prefix.
Print Assumptions tensor_word_outer_original_scan.
Print Assumptions tensor_word_outer_original_scan_at_exit.
Print Assumptions tensor_word_outer_empty_execution.
Print Assumptions tensor_word_outer_first_refusal.
