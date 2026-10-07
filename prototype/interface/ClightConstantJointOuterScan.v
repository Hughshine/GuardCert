From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightRedundantSet
  ClightNoWrap ClightCountedLoop ClightFramedLoop ClightLoopSyntax ClightFrontendLoopProtocol
  ClightLoopExecution ClightRegionProgress CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryWindowCells GuardMemoryBooleanScan
  GuardMemoryNaryCompute GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestValuation AffineNestMathDomain
  AffineNestSourceDecode AffineNestLeafModel AffineNestLeafDecode AffineNestLoopEncoding AffineNestScanSyntax AffineNestScanModel.
From GuardInterface Require Import ClightConstantBoundModel ClightAffineJointObservation
  ClightExpressionBodyPrefix ClightShortCircuitPrefixLoop ClightObservedHeaderPrefix
  ClightNestedExpressionCapture ClightNestedExpressionPrefix ClightNestedExpressionTransport
  ClightJointInnerRowFrame ClightConstantJointInnerScan ClightEmptyExpressionTransport.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition constant_joint_outer_statement root_cache child_cache row_cursor row_limit column_cursor column_limit
  flag nest controls values observers operations :=
  Ssequence(Sset row_limit(Etempvar root_cache type_int32s))
    (Ssequence(Sset flag(Econst_int Int.one type_int32s))
      (Ssequence(Sset row_cursor(Econst_int Int.zero type_int32s))
        (short_circuit_prefix_loop row_cursor row_limit flag
          (constant_joint_inner_statement child_cache column_cursor column_limit flag nest controls values observers operations)))).

(** Numeric and static metadata are explicit inputs. Body executions, check
    availability, preservation, and prefix advancement are produced below
    from the actual source prefix; none is a semantic callback in this API. *)
Section OUTER.
Variables iterator helper row column root_cache child_cache : ident.
Variable upper : Z.
Variable body : statement.
Variable child : affine_source_nest.
Variables coordinates prefix parameters pointers : list ident.
Variable bounds : list(Z*Z).
Variables window_lower window_upper : Z.
Variable operations : list memory_nary_compute.
Variable certificate : affine_leaf_certificate(affine_nest_leaf child) bounds window_lower window_upper
  (coordinates++parameters) [] pointers operations.
Let nest:=AffineSourceAxis iterator helper(MemorySourceConstant upper) body child.
Variable code : L.stmt.
Variables stable public live leaf_written source_written : list ident.
Variable observers : list clight_word_observer.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable entry : clight_entry.
Variable ready : clight_entry -> Prop.
Variables root_bound child_bound : expr.
Variable valuation : Z -> Z -> ident -> Z.
Variables controls values : ident -> ident.
Variables row_cursor row_limit column_cursor column_limit flag : ident.
Let root_count:=Int.signed(temp_word root_cache(entry_temps entry)).
Let child_count:=Int.signed(temp_word child_cache(entry_temps entry)).
Let snapshots:=map word_observer_snapshot observers.
Let source:=constant_body_source iterator(Int.repr upper) body.
Let source_prefix index:=expression_body_prefix fe row root_cache root_bound
  (nested_expression_body column child_bound source) stable ready(fun _=>snapshots) index entry.
Let inner_entry index:=nested_expression_inner_entry row column index entry.
Let row_test index:=memory_boolean_scan_result
  (fun j=>affine_scan_result nest(valuation index j) 0
    (affine_joint_observation_result
      (window_multi_pointer_locations(entry_temps(inner_entry index)) window_lower window_upper) observers operations))
  0(Z.to_nat child_count).
Let result:=memory_boolean_scan_result row_test 0(Z.to_nat root_count).
Let inner_live:=row_cursor::row_limit::live.
Let inner_statement:=constant_joint_inner_statement child_cache column_cursor column_limit flag nest controls values observers operations.

Hypothesis COORDINATES : coordinates=prefix++affine_nest_iterators nest.
Hypothesis SHAPES : affine_nest_shapes nest.
Hypothesis FRESH : NoDup(affine_nest_controls nest).
Hypothesis DEPENDENCIES : affine_nest_bound_dependencies prefix parameters nest.
Hypothesis PROTECTED : forall identifier,In identifier((prefix++parameters)++pointers)->~In identifier(affine_nest_mutated nest).
Hypothesis LOWER : affine_lower_nest nest prefix parameters(L.Constant 0)
  (affine_checked_leaf_code coordinates parameters [] operations)=Some code.
Hypothesis DOMAIN : forall i j,0<=i<root_count -> 0<=j<child_count ->
  affine_math_domain bounds(coordinates++parameters) nest(valuation i j) 0.
Hypothesis SOURCE_WORDS : forall i j,0<=i<root_count -> 0<=j<child_count ->
  affine_word_view(prefix++parameters)(valuation i j)
    (PTree.set column(Vint(Int.repr j))(entry_temps(inner_entry i))).
Hypothesis WORD_SCOPE : incl(prefix++parameters)(column::row::stable).
Hypothesis POINTER_STABLE : incl pointers stable.
Hypothesis HELPER_MEMBER : In helper stable.
Hypothesis HELPER : (entry_temps entry)!helper=Some(Vint(Int.repr upper)).
Hypotheses (LEAF_WRITES : writes_only leaf_written body) (HELPER_PRIVATE : ~In helper leaf_written).
Hypotheses (ROOT_TYPE : typeof root_bound=type_int32s) (CHILD_TYPE : typeof child_bound=type_int32s).
Hypotheses (ROW_PRIVATE : ~In row stable) (COLUMN_PRIVATE : ~In column stable) (ROW_COLUMN : row<>column).
Hypotheses (NORMAL : normal_statement source=true) (QUIET : quiet_statement source=true).
Hypothesis SOURCE_WRITES : writes_only source_written source.
Hypotheses (ROW_UNWRITTEN : ~In row source_written) (COLUMN_UNWRITTEN : ~In column source_written).
Hypothesis STABLE_UNWRITTEN : forall identifier,In identifier stable -> ~In identifier source_written.
Hypothesis ROOT_HEADER : forall i current memory,ready entry -> 0<=i<=root_count ->
  current!row=Some(Vint(Int.repr i)) -> temp_agree stable(entry_temps entry) current ->
  header_observations_match snapshots memory ->
  eval_expr(entry_ge entry)(entry_env entry) current memory root_bound(Vint(temp_word root_cache(entry_temps entry))).
Hypothesis CHILD_HEADER : forall i j current memory,0<=i<root_count -> 0<=j<=child_count ->
  current!row=Some(Vint(Int.repr i)) -> current!column=Some(Vint(Int.repr j)) ->
  temp_agree stable(entry_temps entry) current -> header_observations_match snapshots memory ->
  eval_expr(entry_ge entry)(entry_env entry) current memory child_bound(Vint(temp_word child_cache(entry_temps entry))).
Hypothesis CHILD_DOMAIN : 0<root_count -> register_domain child_cache entry.
Hypothesis CHILD_NONNEGATIVE : 0<root_count -> 0<=child_count.
Hypothesis POINTER_PUBLIC : incl pointers public.
Hypothesis OBSERVERS : forall observer,0<root_count -> In observer observers ->
  word_observer_receipt(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry) observer.
Hypothesis OBSERVER_SCOPE : forall observer,In observer observers -> expression_scope public(word_observer_address observer).
Hypotheses (PUBLIC_STABLE : incl public stable) (STABLE_LIVE : incl stable live).
Hypotheses (ROOT_CACHE_PUBLIC : In root_cache public) (CHILD_CACHE_PUBLIC : In child_cache public).
Hypothesis UNIQUE : NoDup(map controls(affine_nest_controls nest)).
Hypothesis ITERATOR_VALUES : forall identifier,In identifier(affine_nest_iterators nest)->values identifier=controls identifier.
Hypothesis CONTROL_PRIVATE : forall identifier,In identifier(affine_nest_controls nest)->
  ~In(controls identifier)(column_cursor::column_limit::inner_live) /\ controls identifier<>flag.
Hypotheses (ROW_CURSOR_PRIVATE : ~In row_cursor live) (ROW_LIMIT_PRIVATE : ~In row_limit live).
Hypotheses (COLUMN_CURSOR_PRIVATE : ~In column_cursor inner_live) (COLUMN_LIMIT_PRIVATE : ~In column_limit inner_live)
  (FLAG_PRIVATE : ~In flag inner_live).
Hypotheses (ROW_CURSOR_LIMIT : row_cursor<>row_limit) (ROW_CURSOR_FLAG : row_cursor<>flag) (ROW_LIMIT_FLAG : row_limit<>flag).
Hypotheses (COLUMN_CURSOR_LIMIT : column_cursor<>column_limit) (COLUMN_CURSOR_FLAG : column_cursor<>flag)
  (COLUMN_LIMIT_FLAG : column_limit<>flag).
Hypothesis FLAG_WORD : ~In flag(map values(coordinates++parameters)).
Hypotheses (ROW_VALUE : values row=row_cursor) (COLUMN_VALUE : values column=column_cursor).
Hypothesis INDEX_VALUE : forall i j,0<=i<root_count -> 0<=j<child_count -> valuation i j column=j.
Hypothesis OTHER_VALUE : forall i j identifier,0<=i<root_count -> 0<=j<child_count ->
  In identifier(prefix++parameters) -> identifier<>column -> valuation i j identifier=valuation i 0 identifier.
Hypothesis STABLE_VALUE : forall identifier,In identifier(prefix++parameters) -> identifier<>column -> identifier<>row ->
  values identifier=identifier.

Lemma constant_outer_inner_cache index :
  (entry_temps(inner_entry index))!child_cache=(entry_temps entry)!child_cache.
Proof.
  apply joint_inner_cache_frame with(stable:=stable); try assumption.
  apply PUBLIC_STABLE; exact CHILD_CACHE_PUBLIC.
Qed.

Lemma constant_outer_inner_stable index : temp_agree stable(entry_temps entry)(entry_temps(inner_entry index)).
Proof.
  intros identifier MEMBER; unfold inner_entry,nested_expression_inner_entry; cbn [entry_temps].
  rewrite !PTree.gso by(intro SAME; subst identifier; contradiction); reflexivity.
Qed.

Lemma constant_outer_row_words index current :
  0<=index<root_count -> current!row_cursor=Some(Vint(Int.repr index)) ->
  temp_agree live(entry_temps entry) current -> forall j,0<=j<child_count ->
  forall identifier,In identifier(prefix++parameters) -> identifier<>column ->
  current!(values identifier)=Some(Vint(Int.repr(valuation index 0 identifier))).
Proof.
  intros RANGE ROW FRAME j ACTIVE identifier MEMBER OTHER.
  pose proof(@SOURCE_WORDS index 0 RANGE ltac:(lia) identifier MEMBER) as WORD.
  rewrite PTree.gso in WORD by exact OTHER.
  unfold inner_entry,nested_expression_inner_entry in WORD; cbn [entry_temps] in WORD.
  rewrite PTree.gso in WORD by exact OTHER.
  destruct(Pos.eq_dec identifier row) as [->|NOT_ROW].
  - rewrite PTree.gss in WORD; rewrite ROW_VALUE,ROW; exact WORD.
  - rewrite PTree.gso in WORD by exact NOT_ROW.
    rewrite STABLE_VALUE by assumption; rewrite FRAME; [exact WORD|].
    apply STABLE_LIVE; destruct(WORD_SCOPE identifier MEMBER) as [SAME|[SAME|STABLE]]; congruence || exact STABLE.
Qed.

(** Opening a row uses an original source witness. The inner implementation
    itself discharges all BODY and PRESERVE obligations for that row. *)
Theorem constant_outer_row_execution index current :
  0<=index<root_count -> source_prefix index ->
  current!row_cursor=Some(Vint(Int.repr index)) -> current!flag=Some(memory_boolean_word true) ->
  temp_agree live(entry_temps entry) current -> exists after,
    exec_stmt fe(entry_ge entry)(entry_env entry) current(entry_memory entry) inner_statement E0 after(entry_memory entry) Out_normal /\
    temp_agree inner_live current after /\ after!flag=Some(memory_boolean_word(row_test index)) /\
    (row_test index=true ->
      (forall j temps memory exit final,0<=j<child_count ->
        temps!row=Some(Vint(Int.repr index)) -> temps!column=Some(Vint(Int.repr j)) ->
        temp_agree stable(entry_temps entry) temps -> header_observations_match snapshots memory ->
        exec_stmt fe(entry_ge entry)(entry_env entry) temps memory source E0 exit final Out_normal ->
        header_observations_match snapshots final) /\ source_prefix(index+1)).
Proof.
  intros RANGE PREFIX ROW FLAG FRAME.
  assert (COUNT : Int.signed(temp_word child_cache(entry_temps(inner_entry index)))=child_count).
  { unfold temp_word; rewrite constant_outer_inner_cache; reflexivity. }
  assert (CURRENT_PUBLIC : temp_agree public(entry_temps(inner_entry index)) current).
  { intros identifier MEMBER; rewrite FRAME by(apply STABLE_LIVE; apply PUBLIC_STABLE; exact MEMBER).
    symmetry; apply constant_outer_inner_stable; apply PUBLIC_STABLE; exact MEMBER. }
  unfold row_test.
  replace (Z.to_nat child_count) with
    (Z.to_nat(Int.signed(temp_word child_cache(entry_temps(inner_entry index))))) by(rewrite COUNT; reflexivity).
  eapply constant_joint_current_row_execution with(certificate:=certificate)(code:=code)
    (iterator:=iterator)(helper:=helper)(column:=column)(cache:=child_cache)(upper:=upper)(body:=body)(bound:=child_bound)
    (stable:=row::stable)(public:=public)(live:=inner_live)(leaf_written:=leaf_written)(source_written:=source_written)
    (observers:=observers)(entry:=inner_entry index)(base:=current)(ready:=fun _=>True)
    (valuation:=valuation index)(controls:=controls)(values:=values)(cursor:=column_cursor)(limit:=column_limit)
    (origin:=entry)(row:=row)(root_cache:=root_cache)(root_bound:=root_bound)(outer_stable:=stable)(outer_ready:=ready)
    (index:=index)(checked:=current)(fe:=fe).
  - exact COORDINATES.
  - exact SHAPES.
  - exact FRESH.
  - exact DEPENDENCIES.
  - exact PROTECTED.
  - exact LOWER.
  - intros j ACTIVE; apply DOMAIN; [exact RANGE|rewrite <-COUNT; exact ACTIVE].
  - intros j ACTIVE; apply SOURCE_WORDS; [exact RANGE|rewrite <-COUNT; exact ACTIVE].
  - exact WORD_SCOPE.
  - intros identifier MEMBER; right; apply POINTER_STABLE; exact MEMBER.
  - right; exact HELPER_MEMBER.
  - rewrite constant_outer_inner_stable by exact HELPER_MEMBER; exact HELPER.
  - exact LEAF_WRITES.
  - exact HELPER_PRIVATE.
  - exact CHILD_TYPE.
  - cbn; tauto.
  - exact NORMAL.
  - exact QUIET.
  - exact SOURCE_WRITES.
  - exact COLUMN_UNWRITTEN.
  - intros identifier [SAME|MEMBER]; [subst identifier; exact ROW_UNWRITTEN|apply STABLE_UNWRITTEN; exact MEMBER].
  - intros j temps memory _ ACTIVE COLUMN INNER OBSERVED.
    cbn [inner_entry nested_expression_inner_entry entry_ge entry_env].
    unfold temp_word; rewrite constant_outer_inner_cache; fold(temp_word child_cache(entry_temps entry)).
    eapply CHILD_HEADER; [exact RANGE|rewrite <-COUNT; exact ACTIVE| |exact COLUMN| |exact OBSERVED].
    + rewrite INNER by(left; reflexivity).
      unfold inner_entry,nested_expression_inner_entry; cbn [entry_temps]; rewrite PTree.gso by exact ROW_COLUMN; apply PTree.gss.
    + intros identifier MEMBER; rewrite INNER by(right; exact MEMBER).
      apply constant_outer_inner_stable; exact MEMBER.
  - exact POINTER_PUBLIC.
  - intros observer MEMBER; cbn [inner_entry nested_expression_inner_entry entry_ge entry_env entry_memory].
    eapply word_observer_receipt_frame with(live:=public)(temps:=entry_temps entry).
    + apply OBSERVERS; [lia|exact MEMBER].
    + apply OBSERVER_SCOPE; exact MEMBER.
    + intros identifier PUBLIC; apply constant_outer_inner_stable; apply PUBLIC_STABLE; exact PUBLIC.
  - exact OBSERVER_SCOPE.
  - intros identifier MEMBER; right; right; apply STABLE_LIVE; apply PUBLIC_STABLE; exact MEMBER.
  - exact CURRENT_PUBLIC.
  - exact CHILD_CACHE_PUBLIC.
  - exact UNIQUE.
  - exact ITERATOR_VALUES.
  - exact CONTROL_PRIVATE.
  - exact COLUMN_CURSOR_PRIVATE.
  - exact COLUMN_LIMIT_PRIVATE.
  - exact FLAG_PRIVATE.
  - exact COLUMN_CURSOR_LIMIT.
  - exact COLUMN_CURSOR_FLAG.
  - exact COLUMN_LIMIT_FLAG.
  - exact FLAG_WORD.
  - exact COLUMN_VALUE.
  - intros j ACTIVE; apply INDEX_VALUE; [exact RANGE|rewrite <-COUNT; exact ACTIVE].
  - intros j identifier ACTIVE MEMBER OTHER; apply OTHER_VALUE; [exact RANGE|rewrite <-COUNT; exact ACTIVE|exact MEMBER|exact OTHER].
  - intros identifier MEMBER OTHER.
    destruct(Pos.eq_dec identifier row) as [->|NOT_ROW].
    + rewrite ROW_VALUE; left; reflexivity.
    + rewrite STABLE_VALUE by assumption; right; right; apply STABLE_LIVE.
      destruct(WORD_SCOPE identifier MEMBER) as [SAME|[SAME|STABLE]]; congruence || exact STABLE.
  - intros j ACTIVE; eapply constant_outer_row_words with(j:=j); [exact RANGE|exact ROW|exact FRAME|rewrite <-COUNT; exact ACTIVE].
  - reflexivity.
  - reflexivity.
  - exact ROW_PRIVATE.
  - exact COLUMN_PRIVATE.
  - exact ROW_COLUMN.
  - apply PUBLIC_STABLE; exact CHILD_CACHE_PUBLIC.
  - exact ROOT_TYPE.
  - apply CHILD_DOMAIN; lia.
  - rewrite COUNT; apply CHILD_NONNEGATIVE; lia.
  - exact I.
  - exact ROOT_HEADER.
  - exact PREFIX.
  - exact(proj2 RANGE).
  - exact FLAG.
  - apply temp_agree_refl.
Qed.

Let row_checked index:=PTree.set flag(memory_boolean_word true)
  (PTree.set row_cursor(Vint(Int.repr index))(entry_temps entry)).

Lemma constant_outer_row_checked_frame index : temp_agree live(entry_temps entry)(row_checked index).
Proof.
  unfold row_checked; eapply temp_agree_trans;
    [apply temp_agree_set; exact ROW_CURSOR_PRIVATE|apply temp_agree_set].
  intro MEMBER; apply FLAG_PRIVATE; right; right; exact MEMBER.
Qed.

(** Use the concrete row producer at an admissible private state. This is
    proof-only instantiation, not source execution by the runtime guard. *)
Lemma constant_outer_row_accepted index :
  0<=index<root_count -> source_prefix index -> row_test index=true ->
  source_prefix(index+1) /\
  (forall j temps memory exit final,0<=j<child_count ->
    temps!row=Some(Vint(Int.repr index)) -> temps!column=Some(Vint(Int.repr j)) ->
    temp_agree stable(entry_temps entry) temps -> header_observations_match snapshots memory ->
    exec_stmt fe(entry_ge entry)(entry_env entry) temps memory source E0 exit final Out_normal ->
    header_observations_match snapshots final).
Proof.
  intros RANGE PREFIX ACCEPT.
  destruct(@constant_outer_row_execution index(row_checked index) RANGE PREFIX
    ltac:(unfold row_checked; rewrite PTree.gso by congruence; apply PTree.gss)
    ltac:(unfold row_checked; apply PTree.gss)(constant_outer_row_checked_frame index))
    as [after [RUN [KEEP [FLAG SOUND]]]].
  destruct(SOUND ACCEPT) as [PRESERVE NEXT]; split; assumption.
Qed.

Lemma constant_outer_next_prefix index :
  0<=index<root_count -> source_prefix index -> row_test index=true -> source_prefix(index+1).
Proof.
  intros RANGE PREFIX ACCEPT; exact(proj1(constant_outer_row_accepted RANGE PREFIX ACCEPT)).
Qed.

Theorem constant_joint_outer_scan_execution checked :
  source_prefix 0 -> temp_agree live(entry_temps entry) checked -> exists after,
    exec_stmt fe(entry_ge entry)(entry_env entry) checked(entry_memory entry)
      (constant_joint_outer_statement root_cache child_cache row_cursor row_limit column_cursor column_limit
        flag nest controls values observers operations) E0 after(entry_memory entry) Out_normal /\
    temp_agree live checked after /\ after!flag=Some(memory_boolean_word result) /\
    (result=true -> forall i,0<=i<root_count -> source_prefix i /\ row_test i=true /\
      (forall j temps memory exit final,0<=j<child_count ->
        temps!row=Some(Vint(Int.repr i)) -> temps!column=Some(Vint(Int.repr j)) ->
        temp_agree stable(entry_temps entry) temps -> header_observations_match snapshots memory ->
        exec_stmt fe(entry_ge entry)(entry_env entry) temps memory source E0 exit final Out_normal ->
        header_observations_match snapshots final)).
Proof.
  intros PREFIX FRAME.
  pose proof PREFIX as [READY [CACHE [RANGE REST]]].
  assert (NONNEGATIVE : 0<=root_count) by lia.
  assert (UPPER_RANGE : signed_range root_count) by apply Int.signed_range.
  assert (FLAG_LIVE_PRIVATE : ~In flag live).
  { intro MEMBER; apply FLAG_PRIVATE; right; right; exact MEMBER. }
  set(cached:=PTree.set row_limit(Vint(temp_word root_cache(entry_temps entry))) checked).
  set(flagged:=PTree.set flag(memory_boolean_word true) cached).
  set(initialized:=PTree.set row_cursor(Vint Int.zero) flagged).
  assert (INIT_FRAME : temp_agree live checked initialized).
  { eapply temp_agree_trans with(le1:=cached); [apply temp_agree_set; exact ROW_LIMIT_PRIVATE|].
    eapply temp_agree_trans with(le1:=flagged); apply temp_agree_set; assumption. }
  assert (INIT_CURSOR : initialized!row_cursor=Some(Vint(Int.repr 0))) by(unfold initialized; apply PTree.gss).
  assert (INIT_BOUND : initialized!row_limit=Some(Vint(Int.repr root_count))).
  { unfold initialized,flagged,cached; rewrite !PTree.gso by congruence; rewrite PTree.gss.
    unfold root_count; rewrite Int.repr_signed; reflexivity. }
  assert (INIT_FLAG : initialized!flag=Some(memory_boolean_word true)).
  { unfold initialized,flagged; rewrite PTree.gso by congruence; apply PTree.gss. }
  assert (BODY : forall index current,signed_range index -> 0<=index<root_count -> source_prefix index ->
    current!row_cursor=Some(Vint(Int.repr index)) -> current!row_limit=Some(Vint(Int.repr root_count)) ->
    current!flag=Some(memory_boolean_word true) -> temp_agree live(entry_temps entry) current -> exists after,
      exec_stmt fe(entry_ge entry)(entry_env entry) current(entry_memory entry) inner_statement E0 after(entry_memory entry) Out_normal /\
      temp_agree(row_cursor::row_limit::live) current after /\ after!flag=Some(memory_boolean_word(row_test index))).
  { intros index current INDEX ACTIVE INV CURSOR LIMIT FLAG CURRENT.
    destruct(constant_outer_row_execution ACTIVE INV CURSOR FLAG CURRENT) as [after [RUN [KEEP [RESULT SOUND]]]].
    exists after; repeat split; assumption. }
  destruct(@short_circuit_prefix_loop_execution fe(entry_ge entry)(entry_env entry)(entry_memory entry)
    row_cursor row_limit flag inner_statement live(entry_temps entry) 0 root_count source_prefix row_test
    ROW_CURSOR_LIMIT ROW_CURSOR_FLAG ROW_LIMIT_FLAG ROW_CURSOR_PRIVATE UPPER_RANGE constant_outer_next_prefix BODY
    (Z.to_nat root_count) 0 initialized) as [after [RUN [KEEP [RESULT ACCEPTED]]]].
  - rewrite Z2Nat.id by exact NONNEGATIVE; lia.
  - lia.
  - unfold signed_range; change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia.
  - exact PREFIX.
  - exact INIT_CURSOR.
  - exact INIT_BOUND.
  - exact INIT_FLAG.
  - eapply temp_agree_trans; eassumption.
  - exists after; split.
    + unfold constant_joint_outer_statement.
      eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=cached)(m1:=entry_memory entry).
      * constructor; constructor.
        rewrite FRAME by(apply STABLE_LIVE; apply PUBLIC_STABLE; exact ROOT_CACHE_PUBLIC).
        destruct CACHE as [word WORD]; unfold temp_word; rewrite WORD; reflexivity.
      * eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=flagged)(m1:=entry_memory entry); [constructor; constructor|].
        eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=initialized)(m1:=entry_memory entry); [constructor; constructor|exact RUN].
    + split; [eapply temp_agree_trans; eassumption|split; [exact RESULT|]].
      intros ACCEPT index ACTIVE; destruct(ACCEPTED ACCEPT index ACTIVE) as [INV CHECK].
      split; [exact INV|split; [exact CHECK|]].
      exact(proj2(constant_outer_row_accepted ACTIVE INV CHECK)).
Qed.

Theorem constant_joint_outer_acceptance_preserves_all :
  source_prefix 0 -> result=true -> forall i j temps memory exit final,
    0<=i<root_count -> 0<=j<child_count ->
    temps!row=Some(Vint(Int.repr i)) -> temps!column=Some(Vint(Int.repr j)) ->
    temp_agree stable(entry_temps entry) temps -> header_observations_match snapshots memory ->
    exec_stmt fe(entry_ge entry)(entry_env entry) temps memory source E0 exit final Out_normal ->
    header_observations_match snapshots final.
Proof.
  intros PREFIX ACCEPT i j temps memory exit final ROWS COLUMNS ROW COLUMN CURRENT OBSERVED SOURCE.
  destruct(@constant_joint_outer_scan_execution(entry_temps entry) PREFIX(temp_agree_refl _ _))
    as [after [RUN [KEEP [FLAG SOUND]]]].
  destruct(SOUND ACCEPT i ROWS) as [INV [CHECK PRESERVE]]; eapply PRESERVE; eassumption.
Qed.

(** Refusal in the first checked row stops the enclosing loop before its
    increment. No permission or execution witness for the next row is used. *)
Theorem constant_joint_outer_first_row_refusal current :
  source_prefix 0 -> 0<root_count -> row_test 0=false ->
  current!row_cursor=Some(Vint Int.zero) -> current!row_limit=Some(Vint(Int.repr root_count)) ->
  current!flag=Some(memory_boolean_word true) -> temp_agree live(entry_temps entry) current -> exists after,
    exec_stmt fe(entry_ge entry)(entry_env entry) current(entry_memory entry)
      (short_circuit_prefix_loop row_cursor row_limit flag inner_statement) E0 after(entry_memory entry) Out_normal /\
    temp_agree live current after /\ after!row_cursor=Some(Vint Int.zero) /\ after!flag=Some(memory_boolean_word false).
Proof.
  intros PREFIX ACTIVE REFUSE ROW LIMIT FLAG FRAME.
  destruct(@constant_outer_row_execution 0 current ltac:(lia) PREFIX ROW FLAG FRAME) as [after [RUN [KEEP [RESULT SOUND]]]].
  rewrite REFUSE in RESULT; exists after; split.
  - unfold short_circuit_prefix_loop,counted_loop.
    destruct(@counter_condition_at(entry_ge entry)(entry_env entry) current(entry_memory entry)
      row_cursor row_limit 0 root_count ROW_CURSOR_LIMIT ROW LIMIT
      ltac:(unfold signed_range; change(-2147483648<=0<=2147483647); lia)
      (Int.signed_range(temp_word root_cache(entry_temps entry)))) as [value [EVAL BOOL]].
    assert (LT : (0<?root_count)=true) by(apply Z.ltb_lt; exact ACTIVE); rewrite LT in BOOL.
    eapply exec_Sloop_stop1 with(out':=Out_break); [|constructor].
    eapply exec_Sifthenelse; [exact EVAL|exact BOOL|].
    eapply short_circuit_point_execution with(answer:=false); eassumption.
  - split.
    + eapply temp_agree_weaken; [|exact KEEP]; intros identifier MEMBER; right; right; exact MEMBER.
    + split; [rewrite KEEP by(left; reflexivity); exact ROW|exact RESULT].
Qed.

(** Full cached-source execution is a result of acceptance, not an input
    used to license checking. The zero-root case does not read the child. *)
Theorem constant_joint_outer_cached_source after final :
  source_prefix 0 -> result=true -> (entry_temps entry)!row=Some(Vint Int.zero) ->
  exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
    (nested_expression_source row root_bound column child_bound source) E0 after final Out_normal ->
  exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
    (nested_cached_source row root_cache column child_cache source) E0 after final Out_normal /\
  header_observations_match snapshots final.
Proof.
  intros PREFIX ACCEPT ROW SOURCE.
  pose proof PREFIX as [READY [ROOT_DOMAIN [ROOT_RANGE [INITIAL REST]]]].
  assert (ROOT_WORD : (entry_temps entry)!root_cache=Some(Vint(temp_word root_cache(entry_temps entry)))).
  { destruct ROOT_DOMAIN as [word WORD]; unfold temp_word; rewrite WORD; reflexivity. }
  destruct(Z.eq_dec root_count 0) as [EMPTY|ACTIVE].
  - assert (ZERO : temp_word root_cache(entry_temps entry)=Int.zero).
    { rewrite <-(Int.repr_signed(temp_word root_cache(entry_temps entry))); fold root_count; rewrite EMPTY; reflexivity. }
    assert (HEADER : eval_expr(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry) root_bound(Vint Int.zero)).
    { rewrite <-ZERO; eapply ROOT_HEADER with(i:=0); [exact READY|lia|exact ROW|apply temp_agree_refl|exact INITIAL]. }
    destruct(@expression_zero_cached_transport fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
      row root_cache root_bound(nested_expression_body column child_bound source)
      (nested_cached_body column child_cache source) after final ROOT_TYPE
      (@nested_expression_body_quiet column child_bound source QUIET) ROW
      ltac:(rewrite <-ZERO; exact ROOT_WORD) HEADER SOURCE) as [CACHED [TEMPS MEMORY]].
    split.
    + exact CACHED.
    + rewrite MEMORY; exact INITIAL.
  - assert (ROOT_ACTIVE : 0<root_count) by lia.
    assert (CHILD_WORD : (entry_temps entry)!child_cache=Some(Vint(temp_word child_cache(entry_temps entry)))).
    { destruct(CHILD_DOMAIN ROOT_ACTIVE) as [word WORD]; unfold temp_word; rewrite WORD; reflexivity. }
    eapply nested_expression_initial_cached with(stable:=stable)(written:=source_written)
      (upper:=temp_word root_cache(entry_temps entry))(child_upper:=temp_word child_cache(entry_temps entry)).
    + exact ROOT_TYPE.
    + exact CHILD_TYPE.
    + exact ROOT_WORD.
    + exact CHILD_WORD.
    + apply PUBLIC_STABLE; exact ROOT_CACHE_PUBLIC.
    + apply PUBLIC_STABLE; exact CHILD_CACHE_PUBLIC.
    + exact ROW_PRIVATE.
    + exact COLUMN_PRIVATE.
    + exact ROW_COLUMN.
    + exact NORMAL.
    + exact QUIET.
    + exact SOURCE_WRITES.
    + exact ROW_UNWRITTEN.
    + exact COLUMN_UNWRITTEN.
    + exact STABLE_UNWRITTEN.
    + apply CHILD_NONNEGATIVE; exact ROOT_ACTIVE.
    + intros i current memory RANGE CURRENT FRAME OBSERVED; eapply ROOT_HEADER; eassumption.
    + exact CHILD_HEADER.
    + eapply constant_joint_outer_acceptance_preserves_all; eassumption.
    + lia.
    + exact ROW.
    + exact INITIAL.
    + exact SOURCE.
Qed.
End OUTER.

(** This actual empty guard path has no source prefix, child/header receipt,
    math-domain, parameter-word, or output-pointer premise. *)
Theorem constant_joint_outer_empty_execution fe ge locals memory root_cache child_cache row_cursor row_limit column_cursor column_limit
  flag nest controls values observers operations checked live :
  row_cursor<>row_limit -> row_cursor<>flag -> row_limit<>flag ->
  ~In row_cursor live -> ~In row_limit live -> ~In flag live -> checked!root_cache=Some(Vint Int.zero) ->
  let initialized:=PTree.set row_cursor(Vint Int.zero)
    (PTree.set flag(memory_boolean_word true)(PTree.set row_limit(Vint Int.zero) checked)) in
  exec_stmt fe ge locals checked memory
    (constant_joint_outer_statement root_cache child_cache row_cursor row_limit column_cursor column_limit
      flag nest controls values observers operations) E0 initialized memory Out_normal /\
  temp_agree live checked initialized /\ initialized!row_cursor=Some(Vint Int.zero) /\
  initialized!flag=Some(memory_boolean_word true).
Proof.
  intros DISTINCT CURSOR_FLAG LIMIT_FLAG CURSOR_PRIVATE LIMIT_PRIVATE FLAG_PRIVATE ROOT; cbn zeta.
  set(cached:=PTree.set row_limit(Vint Int.zero) checked).
  set(flagged:=PTree.set flag(memory_boolean_word true) cached).
  set(initialized:=PTree.set row_cursor(Vint Int.zero) flagged).
  assert (CURSOR : initialized!row_cursor=Some(Vint(Int.repr 0))) by(unfold initialized; apply PTree.gss).
  assert (LIMIT : initialized!row_limit=Some(Vint(Int.repr 0))).
  { unfold initialized,flagged,cached; rewrite !PTree.gso by congruence; apply PTree.gss. }
  assert (LOOP : exec_stmt fe ge locals initialized memory
    (short_circuit_prefix_loop row_cursor row_limit flag
      (constant_joint_inner_statement child_cache column_cursor column_limit flag nest controls values observers operations))
    E0 initialized memory Out_normal).
  { unfold short_circuit_prefix_loop,counted_loop.
    destruct(@counter_condition_at ge locals initialized memory row_cursor row_limit 0 0 DISTINCT CURSOR LIMIT
      ltac:(unfold signed_range; change(-2147483648<=0<=2147483647); lia)
      ltac:(unfold signed_range; change(-2147483648<=0<=2147483647); lia)) as [value [EVAL BOOL]].
    rewrite Z.ltb_irrefl in BOOL.
    eapply exec_Sloop_stop1 with(out':=Out_break); [|constructor].
    eapply exec_Sifthenelse; [exact EVAL|exact BOOL|constructor]. }
  split.
  - unfold constant_joint_outer_statement.
    eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=cached)(m1:=memory); [constructor; constructor; exact ROOT|].
    eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=flagged)(m1:=memory); [constructor; constructor|].
    eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=initialized)(m1:=memory); [constructor; constructor|exact LOOP].
  - split.
    + eapply temp_agree_trans with(le1:=cached); [apply temp_agree_set; exact LIMIT_PRIVATE|].
      eapply temp_agree_trans with(le1:=flagged); apply temp_agree_set; assumption.
    + split; [exact CURSOR|unfold initialized,flagged; rewrite PTree.gso by congruence; apply PTree.gss].
Qed.

Print Assumptions constant_outer_inner_cache.
Print Assumptions constant_outer_inner_stable.
Print Assumptions constant_outer_row_words.
Print Assumptions constant_outer_row_execution.
Print Assumptions constant_outer_row_checked_frame.
Print Assumptions constant_outer_row_accepted.
Print Assumptions constant_outer_next_prefix.
Print Assumptions constant_joint_outer_scan_execution.
Print Assumptions constant_joint_outer_acceptance_preserves_all.
Print Assumptions constant_joint_outer_first_row_refusal.
Print Assumptions constant_joint_outer_cached_source.
Print Assumptions constant_joint_outer_empty_execution.
