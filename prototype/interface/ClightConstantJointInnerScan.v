From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightRedundantSet ClightNoWrap ClightCountedLoop ClightFramedLoop ClightLoopSyntax
  ClightRegionProgress CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryWindowCells GuardMemoryBooleanScan
  GuardMemoryNaryCompute GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestValuation AffineNestMathDomain
  AffineNestSourceDecode AffineNestLeafModel AffineNestLeafDecode AffineNestLoopEncoding AffineNestScanSyntax AffineNestScanModel.
From GuardInterface Require Import ClightConstantBoundModel ClightConstantBodyJointScan ClightAffineJointObservation
  ClightExpressionBodyPrefix ClightExpressionPrefixAt ClightShortCircuitPrefixLoop ClightObservedHeaderPrefix
  ClightStructuredStorePermissions ClightNestedExpressionCapture ClightNestedExpressionPrefix ClightJointInnerRowFrame.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition constant_joint_inner_body nest controls values flag observers operations :=
  affine_scan_statement nest controls values(Econst_int Int.zero type_int32s)
    (affine_joint_observation_leaf observers operations values flag).
Definition constant_joint_inner_statement cache cursor limit flag nest controls values observers operations :=
  Ssequence(Sset limit(Etempvar cache type_int32s))
    (Ssequence(Sset cursor(Econst_int Int.zero type_int32s))
      (short_circuit_prefix_loop cursor limit flag
        (constant_joint_inner_body nest controls values flag observers operations))).

(** The source prefix has its own reached temps/memory. Guard cursors and the
    public guard anchor are separate: an enclosing private row cursor must not
    require changing the source's public row temp to scan a later row. *)
Section INNER.
Variables iterator helper column cache : ident.
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
Variables observers : list clight_word_observer.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable entry : clight_entry.
Variable base : temp_env.
Variable ready : clight_entry -> Prop.
Variable bound : expr.
Variable valuation : Z -> ident -> Z.
Variables controls values : ident -> ident.
Variables cursor limit flag : ident.
Let count:=Int.signed(temp_word cache(entry_temps entry)).
Let snapshots:=map word_observer_snapshot observers.
Let source:=constant_body_source iterator(Int.repr upper) body.
Let source_prefix index:=expression_body_prefix fe column cache bound source stable ready(fun _=>snapshots) index entry.
Let locations:=window_multi_pointer_locations(entry_temps entry) window_lower window_upper.
Let test index:=affine_scan_result nest(valuation index) 0(affine_joint_observation_result locations observers operations).

Hypothesis COORDINATES : coordinates=prefix++affine_nest_iterators nest.
Hypothesis SHAPES : affine_nest_shapes nest.
Hypothesis FRESH : NoDup(affine_nest_controls nest).
Hypothesis DEPENDENCIES : affine_nest_bound_dependencies prefix parameters nest.
Hypothesis PROTECTED : forall identifier,In identifier((prefix++parameters)++pointers)->~In identifier(affine_nest_mutated nest).
Hypothesis LOWER : affine_lower_nest nest prefix parameters(L.Constant 0)
  (affine_checked_leaf_code coordinates parameters [] operations)=Some code.
Hypothesis DOMAIN : forall index,0<=index<count -> affine_math_domain bounds(coordinates++parameters) nest(valuation index) 0.
Hypothesis SOURCE_WORDS : forall index,0<=index<count ->
  affine_word_view(prefix++parameters)(valuation index)(PTree.set column(Vint(Int.repr index))(entry_temps entry)).
Hypothesis WORD_SCOPE : incl(prefix++parameters)(column::stable).
Hypothesis POINTER_STABLE : incl pointers stable.
Hypothesis HELPER_MEMBER : In helper stable.
Hypothesis HELPER : (entry_temps entry)!helper=Some(Vint(Int.repr upper)).
Hypotheses (LEAF_WRITES : writes_only leaf_written body) (HELPER_PRIVATE : ~In helper leaf_written).
Hypotheses (TYPE : typeof bound=type_int32s) (COLUMN_PRIVATE : ~In column stable).
Hypotheses (NORMAL : normal_statement source=true) (QUIET : quiet_statement source=true).
Hypothesis SOURCE_WRITES : writes_only source_written source.
Hypothesis COLUMN_UNWRITTEN : ~In column source_written.
Hypothesis STABLE_UNWRITTEN : forall identifier,In identifier stable -> ~In identifier source_written.
Hypothesis HEADER : forall index current memory,
  ready entry -> 0<=index<=count -> current!column=Some(Vint(Int.repr index)) ->
  temp_agree stable(entry_temps entry) current -> header_observations_match snapshots memory ->
  eval_expr(entry_ge entry)(entry_env entry) current memory bound(Vint(temp_word cache(entry_temps entry))).
Hypothesis POINTER_PUBLIC : incl pointers public.
Hypothesis OBSERVERS : forall observer,In observer observers ->
  word_observer_receipt(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry) observer.
Hypothesis OBSERVER_SCOPE : forall observer,In observer observers -> expression_scope public(word_observer_address observer).
Hypothesis PUBLIC_LIVE : incl public live.
Hypothesis BASE_PUBLIC : temp_agree public(entry_temps entry) base.
Hypothesis CACHE_PUBLIC : In cache public.
Hypothesis UNIQUE : NoDup(map controls(affine_nest_controls nest)).
Hypothesis ITERATOR_VALUES : forall identifier,In identifier(affine_nest_iterators nest)->values identifier=controls identifier.
Hypothesis CONTROL_PRIVATE : forall identifier,In identifier(affine_nest_controls nest)->
  ~In(controls identifier)(cursor::limit::live) /\ controls identifier<>flag.
Hypotheses (CURSOR_PRIVATE : ~In cursor live) (LIMIT_PRIVATE : ~In limit live) (FLAG_PRIVATE : ~In flag live).
Hypotheses (CURSOR_LIMIT : cursor<>limit) (CURSOR_FLAG : cursor<>flag) (LIMIT_FLAG : limit<>flag).
Hypothesis FLAG_WORD : ~In flag(map values(coordinates++parameters)).
Hypothesis COLUMN_VALUE : values column=cursor.
Hypothesis INDEX_VALUE : forall index,0<=index<count -> valuation index column=index.
Hypothesis OTHER_VALUE : forall index identifier,0<=index<count -> In identifier(prefix++parameters) ->
  identifier<>column -> valuation index identifier=valuation 0 identifier.
Hypothesis OTHER_LIVE : forall identifier,In identifier(prefix++parameters) -> identifier<>column -> In(values identifier) live.
Hypothesis BASE_WORDS : forall index,0<=index<count -> forall identifier,In identifier(prefix++parameters) -> identifier<>column ->
  base!(values identifier)=Some(Vint(Int.repr(valuation 0 identifier))).

Lemma constant_inner_source_words index current :
  0<=index<count -> current!column=Some(Vint(Int.repr index)) ->
  temp_agree stable(entry_temps entry) current -> affine_word_view(prefix++parameters)(valuation index) current.
Proof.
  intros RANGE COLUMN FRAME identifier MEMBER.
  pose proof(SOURCE_WORDS RANGE identifier MEMBER) as WORD.
  destruct(Pos.eq_dec identifier column) as [->|OTHER]; [rewrite PTree.gss in WORD; congruence|].
  rewrite PTree.gso in WORD by exact OTHER; rewrite FRAME; [exact WORD|].
  destruct(WORD_SCOPE identifier MEMBER) as [SAME|STABLE]; [congruence|exact STABLE].
Qed.

Lemma constant_inner_scan_words index current :
  0<=index<count -> current!cursor=Some(Vint(Int.repr index)) -> temp_agree live base current ->
  affine_scan_word_view(prefix++parameters) values(valuation index) current.
Proof.
  intros RANGE CURSOR FRAME identifier MEMBER.
  destruct(Pos.eq_dec identifier column) as [->|OTHER].
  - rewrite COLUMN_VALUE,INDEX_VALUE by exact RANGE; exact CURSOR.
  - rewrite FRAME by(apply OTHER_LIVE; assumption); rewrite OTHER_VALUE by assumption;
      eapply BASE_WORDS; eassumption.
Qed.

Lemma constant_inner_mapped_scope : incl(map values(prefix++parameters))(cursor::limit::live).
Proof.
  intros mapped MEMBER; apply in_map_iff in MEMBER as [identifier [<- MEMBER]].
  destruct(Pos.eq_dec identifier column) as [->|OTHER].
  - rewrite COLUMN_VALUE; left; reflexivity.
  - right; right; apply OTHER_LIVE; assumption.
Qed.

Theorem constant_inner_body_execution index current :
  0<=index<count -> source_prefix index ->
  current!cursor=Some(Vint(Int.repr index)) -> current!flag=Some(memory_boolean_word true) ->
  temp_agree live base current -> exists checked,
    exec_stmt fe(entry_ge entry)(entry_env entry) current(entry_memory entry)
      (constant_joint_inner_body nest controls values flag observers operations) E0 checked(entry_memory entry) Out_normal /\
    temp_agree(cursor::limit::live) current checked /\ checked!flag=Some(memory_boolean_word(test index)).
Proof.
  intros RANGE PREFIX CURSOR FLAG FRAME.
  destruct(@expression_body_prefix_receipt_at fe column cache bound source stable ready(fun _=>snapshots) entry
    TYPE NORMAL QUIET HEADER index PREFIX(proj2 RANGE))
    as [temps [memory [after [final [COLUMN [SOURCE_FRAME [MATCH [BACK SOURCE]]]]]]]].
  assert (WORDS : affine_word_view(prefix++parameters)(valuation index) temps) by(eapply constant_inner_source_words; eassumption).
  assert (POINTERS : temp_agree pointers(entry_temps entry) temps).
  { eapply temp_agree_weaken; [exact POINTER_STABLE|exact SOURCE_FRAME]. }
  assert (BOUND_WORD : temps!helper=Some(Vint(Int.repr upper))) by(rewrite SOURCE_FRAME by exact HELPER_MEMBER; exact HELPER).
  assert (PUBLIC : temp_agree public(entry_temps entry) current).
  { eapply temp_agree_trans; [exact BASE_PUBLIC|eapply temp_agree_weaken; eassumption]. }
  unfold constant_joint_inner_body,test.
  eapply constant_body_joint_scan_execution with(certificate:=certificate)(fe:=fe)
    (ge:=entry_ge entry)(locals:=entry_env entry)(initial:=entry_temps entry)(temps:=temps)
    (guard_memory:=entry_memory entry)(memory:=memory)(after:=after)(final:=final)
    (code:=code)(written:=leaf_written)(coordinates:=coordinates)(prefix:=prefix)(parameters:=parameters)
    (pointers:=pointers)(public:=public)(live:=cursor::limit::live)(current:=current)(good:=true)
    (controls:=controls)(values:=values)(flag:=flag)(observers:=observers); try eassumption.
  - apply DOMAIN; exact RANGE.
  - cbn; intuition congruence.
  - intro BAD; apply FLAG_PRIVATE,PUBLIC_LIVE; exact BAD.
  - intros identifier MEMBER; right; right; apply PUBLIC_LIVE; exact MEMBER.
  - exact constant_inner_mapped_scope.
  - eapply constant_inner_scan_words; eassumption.
Qed.

Theorem constant_inner_body_preserved index :
  0<=index<count -> source_prefix index -> test index=true ->
  expression_body_preserved fe column source stable(fun _=>snapshots) index entry.
Proof.
  intros RANGE PREFIX CHECK.
  destruct(@expression_body_prefix_receipt_at fe column cache bound source stable ready(fun _=>snapshots) entry
    TYPE NORMAL QUIET HEADER index PREFIX(proj2 RANGE))
    as [temps [memory [after [final [COLUMN [FRAME [MATCH [BACK SOURCE]]]]]]]].
  eapply constant_body_joint_scan_inner_preserved with(certificate:=certificate)
    (temps:=temps)(memory:=memory)(after:=after)(final:=final)(code:=code)(written:=leaf_written)
    (coordinates:=coordinates)(prefix:=prefix)(parameters:=parameters)(pointers:=pointers)
    (valuation:=valuation index); try eassumption.
  - apply DOMAIN; exact RANGE.
  - eapply constant_inner_source_words; eassumption.
  - eapply temp_agree_weaken; [exact POINTER_STABLE|exact FRAME].
  - rewrite FRAME by exact HELPER_MEMBER; exact HELPER.
  - apply SOURCE_WORDS; exact RANGE.
Qed.

Theorem constant_inner_next_prefix index :
  0<=index<count -> source_prefix index -> test index=true -> source_prefix(index+1).
Proof.
  intros RANGE PREFIX CHECK.
  eapply expression_body_prefix_advance_at with(written:=source_written); try eassumption.
  - intros ge locals current memory after final RUN; eapply structured_memory_accesses_back; eassumption.
  - exact(proj2 RANGE).
  - eapply constant_inner_body_preserved; eassumption.
Qed.

Theorem constant_joint_inner_loop_execution checked :
  source_prefix 0 -> checked!flag=Some(memory_boolean_word true) -> temp_agree live base checked ->
  exists after,
    exec_stmt fe(entry_ge entry)(entry_env entry) checked(entry_memory entry)
      (constant_joint_inner_statement cache cursor limit flag nest controls values observers operations)
      E0 after(entry_memory entry) Out_normal /\ temp_agree live checked after /\
    after!flag=Some(memory_boolean_word(memory_boolean_scan_result test 0(Z.to_nat count))) /\
    (memory_boolean_scan_result test 0(Z.to_nat count)=true -> forall index,0<=index<count ->
      expression_body_preserved fe column source stable(fun _=>snapshots) index entry).
Proof.
  intros PREFIX FLAG FRAME.
  pose proof PREFIX as [READY [CACHE [RANGE REST]]].
  assert (NONNEGATIVE : 0<=count) by lia.
  assert (UPPER_RANGE : signed_range count) by apply Int.signed_range.
  set(cached:=PTree.set limit(Vint(temp_word cache(entry_temps entry))) checked).
  set(initialized:=PTree.set cursor(Vint Int.zero) cached).
  assert (INIT_FRAME : temp_agree live checked initialized).
  { eapply temp_agree_trans with(le1:=cached); apply temp_agree_set; assumption. }
  assert (INIT_CURSOR : initialized!cursor=Some(Vint(Int.repr 0))) by(unfold initialized; apply PTree.gss).
  assert (INIT_BOUND : initialized!limit=Some(Vint(Int.repr count))).
  { unfold initialized,cached; rewrite PTree.gso by congruence; rewrite PTree.gss; unfold count; rewrite Int.repr_signed; reflexivity. }
  assert (INIT_FLAG : initialized!flag=Some(memory_boolean_word true)).
  { unfold initialized,cached; rewrite !PTree.gso by congruence; exact FLAG. }
  assert (BODY : forall index current,signed_range index -> 0<=index<count -> source_prefix index ->
    current!cursor=Some(Vint(Int.repr index)) -> current!limit=Some(Vint(Int.repr count)) ->
    current!flag=Some(memory_boolean_word true) -> temp_agree live base current -> exists after,
      exec_stmt fe(entry_ge entry)(entry_env entry) current(entry_memory entry)
        (constant_joint_inner_body nest controls values flag observers operations) E0 after(entry_memory entry) Out_normal /\
      temp_agree(cursor::limit::live) current after /\ after!flag=Some(memory_boolean_word(test index))).
  { intros index current INDEX RANGE' INV CURSOR LIMIT FLAG' FRAME'; eapply constant_inner_body_execution; eassumption. }
  destruct(@short_circuit_prefix_loop_execution fe(entry_ge entry)(entry_env entry)(entry_memory entry)
    cursor limit flag(constant_joint_inner_body nest controls values flag observers operations) live base 0 count source_prefix test
    CURSOR_LIMIT CURSOR_FLAG LIMIT_FLAG CURSOR_PRIVATE UPPER_RANGE constant_inner_next_prefix BODY(Z.to_nat count) 0 initialized)
    as [after [RUN [KEEP [RESULT ACCEPTED]]]].
  - rewrite Z2Nat.id by exact NONNEGATIVE; lia.
  - lia.
  - unfold signed_range; change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia.
  - exact PREFIX.
  - exact INIT_CURSOR.
  - exact INIT_BOUND.
  - exact INIT_FLAG.
  - eapply temp_agree_trans; eassumption.
  - exists after; split.
    + unfold constant_joint_inner_statement.
      eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=cached)(m1:=entry_memory entry).
      * constructor; constructor.
        assert (WORD : (entry_temps entry)!cache=Some(Vint(temp_word cache(entry_temps entry)))).
        { destruct CACHE as [word WORD]; unfold temp_word; rewrite WORD; reflexivity. }
        rewrite FRAME by(apply PUBLIC_LIVE; exact CACHE_PUBLIC); rewrite BASE_PUBLIC by exact CACHE_PUBLIC; exact WORD.
      * eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=initialized)(m1:=entry_memory entry); [constructor; constructor|exact RUN].
    + split; [eapply temp_agree_trans; eassumption|split; [exact RESULT|]].
      intros ACCEPT index ACTIVE; destruct(ACCEPTED ACCEPT index ACTIVE) as [INV CHECK].
      eapply constant_inner_body_preserved; eassumption.
Qed.

(** Refusal at the first subbody ends the actual loop with cursor zero. No
    source receipt, physical capability, or execution for a later subbody is
    used. This matters when an alias changed the original loaded bound. *)
Theorem constant_joint_inner_first_refusal checked :
  source_prefix 0 -> 0<count -> test 0=false ->
  checked!flag=Some(memory_boolean_word true) -> temp_agree live base checked ->
  exists after,
    exec_stmt fe(entry_ge entry)(entry_env entry) checked(entry_memory entry)
      (constant_joint_inner_statement cache cursor limit flag nest controls values observers operations)
      E0 after(entry_memory entry) Out_normal /\ temp_agree live checked after /\
    after!cursor=Some(Vint Int.zero) /\ after!flag=Some(memory_boolean_word false).
Proof.
  intros PREFIX ACTIVE REFUSE FLAG FRAME.
  pose proof PREFIX as [READY [CACHE [RANGE REST]]].
  set(cached:=PTree.set limit(Vint(temp_word cache(entry_temps entry))) checked).
  set(initialized:=PTree.set cursor(Vint Int.zero) cached).
  assert (INIT_FRAME : temp_agree live checked initialized).
  { eapply temp_agree_trans with(le1:=cached); apply temp_agree_set; assumption. }
  assert (INIT_CURSOR : initialized!cursor=Some(Vint(Int.repr 0))) by(unfold initialized; apply PTree.gss).
  assert (INIT_BOUND : initialized!limit=Some(Vint(Int.repr count))).
  { unfold initialized,cached; rewrite PTree.gso by congruence; rewrite PTree.gss; unfold count; rewrite Int.repr_signed; reflexivity. }
  assert (INIT_FLAG : initialized!flag=Some(memory_boolean_word true)).
  { unfold initialized,cached; rewrite !PTree.gso by congruence; exact FLAG. }
  assert (FIRST : exists after,
    exec_stmt fe(entry_ge entry)(entry_env entry) initialized(entry_memory entry)
      (constant_joint_inner_body nest controls values flag observers operations) E0 after(entry_memory entry) Out_normal /\
    temp_agree(cursor::limit::live) initialized after /\ after!flag=Some(memory_boolean_word(test 0))).
  { eapply constant_inner_body_execution;
      [lia|exact PREFIX|exact INIT_CURSOR|exact INIT_FLAG|eapply temp_agree_trans; eassumption]. }
  destruct FIRST as [after [BODY [KEEP RESULT]]].
  rewrite REFUSE in RESULT.
  assert (STOP : exec_stmt fe(entry_ge entry)(entry_env entry) initialized(entry_memory entry)
    (short_circuit_prefix_loop cursor limit flag(constant_joint_inner_body nest controls values flag observers operations))
    E0 after(entry_memory entry) Out_normal).
  { unfold short_circuit_prefix_loop,counted_loop.
    destruct(@counter_condition_at(entry_ge entry)(entry_env entry) initialized(entry_memory entry) cursor limit 0 count
      CURSOR_LIMIT INIT_CURSOR INIT_BOUND
      ltac:(unfold signed_range; change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia)
      (Int.signed_range(temp_word cache(entry_temps entry)))) as [value [EVAL BOOL]].
    assert (LT : (0<?count)=true) by(apply Z.ltb_lt; exact ACTIVE); rewrite LT in BOOL.
    eapply exec_Sloop_stop1 with(out':=Out_break); [|constructor].
    eapply exec_Sifthenelse; [exact EVAL|exact BOOL|].
    eapply short_circuit_point_execution with(answer:=false); eassumption. }
  exists after; split.
  - unfold constant_joint_inner_statement.
    eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=cached)(m1:=entry_memory entry).
    + constructor; constructor.
      assert (WORD : (entry_temps entry)!cache=Some(Vint(temp_word cache(entry_temps entry)))).
      { destruct CACHE as [word WORD]; unfold temp_word; rewrite WORD; reflexivity. }
      rewrite FRAME by(apply PUBLIC_LIVE; exact CACHE_PUBLIC); rewrite BASE_PUBLIC by exact CACHE_PUBLIC; exact WORD.
    + eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=initialized)(m1:=entry_memory entry); [constructor; constructor|exact STOP].
  - split.
    + eapply temp_agree_trans; [exact INIT_FRAME|].
      eapply temp_agree_weaken; [|exact KEEP]; intros identifier MEMBER; right; right; exact MEMBER.
    + split; [rewrite KEEP by(left; reflexivity); exact INIT_CURSOR|exact RESULT].
Qed.

(** Open the inner source from the current outer prefix, execute the actual
    inner check, and consume its acceptance directly to advance the outer
    prefix. The caller supplies header laws, not a BODY/PRESERVE callback. *)
Theorem constant_joint_current_row_execution origin row root_cache root_bound outer_stable outer_ready index checked :
  stable=row::outer_stable -> entry=nested_expression_inner_entry row column index origin ->
  ~In row outer_stable -> ~In column outer_stable -> row<>column -> In cache outer_stable ->
  typeof root_bound=type_int32s -> register_domain cache origin -> 0<=count -> ready entry ->
  (forall k current memory,outer_ready origin -> 0<=k<=Int.signed(temp_word root_cache(entry_temps origin)) ->
    current!row=Some(Vint(Int.repr k)) -> temp_agree outer_stable(entry_temps origin) current ->
    header_observations_match snapshots memory ->
    eval_expr(entry_ge origin)(entry_env origin) current memory root_bound(Vint(temp_word root_cache(entry_temps origin)))) ->
  expression_body_prefix fe row root_cache root_bound(nested_expression_body column bound source) outer_stable
    outer_ready(fun _=>snapshots) index origin -> index<Int.signed(temp_word root_cache(entry_temps origin)) ->
  checked!flag=Some(memory_boolean_word true) -> temp_agree live base checked -> exists after,
    exec_stmt fe(entry_ge origin)(entry_env origin) checked(entry_memory origin)
      (constant_joint_inner_statement cache cursor limit flag nest controls values observers operations)
      E0 after(entry_memory origin) Out_normal /\ temp_agree live checked after /\
    after!flag=Some(memory_boolean_word(memory_boolean_scan_result test 0(Z.to_nat count))) /\
    (memory_boolean_scan_result test 0(Z.to_nat count)=true ->
      (forall j current memory exit final,0<=j<Int.signed(temp_word cache(entry_temps origin)) ->
        current!row=Some(Vint(Int.repr index)) -> current!column=Some(Vint(Int.repr j)) ->
        temp_agree outer_stable(entry_temps origin) current -> header_observations_match snapshots memory ->
        exec_stmt fe(entry_ge origin)(entry_env origin) current memory source E0 exit final Out_normal ->
        header_observations_match snapshots final) /\
      expression_body_prefix fe row root_cache root_bound(nested_expression_body column bound source) outer_stable
        outer_ready(fun _=>snapshots)(index+1) origin).
Proof.
  intros STABLE ENTRY ROW_PRIVATE COLUMN_FRESH DISTINCT CACHE_MEMBER ROOT_TYPE CACHE_DOMAIN NONNEGATIVE INNER_READY
    ROOT_HEADER PREFIX ACTIVE FLAG FRAME.
  pose proof PREFIX as [OUTER_READY [ROOT_DOMAIN [ROOT_RANGE REST]]].
  assert (CACHE_WORD : temp_word cache(entry_temps entry)=temp_word cache(entry_temps origin)).
  { unfold temp_word; rewrite ENTRY;
      rewrite(@joint_inner_cache_frame row column index origin outer_stable cache ROW_PRIVATE COLUMN_FRESH CACHE_MEMBER); reflexivity. }
  assert (COUNT : count=Int.signed(temp_word cache(entry_temps origin))) by(unfold count; rewrite CACHE_WORD; reflexivity).
  assert (INITIAL : source_prefix 0).
  { unfold source_prefix.
    eapply expression_body_prefix_ready_change with(first:=fun _=>outer_ready origin); [|exact INNER_READY].
    rewrite ENTRY,STABLE.
    eapply nested_expression_prefix_open with(entry:=origin)(row:=row)(cache:=root_cache)(bound:=root_bound)
      (column:=column)(child_cache:=cache)(child_bound:=bound)(body:=source)(stable:=outer_stable)(i:=index)
      (ready:=outer_ready)(observations:=fun _=>snapshots)(fe:=fe);
      [exact ROOT_TYPE|exact QUIET|exact ROW_PRIVATE|exact COLUMN_FRESH|exact DISTINCT|exact CACHE_MEMBER|
       exact CACHE_DOMAIN|rewrite <-COUNT; exact NONNEGATIVE| |exact PREFIX|exact ACTIVE].
    intros current memory ROW CURRENT OBSERVED; eapply ROOT_HEADER; eassumption. }
  assert (INNER : exists after,
    exec_stmt fe(entry_ge entry)(entry_env entry) checked(entry_memory entry)
      (constant_joint_inner_statement cache cursor limit flag nest controls values observers operations)
      E0 after(entry_memory entry) Out_normal /\ temp_agree live checked after /\
    after!flag=Some(memory_boolean_word(memory_boolean_scan_result test 0(Z.to_nat count))) /\
    (memory_boolean_scan_result test 0(Z.to_nat count)=true -> forall j,0<=j<count ->
      expression_body_preserved fe column source stable(fun _=>snapshots) j entry)).
  { apply constant_joint_inner_loop_execution; assumption. }
  destruct INNER as [after [RUN [KEEP [RESULT PRESERVES]]]].
  exists after; split.
  - rewrite ENTRY in RUN; cbn [nested_expression_inner_entry entry_ge entry_env entry_memory] in RUN; exact RUN.
  - split; [exact KEEP|split; [exact RESULT|]].
    intro ACCEPT.
    assert (ROW_PRESERVED : forall j current memory exit final,0<=j<Int.signed(temp_word cache(entry_temps origin)) ->
      current!row=Some(Vint(Int.repr index)) -> current!column=Some(Vint(Int.repr j)) ->
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
    eapply nested_expression_prefix_advance with(child_cache:=cache)(written:=source_written)
      (ready:=fun other=>outer_ready other /\ other=origin);
      [exact ROOT_TYPE|exact TYPE|exact ROW_PRIVATE|exact COLUMN_FRESH|exact DISTINCT|exact CACHE_MEMBER|
       exact NORMAL|exact QUIET|exact SOURCE_WRITES| |exact COLUMN_UNWRITTEN| | |exact CACHE_DOMAIN|
       rewrite <-COUNT; exact NONNEGATIVE| | | |exact ACTIVE].
    + apply STABLE_UNWRITTEN; rewrite STABLE; left; reflexivity.
    + intros identifier MEMBER; apply STABLE_UNWRITTEN; rewrite STABLE; right; exact MEMBER.
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
End INNER.

(** An empty child guard has no observation, parameter-word, output-pointer,
    or source-body receipt premise. Only the actual cached zero and private
    control names are needed for this execution. *)
Theorem constant_joint_inner_empty_execution fe ge locals memory cache cursor limit flag nest controls values observers operations
  checked live :
  cursor<>limit -> cursor<>flag -> limit<>flag ->
  ~In cursor live -> ~In limit live ->
  checked!cache=Some(Vint Int.zero) -> checked!flag=Some(memory_boolean_word true) ->
  let initialized:=PTree.set cursor(Vint Int.zero)(PTree.set limit(Vint Int.zero) checked) in
  exec_stmt fe ge locals checked memory
    (constant_joint_inner_statement cache cursor limit flag nest controls values observers operations)
    E0 initialized memory Out_normal /\ temp_agree live checked initialized /\
  initialized!cursor=Some(Vint Int.zero) /\ initialized!flag=Some(memory_boolean_word true).
Proof.
  intros CURSOR_LIMIT CURSOR_FLAG LIMIT_FLAG CURSOR_PRIVATE LIMIT_PRIVATE CACHE FLAG; cbn zeta.
  set(cached:=PTree.set limit(Vint Int.zero) checked).
  set(initialized:=PTree.set cursor(Vint Int.zero) cached).
  assert (CURSOR : initialized!cursor=Some(Vint(Int.repr 0))) by(unfold initialized; apply PTree.gss).
  assert (LIMIT : initialized!limit=Some(Vint(Int.repr 0))).
  { unfold initialized,cached; rewrite PTree.gso by congruence; apply PTree.gss. }
  assert (LOOP : exec_stmt fe ge locals initialized memory
    (short_circuit_prefix_loop cursor limit flag(constant_joint_inner_body nest controls values flag observers operations))
    E0 initialized memory Out_normal).
  { unfold short_circuit_prefix_loop,counted_loop.
    destruct(@counter_condition_at ge locals initialized memory cursor limit 0 0 CURSOR_LIMIT CURSOR LIMIT
      ltac:(unfold signed_range; change(-2147483648<=0<=2147483647); lia)
      ltac:(unfold signed_range; change(-2147483648<=0<=2147483647); lia)) as [value [EVAL BOOL]].
    rewrite Z.ltb_irrefl in BOOL.
    eapply exec_Sloop_stop1 with(out':=Out_break); [|constructor].
    eapply exec_Sifthenelse; [exact EVAL|exact BOOL|constructor]. }
  split.
  - unfold constant_joint_inner_statement.
    eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=cached)(m1:=memory).
    + constructor; constructor; exact CACHE.
    + eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=initialized)(m1:=memory); [constructor; constructor|exact LOOP].
  - split.
    + eapply temp_agree_trans with(le1:=cached); apply temp_agree_set; assumption.
    + split; [exact CURSOR|unfold initialized,cached; rewrite !PTree.gso by congruence; exact FLAG].
Qed.

Print Assumptions constant_inner_source_words.
Print Assumptions constant_inner_scan_words.
Print Assumptions constant_inner_body_execution.
Print Assumptions constant_inner_body_preserved.
Print Assumptions constant_inner_next_prefix.
Print Assumptions constant_joint_inner_loop_execution.
Print Assumptions constant_joint_inner_first_refusal.
Print Assumptions constant_joint_current_row_execution.
Print Assumptions constant_joint_inner_empty_execution.
