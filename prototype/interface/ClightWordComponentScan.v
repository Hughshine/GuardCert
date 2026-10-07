From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint
  ClightCountedLoop ClightNoWrap ClightLoopSyntax ClightRegionProgress ClightFrontendLoopProtocol CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryBooleanScan.
From GuardInterface Require Import ClightWordArithmeticTransport ClightWordCoordinateRename
  ClightDirectWordObservation ClightRenamedWordObservation ClightAffineJointObservation
  ClightObservedHeaderPrefix ClightStorePermissions ClightReadonlyCellSwap ClightExpressionBodyPrefix
  ClightExpressionPrefixAt ClightExpressionBodyTransport ClightShortCircuitPrefixLoop
  ClightStrictLoopProgress ClightSignedExpressionProgress.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A runtime cursor checks a literal-bound source component. The invariant
    contains a remaining original execution, rather than permissions for all
    future addresses. Only an accepting point advances that execution. *)
Section COMPONENT.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable memory : mem.
Variables iterator helper pointer cursor limit flag : ident.
Variables index rhs : expr.
Variable rename : ident -> ident.
Variables stable live : list ident.
Variables source_base base : temp_env.
Variable observers : list clight_word_observer.
Variable upper : Z.
Hypothesis WORD : word_arithmetic index.
Hypothesis NONNEGATIVE : 0<=upper.
Hypothesis UPPER : signed_range upper.
Hypothesis CACHE : source_base!helper=Some(Vint(Int.repr upper)).
Hypothesis CACHE_STABLE : In helper stable.
Hypothesis ITERATOR_FRESH : ~In iterator stable.
Hypothesis POINTER_STABLE : In pointer stable.
Hypothesis POINTER_LIVE : In pointer live.
Hypothesis POINTER : source_base!pointer=base!pointer.
Hypothesis SOURCE_SCOPE : incl(expression_temps index)(iterator::stable).
Hypothesis RENAME_ITERATOR : rename iterator=cursor.
Hypothesis RENAME_STABLE : incl(map rename stable)live.
Hypothesis SOURCE_WORDS : forall id,In id stable -> source_base!id=base!(rename id).
Hypotheses (CURSOR_LIMIT : cursor<>limit) (CURSOR_FLAG : cursor<>flag) (LIMIT_FLAG : limit<>flag).
Hypotheses (CURSOR_PRIVATE : ~In cursor live) (LIMIT_PRIVATE : ~In limit live) (FLAG_PRIVATE : ~In flag live).
Hypothesis READS : Forall(word_observer_receipt ge locals base memory)observers.
Hypothesis OBSERVER_SCOPE : forall observer,In observer observers -> expression_scope live(word_observer_address observer).

Let body := direct_word_store pointer index rhs.
Let bound := Econst_int(Int.repr upper)type_int32s.
Let snapshots := map word_observer_snapshot observers.
Let source_entry := Entry ge locals source_base memory.
Let observations := fun _ : clight_entry=>snapshots.
Let ready := fun _ : clight_entry=>True.
Definition word_component_prefix i :=
  expression_body_prefix fe iterator helper bound body stable ready observations i source_entry.
Definition word_component_at i := PTree.set cursor(Vint(Int.repr i))base.
Definition word_component_test i :=
  match word_address_evaluate(word_component_at i)pointer(word_rename rename index)with
  | Some(block,offset)=>forallb(direct_word_observer_flag block offset)observers
  | None=>false end.
Definition word_component_scan_body := renamed_word_check_code rename pointer index observers flag.
Definition word_component_scan_loop := short_circuit_prefix_loop cursor limit flag word_component_scan_body.
Definition word_component_scan_code := Ssequence(Sset limit bound)
  (Ssequence(Sset cursor(Econst_int Int.zero type_int32s))word_component_scan_loop).
Definition word_component_result := memory_boolean_scan_result word_component_test 0(Z.to_nat upper).

Lemma word_component_count : Int.signed(temp_word helper source_base)=upper.
Proof. unfold temp_word; rewrite CACHE; apply Int.signed_repr; exact UPPER. Qed.
Lemma word_component_header i current actual_memory :
  ready source_entry -> 0<=i<=Int.signed(temp_word helper source_base) ->
  current!iterator=Some(Vint(Int.repr i)) -> temp_agree stable source_base current ->
  header_observations_match snapshots actual_memory ->
  eval_expr ge locals current actual_memory bound(Vint(temp_word helper source_base)).
Proof. intros; unfold temp_word; rewrite CACHE; constructor. Qed.

Lemma word_component_source_frame i original current :
  original!iterator=Some(Vint(Int.repr i)) -> temp_agree stable source_base original ->
  current!cursor=Some(Vint(Int.repr i)) -> temp_agree live base current ->
  renamed_word_frame rename pointer index original current.
Proof.
  intros ROW SOURCE CURSOR PUBLIC; split.
  - rewrite SOURCE by exact POINTER_STABLE; rewrite POINTER.
    symmetry; apply PUBLIC; exact POINTER_LIVE.
  - intros id MEMBER; specialize(SOURCE_SCOPE id MEMBER).
    destruct SOURCE_SCOPE as [SAME|MEMBER']; [subst id; rewrite RENAME_ITERATOR; congruence|].
    rewrite SOURCE by exact MEMBER'; rewrite SOURCE_WORDS by exact MEMBER'.
    symmetry; apply PUBLIC,RENAME_STABLE,in_map; exact MEMBER'.
Qed.

Lemma word_component_probe_frame i current :
  current!cursor=Some(Vint(Int.repr i)) -> temp_agree live base current ->
  temp_agree(pointer::expression_temps(word_rename rename index))(word_component_at i)current.
Proof.
  intros CURSOR PUBLIC id [SAME|MEMBER]; [subst id|].
  - unfold word_component_at; rewrite PTree.gso by(intro SAME; apply CURSOR_PRIVATE; congruence).
    apply PUBLIC; exact POINTER_LIVE.
  - rewrite(word_rename_temps rename WORD)in MEMBER.
    apply in_map_iff in MEMBER as [raw [SAME MEMBER]]; subst id.
    specialize(SOURCE_SCOPE raw MEMBER); destruct SOURCE_SCOPE as [SAME|MEMBER']; [subst raw|].
    + rewrite RENAME_ITERATOR; unfold word_component_at; rewrite PTree.gss; exact CURSOR.
    + assert(LIVE:In(rename raw)live)by(apply RENAME_STABLE,in_map; exact MEMBER').
      unfold word_component_at; rewrite PTree.gso by(intro SAME; apply CURSOR_PRIVATE; congruence).
      apply PUBLIC; exact LIVE.
Qed.

Lemma word_component_test_frame i current :
  current!cursor=Some(Vint(Int.repr i)) -> temp_agree live base current ->
  renamed_word_point_flag rename pointer index observers(Entry ge locals current memory)=word_component_test i.
Proof.
  intros CURSOR PUBLIC; unfold renamed_word_point_flag,word_component_test; cbn [entry_temps].
  rewrite(@word_address_evaluate_frame pointer(word_rename rename index)(word_component_at i)current
    (word_rename_arithmetic rename WORD)(word_component_probe_frame CURSOR PUBLIC)); reflexivity.
Qed.

Theorem word_component_point_domain i current :
  word_component_prefix i -> i<upper ->
  current!cursor=Some(Vint(Int.repr i)) -> temp_agree live base current ->
  renamed_word_point_domain fe rename pointer index rhs observers(Entry ge locals current memory).
Proof.
  intros PREFIX ACTIVE CURSOR PUBLIC; split.
  - rewrite Forall_forall in READS|-*; intros observer MEMBER.
    eapply word_observer_receipt_frame; [apply READS; exact MEMBER|apply OBSERVER_SCOPE; exact MEMBER|exact PUBLIC].
  - destruct(@expression_body_prefix_receipt_at fe iterator helper bound body stable ready observations source_entry
      eq_refl eq_refl eq_refl word_component_header i PREFIX ltac:(cbn [source_entry entry_temps]; rewrite word_component_count; exact ACTIVE))
      as [original [actual_memory [after [final [ROW [FRAME [OBSERVED [BACK SOURCE]]]]]]]].
    exists original,actual_memory,after,final; split; [|split; assumption].
    eapply word_component_source_frame; eassumption.
Qed.

Theorem word_component_point_preserved i : word_component_prefix i -> i<upper -> word_component_test i=true ->
  expression_body_preserved fe iterator body stable observations i source_entry.
Proof.
  intros PREFIX ACTIVE ACCEPT.
  assert(PUBLIC:temp_agree live base(word_component_at i))by(apply temp_agree_set; exact CURSOR_PRIVATE).
  pose proof(@word_component_point_domain i(word_component_at i)PREFIX ACTIVE(PTree.gss _ _ _)PUBLIC)as DOMAIN.
  pose proof(@renamed_word_point_sound fe rename pointer index rhs observers
    (Entry ge locals(word_component_at i)memory)WORD DOMAIN ACCEPT)as PRESERVE.
  intros original actual_memory after final ROW FRAME OBSERVED SOURCE.
  eapply PRESERVE.
  - eapply word_component_source_frame; [exact ROW|exact FRAME|apply PTree.gss|exact PUBLIC].
  - exact OBSERVED.
  - exact SOURCE.
Qed.

Theorem word_component_prefix_advance i :
  0<=i<upper -> word_component_prefix i -> word_component_test i=true -> word_component_prefix(i+1).
Proof.
  intros RANGE PREFIX ACCEPT; unfold word_component_prefix.
  eapply(@expression_body_prefix_advance_at fe iterator helper bound body stable ready observations source_entry
    eq_refl eq_refl eq_refl word_component_header [] i).
  - exact ITERATOR_FRESH.
  - constructor.
  - intro MEMBER; inversion MEMBER.
  - intros id MEMBER EMPTY; inversion EMPTY.
  - intros ge' locals' current before after final RUN.
    destruct(direct_word_store_receipt RUN)as [block [offset [value [ADDRESS [STORE _]]]]].
    destruct(@storev_word_facts _ _ _ _ _ STORE)as [_ RAW].
    eapply store_memory_accesses_back; exact RAW.
  - exact PREFIX.
  - cbn [source_entry entry_temps]; rewrite word_component_count; lia.
  - apply word_component_point_preserved; [exact PREFIX|lia|exact ACCEPT].
Qed.

Theorem word_component_scan_body_execution i current :
  word_component_prefix i -> i<upper ->
  current!cursor=Some(Vint(Int.repr i)) -> temp_agree live base current ->
  exists after,
    exec_stmt fe ge locals current memory word_component_scan_body E0 after memory Out_normal /\
    temp_agree(cursor::limit::live)current after /\ after!flag=Some(memory_boolean_word(word_component_test i)).
Proof.
  intros PREFIX ACTIVE CURSOR PUBLIC.
  pose proof(@word_component_point_domain i current PREFIX ACTIVE CURSOR PUBLIC)as DOMAIN.
  pose proof(@renamed_word_check_execution fe rename pointer index rhs observers(Entry ge locals current memory)flag WORD DOMAIN)as RUN.
  rewrite(word_component_test_frame CURSOR PUBLIC)in RUN.
  exists(PTree.set flag(memory_boolean_word(word_component_test i))current); split; [exact RUN|split].
  - apply temp_agree_set; cbn; intros [SAME|[SAME|MEMBER]]; congruence.
  - apply PTree.gss.
Qed.

Theorem word_component_scan_loop_execution current :
  word_component_prefix 0 ->
  current!cursor=Some(Vint Int.zero) -> current!limit=Some(Vint(Int.repr upper)) ->
  current!flag=Some(memory_boolean_word true) -> temp_agree live base current ->
  exists after,
    exec_stmt fe ge locals current memory word_component_scan_loop E0 after memory Out_normal /\
    temp_agree live current after /\ after!flag=Some(memory_boolean_word word_component_result) /\
    (word_component_result=true -> forall i,0<=i<upper ->
      word_component_prefix i /\ word_component_test i=true).
Proof.
  intros PREFIX CURSOR LIMIT FLAG PUBLIC.
  eapply(@short_circuit_prefix_loop_execution fe ge locals memory cursor limit flag word_component_scan_body
    live base 0 upper word_component_prefix word_component_test CURSOR_LIMIT CURSOR_FLAG LIMIT_FLAG CURSOR_PRIVATE UPPER).
  - exact word_component_prefix_advance.
  - intros i temps SIGNED RANGE INV ROW BOUND TRUE FRAME.
    eapply word_component_scan_body_execution; eauto; lia.
  - rewrite Z2Nat.id by exact NONNEGATIVE; lia.
  - lia.
  - unfold signed_range; change Int.min_signed with(-2147483648); change Int.max_signed with 2147483647; lia.
  - exact PREFIX.
  - exact CURSOR.
  - exact LIMIT.
  - exact FLAG.
  - exact PUBLIC.
Qed.

Theorem word_component_scan_execution current : word_component_prefix 0 ->
  current!flag=Some(memory_boolean_word true) -> temp_agree live base current ->
  exists after,
    exec_stmt fe ge locals current memory word_component_scan_code E0 after memory Out_normal /\
    temp_agree live current after /\ after!flag=Some(memory_boolean_word word_component_result) /\
    (word_component_result=true -> forall i,0<=i<upper ->
      expression_body_preserved fe iterator body stable observations i source_entry).
Proof.
  intros PREFIX FLAG PUBLIC.
  set(prepared:=PTree.set cursor(Vint Int.zero)(PTree.set limit(Vint(Int.repr upper))current)).
  assert(FRAME:temp_agree live current prepared).
  { eapply temp_agree_trans; apply temp_agree_set; assumption. }
  destruct(@word_component_scan_loop_execution prepared PREFIX (PTree.gss _ _ _)
    ltac:(unfold prepared; rewrite PTree.gso by congruence; apply PTree.gss)
    ltac:(unfold prepared; rewrite !PTree.gso by congruence; exact FLAG)
    ltac:(eapply temp_agree_trans; eassumption))as [after [LOOP [AFTER [RESULT CHECKED]]]].
  exists after; split.
  - unfold word_component_scan_code; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0);
      [apply exec_Sset; constructor|].
    eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [apply exec_Sset; constructor|exact LOOP].
  - split; [eapply temp_agree_trans; eassumption|split; [exact RESULT|]].
    intros ACCEPT i RANGE; destruct(CHECKED ACCEPT i RANGE)as [INV TRUE].
    apply word_component_point_preserved; [exact INV|lia|exact TRUE].
Qed.

Theorem word_component_accepted_source_transport i current actual_memory trace after final outcome :
  word_component_prefix 0 -> word_component_result=true -> 0<=i<=upper ->
  current!iterator=Some(Vint(Int.repr i)) -> temp_agree stable source_base current ->
  header_observations_match snapshots actual_memory ->
  exec_stmt fe ge locals current actual_memory
    (strict_frontend_loop iterator(signed_expression_test iterator bound)body)trace after final outcome ->
  exec_stmt fe ge locals current actual_memory(frontend_counted_loop iterator helper body)trace after final outcome /\
    header_observations_match snapshots final.
Proof.
  intros PREFIX ACCEPT RANGE ROW FRAME OBSERVED SOURCE.
  destruct(@word_component_scan_execution(PTree.set flag(memory_boolean_word true)base)PREFIX
    (PTree.gss _ _ _)ltac:(apply temp_agree_set; exact FLAG_PRIVATE))as [checked [RUN [PUBLIC [FLAG PRESERVE]]]].
  assert(CACHED:
    exec_stmt fe ge locals current actual_memory(frontend_counted_loop iterator helper body)trace after final outcome /\
    expression_body_snapshot iterator stable source_base snapshots(Int.signed(Int.repr upper))after final).
  { eapply(@expression_body_bound_cached fe ge locals iterator helper bound body stable [] source_base snapshots(Int.repr upper)).
    - reflexivity.
    - exact CACHE.
    - exact CACHE_STABLE.
    - exact ITERATOR_FRESH.
    - reflexivity.
    - reflexivity.
    - constructor.
    - intro EMPTY; inversion EMPTY.
    - intros id MEMBER EMPTY; inversion EMPTY.
    - intros; constructor.
    - intros point original before exit last ACTIVE COUNTER STABLE INITIAL BODY.
      eapply(PRESERVE ACCEPT point); [rewrite Int.signed_repr in ACTIVE by exact UPPER; exact ACTIVE|
        exact COUNTER|exact STABLE|exact INITIAL|exact BODY].
    - exists i; split; [rewrite Int.signed_repr by exact UPPER; exact RANGE|].
      split; [exact ROW|split; assumption].
    - exact SOURCE. }
  destruct CACHED as [MODEL [last [LAST_RANGE [LAST_ROW [LAST_FRAME LAST_OBSERVED]]]]].
  split; assumption.
Qed.
End COMPONENT.

Print Assumptions word_component_count.
Print Assumptions word_component_source_frame.
Print Assumptions word_component_probe_frame.
Print Assumptions word_component_test_frame.
Print Assumptions word_component_point_domain.
Print Assumptions word_component_point_preserved.
Print Assumptions word_component_prefix_advance.
Print Assumptions word_component_scan_body_execution.
Print Assumptions word_component_scan_loop_execution.
Print Assumptions word_component_scan_execution.
Print Assumptions word_component_accepted_source_transport.
