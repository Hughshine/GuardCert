From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCountedLoop ClightTempFrame.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation GuardMemoryBooleanScan.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestMathDomain
  AffineNestScanModel AffineNestScanSyntax AffineNestScanWords AffineNestScanLoop.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section EXECUTION.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable memory : mem.
Variable controls values : ident -> ident.
Variable flag : ident.
Variable leaf : statement.
Variable public : list ident.
Variable base : temp_env.

Theorem affine_scan_execution nest : forall prefix parameters valuation lower lower_code live temps accepted test bounds layout,
  affine_nest_bound_dependencies prefix parameters nest ->
  NoDup(map controls(affine_nest_controls nest)) ->
  (forall identifier, In identifier(affine_nest_iterators nest) -> values identifier=controls identifier) ->
  (forall identifier, In identifier(affine_nest_controls nest) -> ~In(controls identifier) live /\ controls identifier<>flag) ->
  ~In flag live -> incl public live -> incl(map values(prefix++parameters)) live ->
  affine_math_domain bounds layout nest valuation lower ->
  affine_scan_word_view(prefix++parameters) values valuation temps ->
  temp_agree public base temps -> temps!flag=Some(memory_boolean_word accepted) ->
  eval_expr ge locals temps memory lower_code(Vint(Int.repr lower)) ->
  (forall point current good protected,
    affine_scan_point nest valuation lower point ->
    affine_scan_word_view((prefix++affine_nest_iterators nest)++parameters) values point current ->
    temp_agree public base current -> current!flag=Some(memory_boolean_word good) -> ~In flag protected ->
    incl protected(map controls(affine_nest_controls nest)++live) ->
    exists after, exec_stmt fe ge locals current memory leaf E0 after memory Out_normal /\
      temp_agree protected current after /\ after!flag=Some(memory_boolean_word(good&&test point))) ->
  exists after,
    exec_stmt fe ge locals temps memory(affine_scan_statement nest controls values lower_code leaf) E0 after memory Out_normal /\
    temp_agree live temps after /\ after!flag=Some(memory_boolean_word(accepted&&affine_scan_result nest valuation lower test)).
Proof.
  induction nest as [source|iterator bound expression body child IH];
    intros prefix parameters valuation lower lower_code live temps accepted test bounds layout
      DEPENDENCIES UNIQUE COUNTERS PRIVATE FLAG_PRIVATE PUBLIC WORD_LIVE DOMAIN WORDS FRAME FLAG LOWER BODY.
  - cbn [affine_scan_statement affine_scan_result]; eapply BODY.
    + constructor.
    + cbn [affine_nest_iterators]; rewrite app_nil_r; exact WORDS.
    + exact FRAME.
    + exact FLAG.
    + exact FLAG_PRIVATE.
    + cbn [affine_nest_controls map app]; apply incl_refl.
  - destruct DEPENDENCIES as [READS DEPENDENCIES].
    destruct DOMAIN as [LOW_SIGNED [UP_SIGNED DOMAIN]].
    cbn [affine_nest_controls map] in UNIQUE.
    apply NoDup_cons_iff in UNIQUE as [ITER_PRIVATE REST].
    apply NoDup_cons_iff in REST as [BOUND_PRIVATE CHILD_UNIQUE].
    assert(DISTINCT:controls iterator<>controls bound) by(intro SAME; apply ITER_PRIVATE; cbn; auto).
    destruct(PRIVATE iterator ltac:(cbn; auto)) as [ITER_LIVE ITER_FLAG].
    destruct(PRIVATE bound ltac:(cbn; auto)) as [BOUND_LIVE BOUND_FLAG].
    set(upper:=memory_source_affine_math valuation expression).
    set(initialized:=PTree.set(controls bound)(Vint(Int.repr upper))
      (PTree.set(controls iterator)(Vint(Int.repr lower)) temps)).
    assert(INIT_FRAME:temp_agree live temps initialized).
    { unfold initialized; eapply temp_agree_trans; apply temp_agree_set; assumption. }
    assert(INIT_WORDS:affine_scan_word_view(prefix++parameters) values valuation initialized).
    { eapply affine_scan_word_view_frame; eassumption. }
    assert(INIT_FLAG:initialized!flag=Some(memory_boolean_word accepted)).
    { unfold initialized; rewrite !PTree.gso by congruence; exact FLAG. }
    assert(INIT_ITER:initialized!(controls iterator)=Some(Vint(Int.repr lower))).
    { unfold initialized; rewrite PTree.gso by congruence; apply PTree.gss. }
    assert(INIT_BOUND:initialized!(controls bound)=Some(Vint(Int.repr upper))).
    { unfold initialized; apply PTree.gss. }
    assert(LOOP_BODY:forall index current good, signed_range index -> lower<=index<upper ->
      current!(controls iterator)=Some(Vint(Int.repr index)) ->
      current!(controls bound)=Some(Vint(Int.repr upper)) ->
      current!flag=Some(memory_boolean_word good) -> temp_agree live initialized current ->
      exists after,
        exec_stmt fe ge locals current memory
          (affine_scan_statement child controls values(Econst_int Int.zero type_int32s) leaf) E0 after memory Out_normal /\
        temp_agree(controls iterator::controls bound::live) current after /\
        after!flag=Some(memory_boolean_word(good&&affine_scan_result child(memory_source_set_valuation valuation iterator index) 0 test))).
    { intros index current good INDEX RANGE ITER BOUND GOOD CURRENT.
      assert(OLD_WORDS:affine_scan_word_view(prefix++parameters) values valuation current).
      { eapply affine_scan_word_view_frame; [exact WORD_LIVE| |exact WORDS].
        eapply temp_agree_trans; eassumption. }
      assert(NEXT_WORDS:affine_scan_word_view((prefix++[iterator])++parameters) values
        (memory_source_set_valuation valuation iterator index) current).
      { intros identifier MEMBER; unfold memory_source_set_valuation.
        destruct(peq identifier iterator) as [->|OTHER].
        - rewrite COUNTERS by(cbn; auto); exact ITER.
        - apply OLD_WORDS; repeat rewrite in_app_iff in MEMBER; cbn in MEMBER;
            apply in_or_app; intuition congruence. }
      eapply IH with(prefix:=prefix++[iterator])(parameters:=parameters)
        (valuation:=memory_source_set_valuation valuation iterator index)(lower:=0)
        (live:=controls iterator::controls bound::live)(test:=test)(bounds:=bounds)(layout:=layout);
        try eassumption.
      - intros identifier MEMBER; apply COUNTERS; cbn; auto.
      - intros identifier MEMBER; destruct(PRIVATE identifier ltac:(cbn; auto)) as [FRESH NOT_FLAG].
        split; [|exact NOT_FLAG]; intro BAD; cbn in BAD; destruct BAD as [SAME|[SAME|BAD]]; [| |contradiction].
        + apply ITER_PRIVATE; right; rewrite SAME; apply in_map; exact MEMBER.
        + apply BOUND_PRIVATE; rewrite SAME; apply in_map; exact MEMBER.
      - cbn; intros [SAME|[SAME|BAD]]; congruence.
      - intros identifier MEMBER; cbn; auto.
      - intros identifier MEMBER; apply in_map_iff in MEMBER as [original [<- MEMBER]].
        repeat rewrite in_app_iff in MEMBER; cbn in MEMBER; destruct MEMBER as [[MEMBER|[<-|FALSE]]|MEMBER].
        + right; right; apply WORD_LIVE,in_map,in_or_app; auto.
        + left; symmetry; apply COUNTERS; cbn; auto.
        + contradiction.
        + right; right; apply WORD_LIVE,in_map,in_or_app; auto.
      - apply DOMAIN; exact RANGE.
      - eapply temp_agree_trans; [exact FRAME|].
        eapply temp_agree_weaken; [exact PUBLIC|]; eapply temp_agree_trans; eassumption.
      - constructor.
      - intros point inside before protected POINT INSIDE INSIDE_FRAME BEFORE PROTECTED INCLUDED.
        apply BODY; try eassumption.
        + econstructor; eassumption.
        + intros identifier MEMBER; apply INSIDE.
          repeat rewrite in_app_iff in *; cbn [affine_nest_iterators In] in *; tauto.
        + intros identifier MEMBER; apply INCLUDED in MEMBER.
          cbn [affine_nest_controls map]; repeat rewrite in_app_iff in *; cbn [In] in *; tauto. }
    destruct(@affine_boolean_scan_loop fe ge locals memory(controls iterator)(controls bound) flag
      (affine_scan_statement child controls values(Econst_int Int.zero type_int32s) leaf)
      upper lower live initialized
      (fun index=>affine_scan_result child(memory_source_set_valuation valuation iterator index) 0 test)
      DISTINCT ITER_FLAG BOUND_FLAG ITER_LIVE UP_SIGNED LOW_SIGNED LOOP_BODY
      initialized accepted INIT_ITER INIT_BOUND INIT_FLAG(temp_agree_refl _ _))
      as [after [RUN [AFTER GOOD]]].
    exists after; split.
    + cbn [affine_scan_statement]; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0).
      * constructor; exact LOWER.
      * eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [|exact RUN].
        constructor; apply affine_scan_expression_evaluation; intros identifier MEMBER.
        rewrite PTree.gso.
        -- apply WORDS,READS; exact MEMBER.
        -- intro SAME; apply ITER_LIVE; rewrite <-SAME; apply WORD_LIVE,in_map,READS; exact MEMBER.
    + split.
      * eapply temp_agree_trans; [exact INIT_FRAME|].
        eapply temp_agree_weaken; [|exact AFTER]; cbn; auto.
      * exact GOOD.
Qed.
End EXECUTION.
Print Assumptions affine_scan_execution.
