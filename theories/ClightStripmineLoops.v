From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightCountedProtocol ClightTempFrame
  ClightFramedLoop ClightFrontendLoopProtocol ClightFrontendRegion ClightLoopExecution ClightLoopSyntax
  ClightParametricLoops ClightTempFootprint ClightProjectedExecution CountedStripmine.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_body_writes_empty body : memory_body body = true -> writes_only [] body.
Proof.
  induction body; cbn [memory_body]; try discriminate; intros CHECK; try constructor;
    try (apply andb_true_iff in CHECK as [LEFT RIGHT]); auto.
Qed.
Lemma memory_body_normal body : memory_body body = true -> normal_statement body = true.
Proof.
  induction body; cbn [memory_body normal_statement]; try discriminate; auto;
    intro CHECK; apply andb_true_iff in CHECK as [LEFT RIGHT]; rewrite IHbody1, IHbody2 by assumption; reflexivity.
Qed.
Lemma frontend_memory_writes iterator bound body : writes_only [] body ->
  writes_only [iterator] (frontend_counted_loop iterator bound body).
Proof.
  intro BODY; unfold frontend_counted_loop, counter_increment; repeat constructor; cbn; auto.
  eapply writes_only_weaken; [|exact BODY]; intros id BAD; contradiction.
Qed.

Definition stripmine_limit_expr iterator width := Ebinop Oadd (Etempvar iterator type_int32s)
  (Econst_int (Int.repr (Z.of_nat width)) type_int32s) type_int32s.
Definition stripmine_prepare iterator bound limit width :=
  Ssequence (Sset limit (stripmine_limit_expr iterator width))
    (Sifthenelse (counter_condition bound limit) (Sset limit (Etempvar bound type_int32s)) Sskip).
Definition stripmine_loop iterator bound limit width body :=
  Sloop (Ssequence (Sifthenelse (counter_condition iterator bound) Sskip Sbreak)
    (Ssequence (stripmine_prepare iterator bound limit width)
      (frontend_counted_loop iterator limit body))) Sskip.

Lemma stripmine_add_evaluation ge locals le memory iterator width x :
  le ! iterator = Some (Vint (Int.repr x)) ->
  eval_expr ge locals le memory (stripmine_limit_expr iterator width) (Vint (Int.repr (x + Z.of_nat width))).
Proof.
  intro ITER; unfold stripmine_limit_expr.
  eapply eval_Ebinop; [constructor; exact ITER|constructor|].
  change (Some (Vint (Int.add (Int.repr x) (Int.repr (Z.of_nat width)))) =
    Some (Vint (Int.repr (x + Z.of_nat width)))); f_equal; f_equal; unfold Int.add.
  apply Int.eqm_samerepr, Int.eqm_add; apply Int.eqm_sym, Int.eqm_unsigned_repr.
Qed.

Lemma stripmine_prepare_execution fe ge locals le memory iterator bound limit width x upper :
  iterator <> limit -> bound <> limit ->
  le ! iterator = Some (Vint (Int.repr x)) -> le ! bound = Some (Vint (Int.repr upper)) ->
  signed_range upper -> signed_range (x + Z.of_nat width) ->
  exec_stmt fe ge locals le memory (stripmine_prepare iterator bound limit width) E0
    (PTree.set limit (Vint (Int.repr (Z.min upper (x + Z.of_nat width)))) le) memory Out_normal.
Proof.
  intros IL NL ITER BOUND UR SUMR; unfold stripmine_prepare.
  set (sum := x + Z.of_nat width).
  set (middle := PTree.set limit (Vint (Int.repr sum)) le).
  assert (BN : middle ! bound = Some (Vint (Int.repr upper))) by (unfold middle; rewrite PTree.gso by congruence; exact BOUND).
  assert (LN : middle ! limit = Some (Vint (Int.repr sum))) by apply PTree.gss.
  pose proof (@counter_condition_at ge locals middle memory bound limit upper sum NL BN LN UR SUMR) as TEST.
  destruct TEST as [value [EVAL BOOL]].
  destruct (upper <? sum) eqn:CLAMP.
  - apply Z.ltb_lt in CLAMP; rewrite Z.min_l by lia.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := middle) (m1 := memory).
    + constructor; apply stripmine_add_evaluation; exact ITER.
    + replace (PTree.set limit (Vint (Int.repr upper)) le) with (PTree.set limit (Vint (Int.repr upper)) middle)
        by (unfold middle; apply PTree.set2).
      eapply exec_Sifthenelse with (b := true); [exact EVAL|exact BOOL|constructor; constructor; exact BN].
  - apply Z.ltb_ge in CLAMP; rewrite Z.min_r by lia.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := middle) (m1 := memory).
    + constructor; apply stripmine_add_evaluation; exact ITER.
    + eapply exec_Sifthenelse with (b := false); [exact EVAL|exact BOOL|constructor].
Qed.

Section POINTS.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable live : list ident.
Variable iterator : ident.
Variable body : statement.
Variable base : temp_env.
Hypothesis WRITES : writes_only [] body.
Hypothesis SCOPE : statement_scope live body.
Definition canonical_body x memory memory' :=
  exec_stmt fe ge locals (PTree.set iterator (Vint (Int.repr x)) base) memory body E0
    (PTree.set iterator (Vint (Int.repr x)) base) memory' Out_normal.

Lemma canonical_body_decode x le memory after memory' :
  le ! iterator = Some (Vint (Int.repr x)) -> temp_agree (temp_except live iterator) base le ->
  exec_stmt fe ge locals le memory body E0 after memory' Out_normal ->
  canonical_body x memory memory' /\ after = le.
Proof.
  intros ITER FRAME RUN.
  assert (EXACT : after = le) by (eapply memory_body_temporaries_exact; eauto); subst after.
  pose proof (@canonical_temp_agreement live iterator base le (Vint (Int.repr x)) ITER FRAME) as AGREE.
  destruct (@structured_execution_temp_transport fe ge locals le memory body E0 le memory' Out_normal RUN
    live (PTree.set iterator (Vint (Int.repr x)) base) [] WRITES SCOPE (temp_agree_sym AGREE)) as [target [EXEC EQ]].
  assert (SAME : target = PTree.set iterator (Vint (Int.repr x)) base) by (eapply memory_body_temporaries_exact; eauto); subst target.
  split; [exact EXEC|reflexivity].
Qed.
Lemma canonical_body_encode x le memory memory' :
  le ! iterator = Some (Vint (Int.repr x)) -> temp_agree (temp_except live iterator) base le ->
  canonical_body x memory memory' -> exec_stmt fe ge locals le memory body E0 le memory' Out_normal.
Proof.
  intros ITER FRAME RUN.
  pose proof (@canonical_temp_agreement live iterator base le (Vint (Int.repr x)) ITER FRAME) as AGREE.
  destruct (@structured_execution_temp_transport fe ge locals _ memory body E0 _ memory' Out_normal RUN
    live le [] WRITES SCOPE AGREE) as [target [EXEC EQ]].
  assert (SAME : target = le) by (eapply memory_body_temporaries_exact; eauto); subst target; exact EXEC.
Qed.
End POINTS.
Print Assumptions canonical_body_decode.
Print Assumptions stripmine_prepare_execution.

Section CHUNK_ENCODING.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable live : list ident.
Variable iterator bound limit : ident.
Variable width : nat.
Variable body : statement.
Variable base : temp_env.
Variable upper : Z.
Hypothesis DISTINCT : iterator <> bound.
Hypothesis IL : iterator <> limit.
Hypothesis BL : bound <> limit.
Hypothesis PRIVATE : ~ In limit live.
Hypothesis POSITIVE : (0 < width)%nat.
Hypothesis UPPER : 0 <= upper <= Int.max_signed - Z.of_nat width.
Hypothesis WRITES : writes_only [] body.
Hypothesis NORMAL : normal_statement body = true.
Hypothesis SCOPE : statement_scope live body.
Let stable := temp_except live iterator.
Let point := canonical_body fe ge locals iterator body base.

Theorem stripmine_chunked_encode count x before after :
  chunked_iterations point width count x before after ->
  forall le, upper = x + Z.of_nat count -> 0 <= x ->
  le ! iterator = Some (Vint (Int.repr x)) -> le ! bound = Some (Vint (Int.repr upper)) ->
  temp_agree stable base le -> exists final,
    exec_stmt fe ge locals le before (stripmine_loop iterator bound limit width body) E0 final after Out_normal /\
    final ! iterator = Some (Vint (Int.repr upper)) /\ temp_agree stable base final.
Proof.
  intros RUN; induction RUN; intros le LENGTH FLOOR ITER BOUND FRAME.
  - cbn in LENGTH; assert (SAME : upper = x) by lia; subst x.
    exists le; repeat split; auto.
    assert (RANGE : signed_range upper) by (unfold signed_range; change Int.min_signed with (-2147483648); lia).
    pose proof (@counter_condition_at ge locals le state iterator bound upper upper DISTINCT ITER BOUND RANGE RANGE) as TEST.
    rewrite Z.ltb_irrefl in TEST; destruct TEST as [value [EVAL BOOL]].
    unfold stripmine_loop; eapply exec_Sloop_stop1 with (out' := Out_break).
    + eapply exec_Sseq_2; [eapply exec_Sifthenelse with (b := false); [exact EVAL|exact BOOL|constructor]|discriminate].
    + constructor.
  - set (chunk := Nat.min width remaining).
    set (finish := x + Z.of_nat chunk).
    assert (SIZE : (0 < chunk <= remaining)%nat) by (unfold chunk; lia).
    assert (END : x < finish <= upper) by (unfold finish; lia).
    assert (MINIMUM : Z.min upper (x + Z.of_nat width) = finish).
    { unfold finish, chunk; destruct (le_dec width remaining).
      - rewrite Nat.min_l by lia; rewrite Z.min_r; lia.
      - rewrite Nat.min_r by lia; rewrite Z.min_l; lia. }
    assert (UR : signed_range upper) by (unfold signed_range; change Int.min_signed with (-2147483648); lia).
    assert (XR : signed_range x) by (unfold signed_range; change Int.min_signed with (-2147483648); lia).
    assert (FR : signed_range finish) by (unfold signed_range; change Int.min_signed with (-2147483648); lia).
    assert (SUMR : signed_range (x + Z.of_nat width)) by (unfold signed_range; change Int.min_signed with (-2147483648); lia).
    set (prepared := PTree.set limit (Vint (Int.repr finish)) le).
    assert (PREPARE : exec_stmt fe ge locals le before (stripmine_prepare iterator bound limit width) E0 prepared before Out_normal).
    { unfold prepared; rewrite <- MINIMUM; apply stripmine_prepare_execution; assumption. }
    assert (PI : prepared ! iterator = Some (Vint (Int.repr x))) by (unfold prepared; rewrite PTree.gso by congruence; exact ITER).
    assert (PB : prepared ! bound = Some (Vint (Int.repr upper))) by (unfold prepared; rewrite PTree.gso by congruence; exact BOUND).
    assert (PL : prepared ! limit = Some (Vint (Int.repr finish))) by apply PTree.gss.
    assert (PF : temp_agree stable base prepared).
    { eapply temp_agree_trans; [exact FRAME|apply temp_agree_set; apply temp_except_private; exact PRIVATE]. }
    assert (ENCODE : forall y temps memory memory', 0 <= y < finish ->
      temps ! iterator = Some (Vint (Int.repr y)) -> temps ! limit = Some (Vint (Int.repr finish)) ->
      temp_agree stable base temps -> point y memory memory' ->
      exec_stmt fe ge locals temps memory body E0 temps memory' Out_normal).
    { intros y temps memory memory' Y I L F POINT_RUN;
      exact (@canonical_body_encode fe ge locals live iterator body base WRITES SCOPE y temps memory memory' I F POINT_RUN). }
    pose proof (@frontend_parametric_encode fe ge locals iterator limit body None point 0 finish stable base
      IL ltac:(split; intro BAD; inversion BAD) (temp_except_iterator live iterator)
      ltac:(intros id MEMBER BAD; inversion BAD) FR ENCODE
      chunk x before middle H0 prepared ltac:(unfold finish; lia) XR FLOOR PI PL PF) as INNER.
    set (next := PTree.set iterator (Vint (Int.repr finish)) prepared).
    assert (INNER' : exec_stmt fe ge locals prepared before (frontend_counted_loop iterator limit body) E0 next middle Out_normal).
    { unfold next; replace (PTree.set iterator (Vint (Int.repr finish)) prepared)
        with (loop_exit None iterator prepared chunk finish) by (destruct chunk; reflexivity); exact INNER. }
    assert (NI : next ! iterator = Some (Vint (Int.repr finish))) by apply PTree.gss.
    assert (NB : next ! bound = Some (Vint (Int.repr upper))) by (unfold next; rewrite PTree.gso by congruence; exact PB).
    assert (NF : temp_agree stable base next).
    { eapply temp_agree_trans; [exact PF|apply temp_agree_set; apply temp_except_iterator]. }
    destruct (IHRUN next) as [final [TAIL [FI FF]]].
    + unfold finish, chunk; rewrite Nat2Z.inj_sub by apply Nat.le_min_r; lia.
    + lia.
    + exact NI.
    + exact NB.
    + exact NF.
    + exists final; split; [|auto].
      pose proof (@counter_condition_at ge locals le before iterator bound x upper DISTINCT ITER BOUND XR UR) as TEST.
      assert (YES : (x <? upper) = true) by (apply Z.ltb_lt; lia); rewrite YES in TEST.
      destruct TEST as [value [EVAL BOOL]].
      unfold stripmine_loop at 1; eapply exec_Sloop_loop with (out1 := Out_normal) (t1 := E0) (t2 := E0) (t3 := E0).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- eapply exec_Sifthenelse with (b := true); [exact EVAL|exact BOOL|constructor].
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact PREPARE|exact INNER'].
      * constructor.
      * constructor.
      * exact TAIL.
Qed.
End CHUNK_ENCODING.
Print Assumptions stripmine_chunked_encode.
